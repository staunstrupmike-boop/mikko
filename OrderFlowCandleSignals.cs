// =====================================================================================
//  OrderFlowCandleSignals.cs  —  NinjaTrader 8 indicator   (v3.1: adaptive + statistics)
//
//  Order Flow Candle playbook (Bid x Ask) on a NORMAL candle chart:
//    • REVERSAL   : setup at a new session extreme (EXH exhaustion / ABS absorption /
//                   DIV cumulative-delta divergence) -> confirmation candle
//    • TRAPS      : break of swing high/low or OR with no follow-through -> close back inside
//                   with opposite delta  (BULL TRAP, BEAR TRAP, ORB FAIL)
//    • ORB        : valid opening range breakout + retest
//
//  v3 changes
//    • Adaptive statistics instead of fixed contract numbers:
//        - Relative volume vs. the SAME time of day (30-min buckets, learned from history)
//        - Delta strength as a z-score of delta% (delta / volume) over the last N bars
//    • Session-aware: divergence and extremes never compare across sessions
//    • Risk filter: min stop distance, max stop distance in average ranges (no huge stops)
//    • Time filter (default 09:30–16:00 ET = 15:30–22:00 CET) + virtual flatten at end
//    • Performance statistics per setup type and per score: N, win%, T1%, avg R, PF, MFE/MAE
//      (slippage + optional 50% scale-out at T1), optional CSV trade log for analysis
//    • Panels only redraw on the last historical bar and in realtime (faster loading)
//
//  v3.1 fixes
//    • L2 point no longer counts toward the minimum score (live-only data skewed the stats)
//    • Reversal setups never confirm across a session boundary
//    • Open virtual trade is flattened at the previous close on the first bar of a session
//    • Stop / T2 fills honour gaps through the level; MAE no longer overstated on stop bars
//    • Reversed trades get an exit marker
//
//  Data: footprint from a hidden Volumetric series (Order Flow+). Level 2 is live-only
//  confirmation (NT stores no depth history; Market Replay includes it for Playback tests).
//
//  Discipline: OnBarClose (no repaint), one signal per bar, per-side cooldown, daily cap,
//  min score per family. Exits are WARNINGS only — nothing is ever sent to the broker.
//
//  Public series
//    Signal     : +/-1 Reversal, +/-2 Trap, +/-3 ORB break, +/-4 ORB retest
//    ExitSignal : sign = position side; 1 warning, 2 T1, 3 T2, 4 stop, 5 reversed, 6 end of day
// =====================================================================================

#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Globalization;
using System.Text;
using System.Windows;
using System.Windows.Media;
using System.Xml.Serialization;
using NinjaTrader.Cbi;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Chart;
using NinjaTrader.Gui.Tools;
using NinjaTrader.Data;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.DrawingTools;
using NinjaTrader.NinjaScript.BarsTypes;
#endregion

namespace NinjaTrader.NinjaScript.Indicators
{
    public class OrderFlowCandleSignals : Indicator
    {
        #region Private types
        private class BookLevel { public double Price; public long Volume; }

        private class Candidate
        {
            public int Dir, Prio, Code, Score, Max;
            public string Name;
            public double Stop;
            public bool L2Ok;
        }

        private class SetupStat
        {
            public int N, Wins, T1;
            public double SumR, GrossWin, GrossLoss, SumMfe, SumMae;

            public void Add(double r, bool t1, double mfe, double mae)
            {
                N++;
                if (r > 0) { Wins++; GrossWin += r; } else GrossLoss += -r;
                if (t1) T1++;
                SumR += r; SumMfe += mfe; SumMae += mae;
            }
            public double WinPct { get { return N == 0 ? 0 : (double)Wins / N; } }
            public double T1Pct  { get { return N == 0 ? 0 : (double)T1 / N; } }
            public double AvgR   { get { return N == 0 ? 0 : SumR / N; } }
            public double PF     { get { return GrossLoss > 0 ? GrossWin / GrossLoss : (GrossWin > 0 ? 99 : 0); } }
        }
        #endregion

        #region Fields
        private VolumetricBarsType vbt;
        private MasterInstrument   mi;
        private Series<double> cumDelta, deltaPctS, signal, exitSeries;
        private Series<int>    bullSetup, bearSetup;      // bitmask: 1 EXH, 2 ABS, 4 DIV

        // Level 2
        private readonly List<BookLevel> bids = new List<BookLevel>();
        private readonly List<BookLevel> asks = new List<BookLevel>();
        private readonly object bookLock = new object();

        // Time-of-day volume profile (48 x 30 min, ET)
        private readonly double[] todAvg = new double[48];
        private readonly int[]    todN   = new int[48];
        private const int TodMinSamples  = 10;

        private TimeZoneInfo estTz;
        private SimpleFont labelFont, smallFont, panelFont;
        private int sessionStartBar;

        // Opening range
        private DateTime orDate = DateTime.MinValue, orStartChart, orEndChart;
        private double   orHigh, orLow;
        private bool     orBuilding, orComplete, orUpValid, orDnValid, orUpDone, orDnDone, orUpRetested, orDnRetested;
        private int      orUpBar = -1, orDnBar = -1, orUpFirstAbove = -1, orDnFirstBelow = -1;

        // Traps
        private int    bullTrapBar = -1, bearTrapBar = -1;
        private double bullTrapLevel, bullTrapBreakHigh, bullTrapExtreme;
        private double bearTrapLevel, bearTrapBreakLow, bearTrapExtreme;
        private bool   bullTrapIsOR, bullTrapAggressive, bearTrapIsOR, bearTrapAggressive;

        // Virtual position
        private int      posDir, posCode, posBar = -1, posId, posScore, posMax, lastWarnBar = -100000;
        private double   posEntry, posEntryEff, posStop, posInitStop, posRisk, posT1, posT2, posLevel, posT1R, posMfe, posMae;
        private bool     t1Hit, posL2;
        private string   posName = "";
        private DateTime posTime;
        private double   posRelVol, posDeltaZ;
        private int      posAskStack, posBidStack;
        private string   lastWarnText = "-";

        private int      lastLongBar = -100000, lastShortBar = -100000, signalsToday;
        private DateTime sessionDate = DateTime.MinValue;
        private string   lastSignalText = "-";

        // Statistics
        private readonly Dictionary<string, SetupStat> statByType  = new Dictionary<string, SetupStat>();
        private readonly SortedDictionary<string, SetupStat> statByScore = new SortedDictionary<string, SetupStat>();
        private readonly SetupStat statLong = new SetupStat(), statShort = new SetupStat(), statAll = new SetupStat();
        private static readonly string[] TypeOrder = { "REVERSAL", "BULL TRAP", "BEAR TRAP", "ORB FAIL", "ORB BREAK", "ORB RETEST" };
        private string csvPath;
        #endregion

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description              = "Order flow candle signals (Reversal, Traps, ORB) from footprint + Level 2 with adaptive thresholds, exit warnings and performance statistics.";
                Name                     = "OrderFlowCandleSignals";
                Calculate                = Calculate.OnBarClose;
                IsOverlay                = true;
                DisplayInDataBox         = false;
                DrawOnPricePanel         = true;
                PaintPriceMarkers        = false;
                IsSuspendedWhileInactive = false;
                ScaleJustification       = ScaleJustification.Right;

                // 1. Footprint & statistics base
                ImbalanceRatio     = 3.0;
                ImbalanceMinVolume = 5;
                StackedMin         = 3;
                AvgPeriod          = 50;
                StrongDeltaZ       = 1.0;

                // 2. Reversal
                SwingLookback      = 10;
                ExhaustionRatio    = 0.35;
                AbsRelVol          = 1.8;
                AbsRangeMult       = 0.8;
                AbsDeltaZ          = 1.0;
                SetupWindow        = 3;
                MinReversalScore   = 4;

                // 3. Traps
                LevelLookback      = 20;
                BreakTicks         = 1;
                TrapBars           = 3;
                FollowTicks        = 2;
                MinTrapScore       = 3;

                // 4. ORB
                UseORB             = true;
                ORStartHour        = 9;
                ORStartMinute      = 30;
                ORMinutes          = 15;
                ORTradeWindow      = 120;
                ORRelVol           = 1.2;
                RetestTicks        = 2;
                InvalidTicks       = 4;
                MinORScore         = 3;

                // 5. Level 2
                UseL2               = true;
                L2Levels            = 10;
                L2MinImbalance      = 0.20;
                WallMultiple        = 3.0;
                WallTicks           = 3;
                RequireL2InRealtime = false;

                // 6. Signals, risk & time
                CooldownBars       = 3;
                MaxSignalsPerDay   = 8;
                StopBufferTicks    = 2;
                MinRiskTicks       = 4;
                MaxRiskRanges      = 2.5;
                UseTimeFilter      = true;
                EntryStartET       = 930;
                EntryEndET         = 1600;
                ArrowOffsetTicks   = 4;
                ShowSetupMarkers   = true;
                ShowLabels         = true;
                ShowPanel          = true;
                ShowOR             = true;
                EnableAlerts       = true;
                LongBrush          = Brushes.LimeGreen;
                ShortBrush         = Brushes.Red;

                // 7. Exits (warnings only)
                ShowExitWarnings   = true;
                MinWarnReasons     = 1;
                WarnCooldownBars   = 2;
                MoveStopToBE       = true;
                TrailAfterT1       = false;
                ShowTradeLines     = true;
                EnableExitAlerts   = true;
                WarnBrush          = Brushes.Orange;

                // 8. Statistics
                ShowStats          = true;
                SlippageTicks      = 1;
                ScaleOutAtT1       = true;
                LogTradesCsv       = false;
            }
            else if (State == State.Configure)
            {
                BarsPeriodType bpt = BarsPeriod.BarsPeriodType;
                int            bpv = BarsPeriod.Value;
                if (bpt == BarsPeriodType.Volumetric)
                {
                    bpt = BarsPeriod.BaseBarsPeriodType;
                    bpv = BarsPeriod.BaseBarsPeriodValue;
                }
                AddVolumetric(null, bpt, bpv, VolumetricDeltaType.BidAsk, 1);
            }
            else if (State == State.DataLoaded)
            {
                vbt        = BarsArray[1].BarsType as VolumetricBarsType;
                mi         = Instrument.MasterInstrument;
                cumDelta   = new Series<double>(BarsArray[1]);
                deltaPctS  = new Series<double>(BarsArray[1]);
                signal     = new Series<double>(BarsArray[1]);
                exitSeries = new Series<double>(BarsArray[1]);
                bullSetup  = new Series<int>(BarsArray[1]);
                bearSetup  = new Series<int>(BarsArray[1]);

                try   { estTz = TimeZoneInfo.FindSystemTimeZoneById("Eastern Standard Time"); }
                catch { estTz = TimeZoneInfo.Local; }

                labelFont = new SimpleFont("Arial", 11) { Bold = true };
                smallFont = new SimpleFont("Arial", 8);
                panelFont = new SimpleFont("Consolas", 11);

                foreach (string k in TypeOrder) statByType[k] = new SetupStat();

                if (LogTradesCsv)
                {
                    csvPath = System.IO.Path.Combine(NinjaTrader.Core.Globals.UserDataDir,
                              "OFS_trades_" + mi.Name + "_" + DateTime.Now.ToString("yyyyMMdd_HHmmss") + ".csv");
                    try
                    {
                        System.IO.File.WriteAllText(csvPath,
                            "entry_time,exit_time,type,dir,score,max,entry,stop,t1,t2,exit,reason,R,mfeR,maeR,t1_hit,relvol,deltaZ,ask_stack,bid_stack,l2,realtime\r\n");
                    }
                    catch { csvPath = null; }
                }
            }
        }

        // =================================================================================
        //  LEVEL 2
        // =================================================================================
        protected override void OnMarketDepth(MarketDepthEventArgs e)
        {
            if (!UseL2) return;
            lock (bookLock)
            {
                if (e.IsReset) { bids.Clear(); asks.Clear(); return; }

                List<BookLevel> side = null;
                if (e.MarketDataType == MarketDataType.Bid) side = bids;
                else if (e.MarketDataType == MarketDataType.Ask) side = asks;
                if (side == null) return;

                if (e.Operation == Operation.Add)
                {
                    if (e.Position <= side.Count) side.Insert(e.Position, new BookLevel { Price = e.Price, Volume = e.Volume });
                }
                else if (e.Operation == Operation.Update)
                {
                    if (e.Position < side.Count) { side[e.Position].Price = e.Price; side[e.Position].Volume = e.Volume; }
                }
                else if (e.Operation == Operation.Remove)
                {
                    if (e.Position < side.Count) side.RemoveAt(e.Position);
                }
            }
        }

        private bool BookReady() { lock (bookLock) { return bids.Count >= 3 && asks.Count >= 3; } }

        private double BookImbalance(int levels)
        {
            lock (bookLock)
            {
                double b = 0, a = 0;
                for (int i = 0; i < Math.Min(levels, bids.Count); i++) b += bids[i].Volume;
                for (int i = 0; i < Math.Min(levels, asks.Count); i++) a += asks[i].Volume;
                return (a + b) <= 0 ? 0 : (b - a) / (b + a);
            }
        }

        private bool HasWall(bool bidSide, double nearPrice, int ticks)
        {
            lock (bookLock)
            {
                List<BookLevel> side = bidSide ? bids : asks;
                int n = Math.Min(L2Levels, side.Count);
                if (n < 3) return false;
                double sum = 0;
                for (int i = 0; i < n; i++) sum += side[i].Volume;
                double avg = sum / n;
                for (int i = 0; i < n; i++)
                    if (side[i].Volume >= avg * WallMultiple && Math.Abs(side[i].Price - nearPrice) <= (ticks + 0.01) * TickSize)
                        return true;
                return false;
            }
        }

        // =================================================================================
        //  MAIN
        // =================================================================================
        protected override void OnBarUpdate()
        {
            if (BarsInProgress != 1 || vbt == null) return;

            int cb = CurrentBars[1];
            VolumetricData vd = vbt.Volumes[cb];
            if (BarsArray[1].IsFirstBarOfSession) sessionStartBar = cb;

            double vol   = vd.TotalVolume;
            double delta = vd.BarDelta;
            cumDelta[0]   = vd.CumulativeDelta;
            deltaPctS[0]  = vol > 0 ? delta / vol : 0;
            bullSetup[0]  = 0;
            bearSetup[0]  = 0;
            signal[0]     = 0;
            exitSeries[0] = 0;

            DateTime t      = Times[1][0];
            DateTime et     = ToEt(t);
            int      hhmm   = et.Hour * 100 + et.Minute;
            int      bucket = Math.Min(47, (et.Hour * 60 + et.Minute) / 30);

            int need = Math.Max(Math.Max(AvgPeriod, SwingLookback), Math.Max(LevelLookback, SetupWindow)) + 2;
            if (cb < need || CurrentBars[0] < 1) { UpdateTod(bucket, vol); return; }

            if (et.Date != sessionDate) { sessionDate = et.Date; signalsToday = 0; }

            // ---------------- bar metrics & adaptive statistics ----------------
            double o = Opens[1][0], h = Highs[1][0], l = Lows[1][0], c = Closes[1][0];
            double range    = Math.Max(h - l, TickSize);
            double closePos = (c - l) / range;
            double deltaPct = deltaPctS[0];

            double poc;
            vd.GetMaximumVolume(null, out poc);

            double sumV = 0, sumR = 0, sumD = 0, sumD2 = 0;
            for (int i = 1; i <= AvgPeriod; i++)
            {
                sumV  += Volumes[1][i];
                sumR  += Highs[1][i] - Lows[1][i];
                double d = deltaPctS[i];
                sumD  += d;
                sumD2 += d * d;
            }
            double avgVol   = Math.Max(sumV / AvgPeriod, 1);
            double avgRange = Math.Max(sumR / AvgPeriod, TickSize);
            double dMean    = sumD / AvgPeriod;
            double dStd     = Math.Sqrt(Math.Max(sumD2 / AvgPeriod - dMean * dMean, 0));
            double deltaZ   = (deltaPct - dMean) / Math.Max(dStd, 0.02);

            double relVol = TodRelVol(bucket, vol, avgVol);   // volume vs. same time of day
            UpdateTod(bucket, vol);

            int    levels      = (int)Math.Round((h - l) / TickSize) + 1;
            double avgLevelVol = vol / Math.Max(levels, 1);

            int askStack, bidStack;
            ScanImbalances(vd, l, h, out askStack, out bidStack);

            // Session-scoped extremes (divergence never compares across sessions)
            int    lb = Math.Min(SwingLookback, cb - sessionStartBar);
            bool   sessionReady = lb >= 3;
            double prevLow = double.MaxValue, prevHigh = double.MinValue, cdAtPrevLow = 0, cdAtPrevHigh = 0;
            for (int i = 1; i <= Math.Max(lb, 1); i++)
            {
                if (Lows[1][i]  < prevLow)  { prevLow  = Lows[1][i];  cdAtPrevLow  = cumDelta[i]; }
                if (Highs[1][i] > prevHigh) { prevHigh = Highs[1][i]; cdAtPrevHigh = cumDelta[i]; }
            }

            bool   l2Live = UseL2 && State == State.Realtime && BookReady();
            double imb    = l2Live ? BookImbalance(L2Levels) : 0;
            bool   strongUp = deltaZ >=  StrongDeltaZ && delta > 0;
            bool   strongDn = deltaZ <= -StrongDeltaZ && delta < 0;

            // ---------------- 1) setups at session extremes ----------------
            if (sessionReady)
            {
                bool atLow  = l <= prevLow  + TickSize;
                bool atHigh = h >= prevHigh - TickSize;

                double lowEdgeVol  = EdgeVolume(vd, l, true);    // bottom 2 prices
                double highEdgeVol = EdgeVolume(vd, h, false);   // top 2 prices

                bool exhBull = atLow  && (lowEdgeVol  <= 2 * avgLevelVol * ExhaustionRatio || vd.GetBidVolumeForPrice(l) == 0) && deltaPct > deltaPctS[1];
                bool exhBear = atHigh && (highEdgeVol <= 2 * avgLevelVol * ExhaustionRatio || vd.GetAskVolumeForPrice(h) == 0) && deltaPct < deltaPctS[1];

                bool absBull = atLow  && relVol >= AbsRelVol && deltaZ <= -AbsDeltaZ && (range <= avgRange * AbsRangeMult || closePos >= 0.5);
                bool absBear = atHigh && relVol >= AbsRelVol && deltaZ >=  AbsDeltaZ && (range <= avgRange * AbsRangeMult || closePos <= 0.5);

                bool divBull = l < prevLow  && cumDelta[0] > cdAtPrevLow;
                bool divBear = h > prevHigh && cumDelta[0] < cdAtPrevHigh;

                bullSetup[0] = (exhBull ? 1 : 0) | (absBull ? 2 : 0) | (divBull ? 4 : 0);
                bearSetup[0] = (exhBear ? 1 : 0) | (absBear ? 2 : 0) | (divBear ? 4 : 0);

                if (ShowSetupMarkers)
                {
                    if (bullSetup[0] != 0)
                        Draw.Text(this, "OFS_SUL_" + cb, false, MaskText(bullSetup[0]), t, l - TickSize, -12, Brushes.Gray, smallFont, TextAlignment.Center, Brushes.Transparent, Brushes.Transparent, 0);
                    if (bearSetup[0] != 0)
                        Draw.Text(this, "OFS_SUH_" + cb, false, MaskText(bearSetup[0]), t, h + TickSize, 12, Brushes.Gray, smallFont, TextAlignment.Center, Brushes.Transparent, Brushes.Transparent, 0);
                }
            }

            List<Candidate> cands = new List<Candidate>(4);
            double buf = StopBufferTicks * TickSize;

            // ---------------- 2) reversal confirmation ----------------
            {
                int mask = 0, newest = -1;
                double sLow = double.MaxValue, sHigh = 0;
                for (int i = 1; i <= SetupWindow && cb - i >= sessionStartBar; i++)
                {
                    int m = bullSetup[i];
                    if (m == 0) continue;
                    mask |= m;
                    sLow = Math.Min(sLow, Lows[1][i]);
                    if (newest < 0) { newest = cb - i; sHigh = Highs[1][i]; }
                }
                if (mask != 0 && newest > lastLongBar && c > o && delta > 0 && deltaZ > 0
                    && (askStack >= StackedMin || c > sHigh) && l >= sLow - TickSize)
                {
                    bool l2ok  = l2Live && (imb >= L2MinImbalance || HasWall(true, sLow, WallTicks));
                    int  score = PopCount(mask) + (askStack >= StackedMin ? 1 : 0) + (poc >= l + 0.5 * range ? 1 : 0)
                               + (strongUp ? 1 : 0);
                    if (score >= MinReversalScore)
                        cands.Add(new Candidate { Dir = 1, Prio = 1, Code = 1, Name = "REVERSAL", Score = score + L2Bonus(l2ok), Max = 7, Stop = sLow - buf, L2Ok = l2ok });
                }
            }
            {
                int mask = 0, newest = -1;
                double sHigh = double.MinValue, sLow = 0;
                for (int i = 1; i <= SetupWindow && cb - i >= sessionStartBar; i++)
                {
                    int m = bearSetup[i];
                    if (m == 0) continue;
                    mask |= m;
                    sHigh = Math.Max(sHigh, Highs[1][i]);
                    if (newest < 0) { newest = cb - i; sLow = Lows[1][i]; }
                }
                if (mask != 0 && newest > lastShortBar && c < o && delta < 0 && deltaZ < 0
                    && (bidStack >= StackedMin || c < sLow) && h <= sHigh + TickSize)
                {
                    bool l2ok  = l2Live && (imb <= -L2MinImbalance || HasWall(false, sHigh, WallTicks));
                    int  score = PopCount(mask) + (bidStack >= StackedMin ? 1 : 0) + (poc <= l + 0.5 * range ? 1 : 0)
                               + (strongDn ? 1 : 0);
                    if (score >= MinReversalScore)
                        cands.Add(new Candidate { Dir = -1, Prio = 1, Code = 1, Name = "REVERSAL", Score = score + L2Bonus(l2ok), Max = 7, Stop = sHigh + buf, L2Ok = l2ok });
                }
            }

            // ---------------- 3) opening range ----------------
            if (UseORB) UpdateOR(et, t, h, l);
            bool orLive = UseORB && orComplete && et.Date == orDate && InORWindow(et);

            // ---------------- 4) traps ----------------
            double swingHi = double.MinValue, swingLo = double.MaxValue;
            for (int i = 1; i <= LevelLookback; i++)
            {
                swingHi = Math.Max(swingHi, Highs[1][i]);
                swingLo = Math.Min(swingLo, Lows[1][i]);
            }
            double brk = BreakTicks * TickSize;

            if (bullTrapBar >= 0 && cb - bullTrapBar > TrapBars) bullTrapBar = -1;
            if (bullTrapBar >= 0 && cb > bullTrapBar)
            {
                bullTrapExtreme = Math.Max(bullTrapExtreme, h);
                if (c > bullTrapBreakHigh + FollowTicks * TickSize) bullTrapBar = -1;            // accepted -> real breakout
                else if (c < bullTrapLevel && delta < 0) { AddBullTrap(cands, l2Live, imb, strongDn, bidStack); bullTrapBar = -1; }
            }
            if (bullTrapBar < 0)
            {
                double lvl = double.NaN; bool isOR = false;
                if (orLive && h > orHigh + brk && Closes[1][1] <= orHigh) { lvl = orHigh; isOR = true; }
                else if (h > swingHi + brk && Closes[1][1] <= swingHi)     { lvl = swingHi; }
                if (!double.IsNaN(lvl))
                {
                    bullTrapBar = cb; bullTrapLevel = lvl; bullTrapBreakHigh = h; bullTrapExtreme = h; bullTrapIsOR = isOR;
                    bullTrapAggressive = askStack >= 1 || deltaZ > 0;
                    if (c < lvl && delta < 0) { AddBullTrap(cands, l2Live, imb, strongDn, bidStack); bullTrapBar = -1; }
                }
            }

            if (bearTrapBar >= 0 && cb - bearTrapBar > TrapBars) bearTrapBar = -1;
            if (bearTrapBar >= 0 && cb > bearTrapBar)
            {
                bearTrapExtreme = Math.Min(bearTrapExtreme, l);
                if (c < bearTrapBreakLow - FollowTicks * TickSize) bearTrapBar = -1;
                else if (c > bearTrapLevel && delta > 0) { AddBearTrap(cands, l2Live, imb, strongUp, askStack); bearTrapBar = -1; }
            }
            if (bearTrapBar < 0)
            {
                double lvl = double.NaN; bool isOR = false;
                if (orLive && l < orLow - brk && Closes[1][1] >= orLow) { lvl = orLow; isOR = true; }
                else if (l < swingLo - brk && Closes[1][1] >= swingLo)  { lvl = swingLo; }
                if (!double.IsNaN(lvl))
                {
                    bearTrapBar = cb; bearTrapLevel = lvl; bearTrapBreakLow = l; bearTrapExtreme = l; bearTrapIsOR = isOR;
                    bearTrapAggressive = bidStack >= 1 || deltaZ < 0;
                    if (c > lvl && delta > 0) { AddBearTrap(cands, l2Live, imb, strongUp, askStack); bearTrapBar = -1; }
                }
            }

            // ---------------- 5) ORB break + retest ----------------
            if (orLive)
            {
                // long
                if (c > orHigh) { if (orUpFirstAbove < 0) orUpFirstAbove = cb; } else orUpFirstAbove = -1;
                if (!orUpDone && orUpFirstAbove >= 0 && cb - orUpFirstAbove <= 2)
                {
                    bool stack = askStack >= StackedMin;
                    if ((stack || strongUp) && relVol >= ORRelVol)
                    {
                        bool l2ok  = l2Live && imb >= L2MinImbalance;
                        int  score = 1 + (stack ? 1 : 0) + (strongUp ? 1 : 0) + (closePos >= 0.7 ? 1 : 0);
                        if (score >= MinORScore)
                        {
                            cands.Add(new Candidate { Dir = 1, Prio = 2, Code = 3, Name = "ORB BREAK", Score = score + L2Bonus(l2ok), Max = 5, Stop = Math.Min(l, orHigh) - buf, L2Ok = l2ok });
                            orUpDone = true; orUpValid = true; orUpBar = cb;
                        }
                    }
                }
                if (orUpValid && c < orHigh - InvalidTicks * TickSize) orUpValid = false;
                if (orUpValid && !orUpRetested && cb > orUpBar + 1 && l <= orHigh + RetestTicks * TickSize && c > orHigh && delta > 0)
                {
                    bool l2ok  = l2Live && (imb >= L2MinImbalance || HasWall(true, orHigh, WallTicks));
                    int  score = 2 + (askStack >= 1 ? 1 : 0) + (deltaZ > 0 ? 1 : 0);
                    if (score >= MinORScore)
                        cands.Add(new Candidate { Dir = 1, Prio = 2, Code = 4, Name = "ORB RETEST", Score = score + L2Bonus(l2ok), Max = 5, Stop = Math.Min(l, orHigh) - buf, L2Ok = l2ok });
                    orUpRetested = true;
                }

                // short
                if (c < orLow) { if (orDnFirstBelow < 0) orDnFirstBelow = cb; } else orDnFirstBelow = -1;
                if (!orDnDone && orDnFirstBelow >= 0 && cb - orDnFirstBelow <= 2)
                {
                    bool stack = bidStack >= StackedMin;
                    if ((stack || strongDn) && relVol >= ORRelVol)
                    {
                        bool l2ok  = l2Live && imb <= -L2MinImbalance;
                        int  score = 1 + (stack ? 1 : 0) + (strongDn ? 1 : 0) + (closePos <= 0.3 ? 1 : 0);
                        if (score >= MinORScore)
                        {
                            cands.Add(new Candidate { Dir = -1, Prio = 2, Code = 3, Name = "ORB BREAK", Score = score + L2Bonus(l2ok), Max = 5, Stop = Math.Max(h, orLow) + buf, L2Ok = l2ok });
                            orDnDone = true; orDnValid = true; orDnBar = cb;
                        }
                    }
                }
                if (orDnValid && c > orLow + InvalidTicks * TickSize) orDnValid = false;
                if (orDnValid && !orDnRetested && cb > orDnBar + 1 && h >= orLow - RetestTicks * TickSize && c < orLow && delta < 0)
                {
                    bool l2ok  = l2Live && (imb <= -L2MinImbalance || HasWall(false, orLow, WallTicks));
                    int  score = 2 + (bidStack >= 1 ? 1 : 0) + (deltaZ < 0 ? 1 : 0);
                    if (score >= MinORScore)
                        cands.Add(new Candidate { Dir = -1, Prio = 2, Code = 4, Name = "ORB RETEST", Score = score + L2Bonus(l2ok), Max = 5, Stop = Math.Max(h, orLow) + buf, L2Ok = l2ok });
                    orDnRetested = true;
                }
            }

            // ---------------- 6) manage open virtual position ----------------
            ManagePosition(cb, t, hhmm, o, h, l, c, deltaZ, bidStack, askStack, l2Live, imb);

            // ---------------- 7) pick ONE signal ----------------
            bool inWindow = !UseTimeFilter || (hhmm >= EntryStartET && hhmm < EntryEndET);
            Candidate best = null;
            if (inWindow && signalsToday < MaxSignalsPerDay)
            {
                foreach (Candidate cd in cands)
                {
                    if (posDir != 0 && cd.Dir == posDir) continue;
                    if (cd.Dir > 0 ? cb - lastLongBar < CooldownBars : cb - lastShortBar < CooldownBars) continue;
                    if (RequireL2InRealtime && State == State.Realtime && !cd.L2Ok) continue;

                    // Risk sanity: enforce minimum stop distance, reject oversized stops
                    double minRisk = MinRiskTicks * TickSize;
                    if (Math.Abs(c - cd.Stop) < minRisk) cd.Stop = c - cd.Dir * minRisk;
                    if (Math.Abs(c - cd.Stop) > MaxRiskRanges * avgRange) continue;
                    cd.Stop = mi.RoundToTickSize(cd.Stop);

                    if (best == null || cd.Prio > best.Prio || (cd.Prio == best.Prio && cd.Score > best.Score))
                        best = cd;
                }
            }

            if (best != null)
            {
                signal[0] = best.Dir * best.Code;
                if (best.Dir > 0) lastLongBar = cb; else lastShortBar = cb;
                signalsToday++;
                DrawSignal(best, t, h, l, cb);

                if (posDir != 0 && posDir == -best.Dir)
                {
                    MarkExit(cb, t, h, l, "↩ REVERSED", Brushes.Gray, 5);
                    FinishTrade(c, false, "REVERSE", t);
                }
                double t1, t2;
                ComputeTargets(best, c, prevHigh, prevLow, swingHi, swingLo, out t1, out t2);
                OpenPosition(best, c, t1, t2, t, cb, relVol, deltaZ, askStack, bidStack);
            }

            // ---------------- 8) panels (only where they are visible) ----------------
            bool lastHistorical = State == State.Historical && cb >= BarsArray[1].Count - 2;
            if (State == State.Realtime || lastHistorical)
            {
                if (ShowPanel) DrawPanel(delta, deltaZ, relVol, askStack, bidStack, l2Live, imb);
                if (ShowStats) DrawStats();
            }
        }

        // =================================================================================
        //  SIGNAL HELPERS
        // =================================================================================
        private void AddBullTrap(List<Candidate> cands, bool l2Live, double imb, bool strongDn, int bidStack)
        {
            bool l2ok  = l2Live && (imb <= -L2MinImbalance || HasWall(false, bullTrapLevel, WallTicks));
            int  score = 2 + (bullTrapAggressive ? 1 : 0) + (bidStack >= StackedMin ? 1 : 0) + (strongDn ? 1 : 0);
            if (score >= MinTrapScore)
                cands.Add(new Candidate { Dir = -1, Prio = 3, Code = 2, Name = bullTrapIsOR ? "ORB FAIL" : "BULL TRAP",
                                          Score = score + L2Bonus(l2ok), Max = 6, Stop = bullTrapExtreme + StopBufferTicks * TickSize, L2Ok = l2ok });
        }

        private void AddBearTrap(List<Candidate> cands, bool l2Live, double imb, bool strongUp, int askStack)
        {
            bool l2ok  = l2Live && (imb >= L2MinImbalance || HasWall(true, bearTrapLevel, WallTicks));
            int  score = 2 + (bearTrapAggressive ? 1 : 0) + (askStack >= StackedMin ? 1 : 0) + (strongUp ? 1 : 0);
            if (score >= MinTrapScore)
                cands.Add(new Candidate { Dir = 1, Prio = 3, Code = 2, Name = bearTrapIsOR ? "ORB FAIL" : "BEAR TRAP",
                                          Score = score + L2Bonus(l2ok), Max = 6, Stop = bearTrapExtreme - StopBufferTicks * TickSize, L2Ok = l2ok });
        }

        // L2 exists only in realtime, so it is shown in the score but never decides the minimum:
        // otherwise live trading admits signals the historical statistics never saw.
        private static int L2Bonus(bool l2ok) { return l2ok ? 1 : 0; }

        // Diagonal imbalances: ask(p) vs bid(p-1), bid(p) vs ask(p+1). Returns longest runs.
        private void ScanImbalances(VolumetricData vd, double lo, double hi, out int maxAskRun, out int maxBidRun)
        {
            maxAskRun = 0; maxBidRun = 0;
            int askRun = 0, bidRun = 0;
            int n = (int)Math.Round((hi - lo) / TickSize);

            long prevBid = 0;                                       // bid at p - 1 tick
            long curAsk  = vd.GetAskVolumeForPrice(mi.RoundToTickSize(lo));
            long curBid  = vd.GetBidVolumeForPrice(mi.RoundToTickSize(lo));

            for (int i = 0; i <= n; i++)
            {
                long nextAsk = i < n ? vd.GetAskVolumeForPrice(mi.RoundToTickSize(lo + (i + 1) * TickSize)) : 0;
                long nextBid = i < n ? vd.GetBidVolumeForPrice(mi.RoundToTickSize(lo + (i + 1) * TickSize)) : 0;

                bool askImb = i > 0 && curAsk >= ImbalanceMinVolume && curAsk >= ImbalanceRatio * Math.Max(prevBid, 1);
                bool bidImb = i < n && curBid >= ImbalanceMinVolume && curBid >= ImbalanceRatio * Math.Max(nextAsk, 1);

                askRun = askImb ? askRun + 1 : 0;
                bidRun = bidImb ? bidRun + 1 : 0;
                if (askRun > maxAskRun) maxAskRun = askRun;
                if (bidRun > maxBidRun) maxBidRun = bidRun;

                prevBid = curBid; curAsk = nextAsk; curBid = nextBid;
            }
        }

        // Total volume of the 2 outermost prices of the bar (low side or high side)
        private double EdgeVolume(VolumetricData vd, double edge, bool fromLow)
        {
            double p2 = mi.RoundToTickSize(edge + (fromLow ? TickSize : -TickSize));
            return vd.GetTotalVolumeForPrice(edge) + vd.GetTotalVolumeForPrice(p2);
        }

        private double TodRelVol(int b, double vol, double avgVol)
        {
            double baseVol = todN[b] >= TodMinSamples ? todAvg[b] : avgVol;
            return vol / Math.Max(baseVol, 1);
        }

        private void UpdateTod(int b, double vol)
        {
            if (todN[b] == 0) todAvg[b] = vol;
            else todAvg[b] += 0.05 * (vol - todAvg[b]);
            todN[b]++;
        }

        private void UpdateOR(DateTime et, DateTime t, double h, double l)
        {
            DateTime start = et.Date.AddHours(ORStartHour).AddMinutes(ORStartMinute);
            DateTime end   = start.AddMinutes(ORMinutes);

            if (et > start && et <= end)
            {
                if (orDate != et.Date)
                {
                    orDate = et.Date; orHigh = h; orLow = l; orBuilding = true; orComplete = false;
                    orStartChart = Times[1][1];
                    orUpValid = orDnValid = orUpDone = orDnDone = orUpRetested = orDnRetested = false;
                    orUpBar = orDnBar = orUpFirstAbove = orDnFirstBelow = -1;
                }
                else if (orBuilding) { orHigh = Math.Max(orHigh, h); orLow = Math.Min(orLow, l); }

                if (et >= end && orBuilding) { orBuilding = false; orComplete = true; orEndChart = t; }

                if (ShowOR)
                    Draw.Rectangle(this, "OFS_OR_" + orDate.ToString("yyyyMMdd"), false, orStartChart, orHigh, t, orLow, Brushes.DodgerBlue, Brushes.DodgerBlue, 8);
            }
            else if (orBuilding && orDate == et.Date && et > end)
            {
                orBuilding = false; orComplete = true; orEndChart = Times[1][1];
            }

            if (ShowOR && orComplete && orDate == et.Date && InORWindow(et))
            {
                string d = orDate.ToString("yyyyMMdd");
                Draw.Line(this, "OFS_ORH_" + d, false, orEndChart, orHigh, t, orHigh, Brushes.DodgerBlue, DashStyleHelper.Dash, 1);
                Draw.Line(this, "OFS_ORL_" + d, false, orEndChart, orLow,  t, orLow,  Brushes.DodgerBlue, DashStyleHelper.Dash, 1);
            }
        }

        private bool InORWindow(DateTime et)
        {
            DateTime start = et.Date.AddHours(ORStartHour).AddMinutes(ORStartMinute);
            return et > start.AddMinutes(ORMinutes) && et <= start.AddMinutes(ORMinutes + ORTradeWindow);
        }

        private DateTime ToEt(DateTime chartTime)
        {
            try   { return TimeZoneInfo.ConvertTime(chartTime, NinjaTrader.Core.Globals.GeneralOptions.TimeZoneInfo, estTz); }
            catch { return chartTime; }
        }

        // =================================================================================
        //  TRADE MANAGEMENT (virtual position — markers, warnings, statistics)
        // =================================================================================
        private void ComputeTargets(Candidate s, double entry, double prevHigh, double prevLow,
                                    double swingHi, double swingLo, out double t1, out double t2)
        {
            int    d    = s.Dir;
            double risk = Math.Max(Math.Abs(entry - s.Stop), TickSize);
            t1 = entry + d * risk;
            t2 = entry + d * 2 * risk;

            if (s.Code == 1)
                t2 = d > 0 ? prevHigh : prevLow;
            else if (s.Code == 2)
            {
                if (s.Name == "ORB FAIL")  { t1 = (orHigh + orLow) / 2; t2 = d > 0 ? orHigh : orLow; }
                else if (d < 0)            { t1 = (bullTrapLevel + swingLo) / 2; t2 = swingLo; }
                else                       { t1 = (bearTrapLevel + swingHi) / 2; t2 = swingHi; }
            }
            else if (s.Code == 3 || s.Code == 4)
            {
                double rng = orHigh - orLow;
                t1 = d > 0 ? orHigh + rng     : orLow - rng;
                t2 = d > 0 ? orHigh + 2 * rng : orLow - 2 * rng;
            }

            if (d * (t1 - entry) < 0.75 * risk) t1 = entry + d * risk;
            if (d * (t2 - t1)    < 0.5  * risk) t2 = t1 + d * risk;
            t1 = mi.RoundToTickSize(t1);
            t2 = mi.RoundToTickSize(t2);
        }

        private void OpenPosition(Candidate s, double entry, double t1, double t2, DateTime t, int cb,
                                  double relVol, double deltaZ, int askStack, int bidStack)
        {
            posId++;
            posDir      = s.Dir;
            posCode     = s.Code;
            posName     = s.Name;
            posScore    = s.Score;
            posMax      = s.Max;
            posL2       = s.L2Ok;
            posBar      = cb;
            posTime     = t;
            posEntry    = entry;
            posEntryEff = entry + posDir * SlippageTicks * TickSize;
            posStop     = s.Stop;
            posInitStop = s.Stop;
            posRisk     = Math.Max(Math.Abs(posEntryEff - posInitStop), TickSize);
            posT1       = t1;
            posT2       = t2;
            posT1R      = posDir * (posT1 - posEntryEff) / posRisk;
            posLevel    = s.Dir > 0 ? orHigh : orLow;
            posMfe      = 0;
            posMae      = 0;
            posRelVol   = relVol;
            posDeltaZ   = deltaZ;
            posAskStack = askStack;
            posBidStack = bidStack;
            t1Hit       = false;
            lastWarnBar  = -100000;
            lastWarnText = "-";
            DrawTradeLines(t);
        }

        // Closes the virtual trade, books R into the statistics and the optional CSV
        private void FinishTrade(double exitPx, bool isLimit, string reason, DateTime t)
        {
            if (posDir == 0) return;
            double exitEff = isLimit ? exitPx : exitPx - posDir * SlippageTicks * TickSize;
            double rRest   = posDir * (exitEff - posEntryEff) / posRisk;
            double r       = (ScaleOutAtT1 && t1Hit) ? 0.5 * posT1R + 0.5 * rRest : rRest;

            SetupStat st;
            if (!statByType.TryGetValue(posName, out st)) { st = new SetupStat(); statByType[posName] = st; }
            st.Add(r, t1Hit, posMfe, posMae);
            statAll.Add(r, t1Hit, posMfe, posMae);
            (posDir > 0 ? statLong : statShort).Add(r, t1Hit, posMfe, posMae);

            string sk = posScore + "/" + posMax;
            SetupStat ss;
            if (!statByScore.TryGetValue(sk, out ss)) { ss = new SetupStat(); statByScore[sk] = ss; }
            ss.Add(r, t1Hit, posMfe, posMae);

            if (csvPath != null)
            {
                CultureInfo ci = CultureInfo.InvariantCulture;
                string line = string.Join(",", new string[] {
                    posTime.ToString("yyyy-MM-dd HH:mm:ss", ci), t.ToString("yyyy-MM-dd HH:mm:ss", ci), posName,
                    posDir > 0 ? "LONG" : "SHORT", posScore.ToString(ci), posMax.ToString(ci),
                    posEntry.ToString(ci), posInitStop.ToString(ci), posT1.ToString(ci), posT2.ToString(ci), exitPx.ToString(ci), reason,
                    r.ToString("0.000", ci), posMfe.ToString("0.000", ci), posMae.ToString("0.000", ci), t1Hit ? "1" : "0",
                    posRelVol.ToString("0.00", ci), posDeltaZ.ToString("0.00", ci), posAskStack.ToString(ci), posBidStack.ToString(ci),
                    posL2 ? "1" : "0", State == State.Realtime ? "1" : "0" });
                try { System.IO.File.AppendAllText(csvPath, line + "\r\n"); } catch { }
            }

            DrawTradeLines(t);
            posDir = 0;
        }

        private void ManagePosition(int cb, DateTime t, int hhmm, double o, double h, double l, double c,
                                    double deltaZ, int bidStack, int askStack, bool l2Live, double imb)
        {
            if (posDir == 0 || cb <= posBar) return;
            bool   lng = posDir > 0;
            double buf = StopBufferTicks * TickSize;

            // 0) a position carried across a session boundary (early close, data gap, time
            //    filter off) was flat at the previous session's last bar
            if (BarsArray[1].IsFirstBarOfSession)
            {
                MarkExit(cb, t, h, l, "■ END OF DAY", Brushes.Gray, 6);
                FinishTrade(Closes[1][1], false, "EOD", Times[1][1]);
                return;
            }

            // 1) stop first (conservative when stop and target are both inside the bar).
            //    A gap through the stop fills at the open, not at the stop.
            if (lng ? l <= posStop : h >= posStop)
            {
                double fill = lng ? Math.Min(o, posStop) : Math.Max(o, posStop);
                posMae = Math.Max(posMae, (lng ? posEntryEff - fill : fill - posEntryEff) / posRisk);
                string what = !t1Hit ? "STOP" : Math.Abs(posStop - posEntry) < TickSize * 0.5 ? "BE STOP" : "TRAIL STOP";
                MarkExit(cb, t, h, l, "✕ " + what, Brushes.IndianRed, 4);
                FinishTrade(fill, false, what, t);
                return;
            }

            // excursions (in R) — only once the bar is known not to have stopped us out
            posMfe = Math.Max(posMfe, (lng ? h - posEntryEff : posEntryEff - l) / posRisk);
            posMae = Math.Max(posMae, (lng ? posEntryEff - l : h - posEntryEff) / posRisk);

            // 2) targets (limit fills; a gap through the target fills at the better open)
            if (!t1Hit && (lng ? h >= posT1 : l <= posT1))
            {
                t1Hit = true;
                MarkExit(cb, t, h, l, "✓ T1", Brushes.Gold, 2);
                if (MoveStopToBE) posStop = lng ? Math.Max(posStop, posEntry) : Math.Min(posStop, posEntry);
            }
            if (lng ? h >= posT2 : l <= posT2)
            {
                double fill = lng ? Math.Max(o, posT2) : Math.Min(o, posT2);
                MarkExit(cb, t, h, l, "✓ T2 TARGET", Brushes.Gold, 3);
                FinishTrade(fill, true, "T2", t);
                return;
            }

            // 3) end of the trading window -> virtual flatten (keeps statistics honest)
            if (UseTimeFilter && hhmm >= EntryEndET)
            {
                MarkExit(cb, t, h, l, "■ END OF DAY", Brushes.Gray, 6);
                FinishTrade(c, false, "EOD", t);
                return;
            }

            // 4) optional trail after T1 on bars where delta agrees with the trade
            if (TrailAfterT1 && t1Hit)
            {
                if (lng && deltaZ > 0)  posStop = Math.Max(posStop, mi.RoundToTickSize(l - buf));
                if (!lng && deltaZ < 0) posStop = Math.Min(posStop, mi.RoundToTickSize(h + buf));
            }

            // 5) order flow exit WARNINGS (position stays open)
            if (ShowExitWarnings && cb - lastWarnBar >= WarnCooldownBars)
            {
                List<string> reasons = new List<string>(4);
                if (lng)
                {
                    int m = bearSetup[0];
                    if (bidStack >= StackedMin && deltaZ < 0)                         reasons.Add("opp. stacked bids");
                    if ((m & 1) != 0)                                                 reasons.Add("exhaustion at high");
                    if ((m & 2) != 0)                                                 reasons.Add("absorption at high");
                    if ((m & 4) != 0)                                                 reasons.Add("delta divergence");
                    if (deltaZ <= -StrongDeltaZ && c < o && c < Lows[1][1])           reasons.Add("delta flip");
                    if ((posCode == 3 || posCode == 4) && c < posLevel)               reasons.Add("back inside OR");
                    if (l2Live && imb <= -L2MinImbalance && HasWall(false, c, WallTicks * 2)) reasons.Add("L2 ask wall ahead");
                }
                else
                {
                    int m = bullSetup[0];
                    if (askStack >= StackedMin && deltaZ > 0)                         reasons.Add("opp. stacked asks");
                    if ((m & 1) != 0)                                                 reasons.Add("exhaustion at low");
                    if ((m & 2) != 0)                                                 reasons.Add("absorption at low");
                    if ((m & 4) != 0)                                                 reasons.Add("delta divergence");
                    if (deltaZ >= StrongDeltaZ && c > o && c > Highs[1][1])           reasons.Add("delta flip");
                    if ((posCode == 3 || posCode == 4) && c > posLevel)               reasons.Add("back inside OR");
                    if (l2Live && imb >= L2MinImbalance && HasWall(true, c, WallTicks * 2)) reasons.Add("L2 bid wall ahead");
                }

                if (reasons.Count >= MinWarnReasons)
                {
                    lastWarnBar  = cb;
                    string why   = string.Join(" + ", reasons.ToArray());
                    lastWarnText = why + string.Format(" @ {0:HH:mm}", t);
                    MarkExit(cb, t, h, l, "⚠ EXIT? " + why, WarnBrush, 1);

                    if (EnableExitAlerts && State == State.Realtime)
                        Alert("OFS_W_" + cb, Priority.Medium, string.Format("OrderFlow EXIT WARNING ({0}): {1}", lng ? "long" : "short", why),
                              NinjaTrader.Core.Globals.InstallDir + @"\sounds\Alert4.wav", 10, Brushes.Black, WarnBrush);
                }
            }

            DrawTradeLines(t);
        }

        private void MarkExit(int cb, DateTime t, double h, double l, string text, Brush brush, int code)
        {
            if (Math.Abs(exitSeries[0]) < code) exitSeries[0] = posDir * code;

            double off = ArrowOffsetTicks * TickSize;
            string tag = "OFS_EX_" + cb + "_" + code;
            int    yOff = 18 + (code == 1 ? 0 : 14);
            if (posDir > 0)
            {
                Draw.Diamond(this, tag, false, t, h + off, brush);
                Draw.Text(this, tag + "_T", false, text, t, h + off, yOff, brush, smallFont, TextAlignment.Center, Brushes.Transparent, Brushes.Black, 60);
            }
            else
            {
                Draw.Diamond(this, tag, false, t, l - off, brush);
                Draw.Text(this, tag + "_T", false, text, t, l - off, -yOff, brush, smallFont, TextAlignment.Center, Brushes.Transparent, Brushes.Black, 60);
            }
        }

        private void DrawTradeLines(DateTime t)
        {
            if (!ShowTradeLines || posDir == 0) return;
            string p = "OFS_P" + posId + "_";
            Draw.Line(this, p + "E",  false, posTime, posEntry, t, posEntry, Brushes.Gray,      DashStyleHelper.Solid, 1);
            Draw.Line(this, p + "SL", false, posTime, posStop,  t, posStop,  Brushes.IndianRed, DashStyleHelper.Dash,  2);
            Draw.Line(this, p + "T1", false, posTime, posT1,    t, posT1,    Brushes.Gold,      DashStyleHelper.Dot,   1);
            Draw.Line(this, p + "T2", false, posTime, posT2,    t, posT2,    Brushes.Gold,      DashStyleHelper.Dot,   2);
        }

        // =================================================================================
        //  DRAWING
        // =================================================================================
        private void DrawSignal(Candidate s, DateTime t, double h, double l, int cb)
        {
            Brush  b   = s.Dir > 0 ? LongBrush : ShortBrush;
            double off = ArrowOffsetTicks * TickSize;
            string tag = "OFS_SIG_" + cb;
            string txt = string.Format("{0} {1}  {2}/{3}{4}\nSL {5}", s.Dir > 0 ? "▲" : "▼", s.Name, s.Score, s.Max,
                                       s.L2Ok ? " L2" : "", mi.FormatPrice(s.Stop));

            if (s.Dir > 0)
            {
                Draw.ArrowUp(this, tag, false, t, l - off, b);
                if (ShowLabels) Draw.Text(this, tag + "_T", false, txt, t, l - off, -34, b, labelFont, TextAlignment.Center, Brushes.Transparent, Brushes.Black, 70);
            }
            else
            {
                Draw.ArrowDown(this, tag, false, t, h + off, b);
                if (ShowLabels) Draw.Text(this, tag + "_T", false, txt, t, h + off, 34, b, labelFont, TextAlignment.Center, Brushes.Transparent, Brushes.Black, 70);
            }

            lastSignalText = string.Format("{0} {1} {2}/{3} @ {4:HH:mm}", s.Dir > 0 ? "LONG" : "SHORT", s.Name, s.Score, s.Max, t);

            if (EnableAlerts && State == State.Realtime)
                Alert("OFS_" + cb, Priority.High, "OrderFlow: " + lastSignalText + "  SL " + mi.FormatPrice(s.Stop),
                      NinjaTrader.Core.Globals.InstallDir + @"\sounds\Alert2.wav", 10, Brushes.Black, b);
        }

        private void DrawPanel(double delta, double deltaZ, double relVol, int askStack, int bidStack, bool l2Live, double imb)
        {
            string l2 = l2Live
                ? string.Format("{0:+0%;-0%;0%} {1}", imb, imb >= L2MinImbalance ? "BID heavy" : imb <= -L2MinImbalance ? "ASK heavy" : "neutral")
                : "n/a (historical / no depth)";
            string pos = posDir == 0
                ? "FLAT"
                : string.Format("{0} {1} @ {2}  SL {3}\n            T1 {4}{5}  T2 {6}  ({7:+0.0;-0.0}R open)",
                                posDir > 0 ? "LONG" : "SHORT", posName, mi.FormatPrice(posEntry), mi.FormatPrice(posStop),
                                mi.FormatPrice(posT1), t1Hit ? " ✓" : "", mi.FormatPrice(posT2),
                                posDir * (Closes[1][0] - posEntryEff) / posRisk);

            string txt = string.Format(
                "ORDER FLOW SIGNALS\n" +
                "Bar delta : {0:+#,0;-#,0;0}  (z {1:+0.0;-0.0})\n" +
                "Rel. vol  : {2:0.00}x time-of-day\n" +
                "Cum delta : {3:+#,0;-#,0;0}\n" +
                "Stacked   : ask {4}  bid {5}\n" +
                "L2 book   : {6}\n" +
                "Today     : {7}/{8} signals\n" +
                "Last      : {9}\n" +
                "Position  : {10}\n" +
                "Warning   : {11}",
                delta, deltaZ, relVol, cumDelta[0], askStack, bidStack, l2, signalsToday, MaxSignalsPerDay,
                lastSignalText, pos, posDir == 0 ? "-" : lastWarnText);
            Draw.TextFixed(this, "OFS_PANEL", txt, TextPosition.TopRight, Brushes.WhiteSmoke, panelFont, Brushes.Transparent, Brushes.Black, 75);
        }

        private void DrawStats()
        {
            StringBuilder sb = new StringBuilder();
            sb.AppendFormat("SIGNAL STATS  ({0} tick slip{1})\n", SlippageTicks, ScaleOutAtT1 ? ", 50% at T1" : "");
            sb.AppendLine("Type          N   Win%  T1%   AvgR    PF   MFE  MAE");
            foreach (string k in TypeOrder)
            {
                SetupStat s;
                if (statByType.TryGetValue(k, out s) && s.N > 0) sb.AppendLine(StatRow(k, s));
            }
            sb.AppendLine(StatRow("LONG", statLong));
            sb.AppendLine(StatRow("SHORT", statShort));
            sb.AppendLine(StatRow("TOTAL", statAll));
            sb.AppendLine("By score:");
            foreach (KeyValuePair<string, SetupStat> kv in statByScore)
                sb.AppendLine(StatRow("  " + kv.Key, kv.Value));
            if (statAll.N < 30) sb.Append("(< 30 trades: not significant yet — load more days)");
            else                sb.Append("(historical rows have no L2 — live results may differ)");

            Draw.TextFixed(this, "OFS_STATS", sb.ToString(), TextPosition.BottomLeft, Brushes.WhiteSmoke, panelFont, Brushes.Transparent, Brushes.Black, 75);
        }

        private static string StatRow(string name, SetupStat s)
        {
            if (s.N == 0) return string.Format("{0,-12}{1,3}", name, 0);
            return string.Format(CultureInfo.InvariantCulture, "{0,-12}{1,3}  {2,4:0}%  {3,3:0}%  {4,6:+0.00;-0.00}  {5,4:0.0}  {6,4:0.0}  {7,3:0.0}",
                                 name, s.N, s.WinPct * 100, s.T1Pct * 100, s.AvgR, Math.Min(s.PF, 99), s.SumMfe / s.N, s.SumMae / s.N);
        }

        private static int PopCount(int m) { return (m & 1) + ((m >> 1) & 1) + ((m >> 2) & 1); }

        private static string MaskText(int m)
        {
            string s = "";
            if ((m & 1) != 0) s += "EXH ";
            if ((m & 2) != 0) s += "ABS ";
            if ((m & 4) != 0) s += "DIV ";
            return s.Trim();
        }

        #region Properties
        [Browsable(false), XmlIgnore] public Series<double> Signal     { get { Update(); return signal; } }
        [Browsable(false), XmlIgnore] public Series<double> ExitSignal { get { Update(); return exitSeries; } }

        // 1. Footprint
        [Range(1.5, 10), Display(Name = "Imbalance ratio", Description = "Diagonal ask/bid ratio (3 = 300%)", GroupName = "1. Footprint & stats base", Order = 1)]
        public double ImbalanceRatio { get; set; }
        [Range(1, int.MaxValue), Display(Name = "Imbalance min volume", Description = "Min contracts on the dominant side (ES/NQ 5-10, micros 2-3)", GroupName = "1. Footprint & stats base", Order = 2)]
        public int ImbalanceMinVolume { get; set; }
        [Range(2, 10), Display(Name = "Stacked imbalance min", GroupName = "1. Footprint & stats base", Order = 3)]
        public int StackedMin { get; set; }
        [Range(10, 300), Display(Name = "Statistics window (bars)", Description = "Window for average range and delta% z-score", GroupName = "1. Footprint & stats base", Order = 4)]
        public int AvgPeriod { get; set; }
        [Range(0.2, 4), Display(Name = "Strong delta z-score", Description = "Delta% this many std-devs from normal = strong", GroupName = "1. Footprint & stats base", Order = 5)]
        public double StrongDeltaZ { get; set; }

        // 2. Reversal
        [Range(3, 100), Display(Name = "Swing lookback (within session)", GroupName = "2. Reversal", Order = 1)]
        public int SwingLookback { get; set; }
        [Range(0.05, 1.0), Display(Name = "Exhaustion ratio", Description = "Volume at the 2 extreme prices vs average volume per price", GroupName = "2. Reversal", Order = 2)]
        public double ExhaustionRatio { get; set; }
        [Range(1.0, 10), Display(Name = "Absorption rel. volume", Description = "x normal volume for this time of day", GroupName = "2. Reversal", Order = 3)]
        public double AbsRelVol { get; set; }
        [Range(0.1, 3), Display(Name = "Absorption range x avg", GroupName = "2. Reversal", Order = 4)]
        public double AbsRangeMult { get; set; }
        [Range(0.2, 4), Display(Name = "Absorption delta z-score", GroupName = "2. Reversal", Order = 5)]
        public double AbsDeltaZ { get; set; }
        [Range(1, 10), Display(Name = "Setup window (bars)", GroupName = "2. Reversal", Order = 6)]
        public int SetupWindow { get; set; }
        [Range(1, 6), Display(Name = "Min reversal score (of 6 + L2)", Description = "Footprint points required; the live-only L2 point is shown but never counts toward the minimum", GroupName = "2. Reversal", Order = 7)]
        public int MinReversalScore { get; set; }

        // 3. Traps
        [Range(3, 200), Display(Name = "Level lookback (bars)", GroupName = "3. Traps", Order = 1)]
        public int LevelLookback { get; set; }
        [Range(0, 50), Display(Name = "Break ticks", GroupName = "3. Traps", Order = 2)]
        public int BreakTicks { get; set; }
        [Range(1, 10), Display(Name = "Trap confirm bars", GroupName = "3. Traps", Order = 3)]
        public int TrapBars { get; set; }
        [Range(0, 50), Display(Name = "Follow-through ticks", Description = "Close this far beyond the break bar = real breakout, cancel trap", GroupName = "3. Traps", Order = 4)]
        public int FollowTicks { get; set; }
        [Range(1, 5), Display(Name = "Min trap score (of 5 + L2)", Description = "Footprint points required; the live-only L2 point is shown but never counts toward the minimum", GroupName = "3. Traps", Order = 5)]
        public int MinTrapScore { get; set; }

        // 4. ORB
        [Display(Name = "Use ORB", GroupName = "4. ORB", Order = 1)]
        public bool UseORB { get; set; }
        [Range(0, 23), Display(Name = "OR start hour (ET)", GroupName = "4. ORB", Order = 2)]
        public int ORStartHour { get; set; }
        [Range(0, 59), Display(Name = "OR start minute (ET)", GroupName = "4. ORB", Order = 3)]
        public int ORStartMinute { get; set; }
        [Range(1, 240), Display(Name = "OR length (minutes)", GroupName = "4. ORB", Order = 4)]
        public int ORMinutes { get; set; }
        [Range(5, 600), Display(Name = "Trade window after OR (min)", GroupName = "4. ORB", Order = 5)]
        public int ORTradeWindow { get; set; }
        [Range(0.3, 10), Display(Name = "Breakout rel. volume", Description = "x normal volume for this time of day", GroupName = "4. ORB", Order = 6)]
        public double ORRelVol { get; set; }
        [Range(0, 50), Display(Name = "Retest tolerance ticks", GroupName = "4. ORB", Order = 7)]
        public int RetestTicks { get; set; }
        [Range(1, 50), Display(Name = "Invalidate ticks", GroupName = "4. ORB", Order = 8)]
        public int InvalidTicks { get; set; }
        [Range(1, 4), Display(Name = "Min ORB score (of 4 + L2)", Description = "Footprint points required; the live-only L2 point is shown but never counts toward the minimum", GroupName = "4. ORB", Order = 9)]
        public int MinORScore { get; set; }

        // 5. Level 2
        [Display(Name = "Use Level 2", GroupName = "5. Level 2", Order = 1)]
        public bool UseL2 { get; set; }
        [Range(1, 50), Display(Name = "Book levels", GroupName = "5. Level 2", Order = 2)]
        public int L2Levels { get; set; }
        [Range(0.01, 1), Display(Name = "Min book imbalance", GroupName = "5. Level 2", Order = 3)]
        public double L2MinImbalance { get; set; }
        [Range(1.5, 20), Display(Name = "Wall = x avg size", GroupName = "5. Level 2", Order = 4)]
        public double WallMultiple { get; set; }
        [Range(0, 20), Display(Name = "Wall distance ticks", GroupName = "5. Level 2", Order = 5)]
        public int WallTicks { get; set; }
        [Display(Name = "Require L2 confirm (live)", GroupName = "5. Level 2", Order = 6)]
        public bool RequireL2InRealtime { get; set; }

        // 6. Signals, risk & time
        [Range(0, 100), Display(Name = "Cooldown bars (per side)", GroupName = "6. Signals, risk & time", Order = 1)]
        public int CooldownBars { get; set; }
        [Range(1, 100), Display(Name = "Max signals per day", GroupName = "6. Signals, risk & time", Order = 2)]
        public int MaxSignalsPerDay { get; set; }
        [Range(0, 50), Display(Name = "Stop buffer ticks", GroupName = "6. Signals, risk & time", Order = 3)]
        public int StopBufferTicks { get; set; }
        [Range(1, 100), Display(Name = "Min stop distance (ticks)", GroupName = "6. Signals, risk & time", Order = 4)]
        public int MinRiskTicks { get; set; }
        [Range(0.5, 20), Display(Name = "Max stop (x avg bar range)", Description = "Signals needing a wider stop are skipped", GroupName = "6. Signals, risk & time", Order = 5)]
        public double MaxRiskRanges { get; set; }
        [Display(Name = "Use time filter (ET)", GroupName = "6. Signals, risk & time", Order = 6)]
        public bool UseTimeFilter { get; set; }
        [Range(0, 2359), Display(Name = "Entries from (HHMM ET)", Description = "930 = 15:30 Copenhagen", GroupName = "6. Signals, risk & time", Order = 7)]
        public int EntryStartET { get; set; }
        [Range(0, 2359), Display(Name = "Entries until / flatten (HHMM ET)", Description = "1600 = 22:00 Copenhagen", GroupName = "6. Signals, risk & time", Order = 8)]
        public int EntryEndET { get; set; }
        [Range(0, 50), Display(Name = "Arrow offset ticks", GroupName = "6. Signals, risk & time", Order = 9)]
        public int ArrowOffsetTicks { get; set; }
        [Display(Name = "Show setup markers (EXH/ABS/DIV)", GroupName = "6. Signals, risk & time", Order = 10)]
        public bool ShowSetupMarkers { get; set; }
        [Display(Name = "Show signal labels", GroupName = "6. Signals, risk & time", Order = 11)]
        public bool ShowLabels { get; set; }
        [Display(Name = "Show info panel", GroupName = "6. Signals, risk & time", Order = 12)]
        public bool ShowPanel { get; set; }
        [Display(Name = "Show opening range", GroupName = "6. Signals, risk & time", Order = 13)]
        public bool ShowOR { get; set; }
        [Display(Name = "Enable alerts", GroupName = "6. Signals, risk & time", Order = 14)]
        public bool EnableAlerts { get; set; }

        [XmlIgnore, Display(Name = "Long color", GroupName = "6. Signals, risk & time", Order = 15)]
        public Brush LongBrush { get; set; }
        [Browsable(false)]
        public string LongBrushSerializable { get { return Serialize.BrushToString(LongBrush); } set { LongBrush = Serialize.StringToBrush(value); } }

        [XmlIgnore, Display(Name = "Short color", GroupName = "6. Signals, risk & time", Order = 16)]
        public Brush ShortBrush { get; set; }
        [Browsable(false)]
        public string ShortBrushSerializable { get { return Serialize.BrushToString(ShortBrush); } set { ShortBrush = Serialize.StringToBrush(value); } }

        // 7. Exits (warnings only)
        [Display(Name = "Show exit warnings", GroupName = "7. Exits (warnings)", Order = 1)]
        public bool ShowExitWarnings { get; set; }
        [Range(1, 5), Display(Name = "Min reasons per warning", GroupName = "7. Exits (warnings)", Order = 2)]
        public int MinWarnReasons { get; set; }
        [Range(1, 50), Display(Name = "Bars between warnings", GroupName = "7. Exits (warnings)", Order = 3)]
        public int WarnCooldownBars { get; set; }
        [Display(Name = "Move stop to breakeven at T1", GroupName = "7. Exits (warnings)", Order = 4)]
        public bool MoveStopToBE { get; set; }
        [Display(Name = "Trail stop after T1", GroupName = "7. Exits (warnings)", Order = 5)]
        public bool TrailAfterT1 { get; set; }
        [Display(Name = "Show entry / SL / target lines", GroupName = "7. Exits (warnings)", Order = 6)]
        public bool ShowTradeLines { get; set; }
        [Display(Name = "Exit warning alerts", GroupName = "7. Exits (warnings)", Order = 7)]
        public bool EnableExitAlerts { get; set; }

        [XmlIgnore, Display(Name = "Warning color", GroupName = "7. Exits (warnings)", Order = 8)]
        public Brush WarnBrush { get; set; }
        [Browsable(false)]
        public string WarnBrushSerializable { get { return Serialize.BrushToString(WarnBrush); } set { WarnBrush = Serialize.StringToBrush(value); } }

        // 8. Statistics
        [Display(Name = "Show statistics panel", GroupName = "8. Statistics", Order = 1)]
        public bool ShowStats { get; set; }
        [Range(0, 20), Display(Name = "Slippage ticks (per side)", Description = "Applied to entry and to stop/EOD/reverse exits; targets are limit fills", GroupName = "8. Statistics", Order = 2)]
        public int SlippageTicks { get; set; }
        [Display(Name = "Scale out 50% at T1", GroupName = "8. Statistics", Order = 3)]
        public bool ScaleOutAtT1 { get; set; }
        [Display(Name = "Log trades to CSV", Description = "Writes to Documents\\NinjaTrader 8\\OFS_trades_<instrument>_<time>.csv", GroupName = "8. Statistics", Order = 4)]
        public bool LogTradesCsv { get; set; }
        #endregion
    }
}

#region NinjaScript generated code. Neither change nor remove.

namespace NinjaTrader.NinjaScript.Indicators
{
	public partial class Indicator : NinjaTrader.Gui.NinjaScript.IndicatorRenderBase
	{
		private OrderFlowCandleSignals[] cacheOrderFlowCandleSignals;
		public OrderFlowCandleSignals OrderFlowCandleSignals()
		{
			return OrderFlowCandleSignals(Input);
		}

		public OrderFlowCandleSignals OrderFlowCandleSignals(ISeries<double> input)
		{
			if (cacheOrderFlowCandleSignals != null)
				for (int idx = 0; idx < cacheOrderFlowCandleSignals.Length; idx++)
					if (cacheOrderFlowCandleSignals[idx] != null &&  cacheOrderFlowCandleSignals[idx].EqualsInput(input))
						return cacheOrderFlowCandleSignals[idx];
			return CacheIndicator<OrderFlowCandleSignals>(new OrderFlowCandleSignals(), input, ref cacheOrderFlowCandleSignals);
		}
	}
}

namespace NinjaTrader.NinjaScript.MarketAnalyzerColumns
{
	public partial class MarketAnalyzerColumn : MarketAnalyzerColumnBase
	{
		public Indicators.OrderFlowCandleSignals OrderFlowCandleSignals()
		{
			return indicator.OrderFlowCandleSignals(Input);
		}

		public Indicators.OrderFlowCandleSignals OrderFlowCandleSignals(ISeries<double> input )
		{
			return indicator.OrderFlowCandleSignals(input);
		}
	}
}

namespace NinjaTrader.NinjaScript.Strategies
{
	public partial class Strategy : NinjaTrader.Gui.NinjaScript.StrategyRenderBase
	{
		public Indicators.OrderFlowCandleSignals OrderFlowCandleSignals()
		{
			return indicator.OrderFlowCandleSignals(Input);
		}

		public Indicators.OrderFlowCandleSignals OrderFlowCandleSignals(ISeries<double> input )
		{
			return indicator.OrderFlowCandleSignals(input);
		}
	}
}

#endregion
