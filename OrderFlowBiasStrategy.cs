// =====================================================================================
//  OrderFlowBiasStrategy.cs  —  NinjaTrader 8 strategy
//
//  Turns live order flow into one directional read, logs it for calibration, and can
//  (optionally) trade it.
//
//  Five components, each -1 (sellers) .. +1 (buyers):
//    1. Aggression : contracts lifting the ask minus contracts hitting the bid, last N bars
//    2. Book lean  : persistence-weighted resting bid size vs ask size (top DomDepth rows)
//    3. Defence    : icebergs (rows eaten and refilled) and absorption (block prints that
//                    produced no follow-through), by side
//    4. Pulls      : large resting size cancelled before price reached it — asks pulled
//                    clears the road up, bids pulled clears the road down
//    5. Blocks     : block prints at the ask vs at the bid, last N bars
//
//  Bias = weighted average. Agreement = share of active components pointing the same way.
//
//  Drawn: an arrow at column +3 (length = bias, brightness = agreement) and a panel
//  (top-left) with every component, the strongest clusters and their status.
//
//  Logged (realtime only — history has no Level 2): one CSV row per closed bar with every
//  component, the bias, and where price went 5 / 10 / 20 bars later, in ticks. That file
//  is what turns "bias" into a measured probability and sets the weights from data.
//
//  Trading (off by default): enter when |bias| >= EntryBias and agreement >= MinAgreement,
//  tick stop / target, exit when bias flips past ExitBias, daily cap, time window, flat at
//  session close. Nothing is sent to the broker unless EnableTrading is on.
//
//  Level 2 is live only. Keep the OrderFlowBubbles indicator on the chart for the map.
// =====================================================================================

#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Globalization;
using System.Text;
using System.Windows.Media;
using System.Xml.Serialization;
using NinjaTrader.Cbi;
using NinjaTrader.Data;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Chart;
using NinjaTrader.Gui.Tools;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.DrawingTools;
#endregion

namespace NinjaTrader.NinjaScript.Strategies
{
    public class OrderFlowBiasStrategy : Strategy
    {
        #region Private types
        private class BookLevel { public double Price; public long Volume; }

        private class Cluster
        {
            public double   Price;
            public double   Persist;
            public DateTime Stamp;
            public bool     IsBid;
        }

        private class Level
        {
            public double Price;
            public double BidVol;
            public double AskVol;
            public double Total { get { return BidVol + AskVol; } }
        }

        private class Ice
        {
            public long     Peak;
            public bool     Dropped;
            public int      Refills;
            public DateTime Last;
        }

        private class PendingRow
        {
            public int      Bar;
            public DateTime Time;
            public double   Close;
            public string   Fields;
        }
        #endregion

        #region Fields
        private readonly List<BookLevel> _bids = new List<BookLevel>();
        private readonly List<BookLevel> _asks = new List<BookLevel>();
        private readonly Dictionary<double, Cluster> _clusters = new Dictionary<double, Cluster>();
        private readonly Dictionary<double, Ice> _ice = new Dictionary<double, Ice>();
        private readonly Dictionary<int, Dictionary<double, Level>> _trades = new Dictionary<int, Dictionary<double, Level>>();
        private readonly object _sync = new object();

        private MasterInstrument _mi;
        private int      _depthEvents;
        private DateTime _lastDepthTime = DateTime.MinValue;
        private DateTime _lastCleanup   = DateTime.MinValue;
        private const double MaxGapSeconds = 5.0;

        private double   _lastPrice, _liveBid, _liveAsk;
        private DateTime _lastTradeTime = DateTime.MinValue;
        private int      _lastSide = 1;

        // pulled size by side, decaying
        private double   _pullAsk, _pullBid;
        private DateTime _pullStamp = DateTime.MinValue;

        // components and result (written on bar close, read by render)
        private double _cAggression, _cBookLean, _cDefence, _cPulls, _cBlocks;
        private double _bias, _agreement;
        private bool   _biasValid;
        private string _clusterText = "";

        private DateTime _lastRefresh = DateTime.MinValue;
        private SharpDX.Direct2D1.Brush _buyDx, _sellDx;

        private readonly List<PendingRow> _pending = new List<PendingRow>();
        private string _csvPath;

        private int      _tradesToday;
        private DateTime _tradeDate = DateTime.MinValue;
        #endregion

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description                              = "Order-flow bias from the live book: aggression, book lean, defence, pulls and blocks combined into one directional read with calibration log and optional trading.";
                Name                                     = "OrderFlowBiasStrategy";
                Calculate                                = Calculate.OnEachTick;
                EntriesPerDirection                      = 1;
                EntryHandling                            = EntryHandling.AllEntries;
                IsExitOnSessionCloseStrategy             = true;
                ExitOnSessionCloseSeconds                = 30;
                IsFillLimitOnTouch                       = false;
                MaximumBarsLookBack                      = MaximumBarsLookBack.TwoHundredFiftySix;
                OrderFillResolution                      = OrderFillResolution.Standard;
                Slippage                                 = 0;
                StartBehavior                            = StartBehavior.WaitUntilFlat;
                TimeInForce                              = TimeInForce.Gtc;
                TraceOrders                              = false;
                RealtimeErrorHandling                    = RealtimeErrorHandling.StopCancelClose;
                StopTargetHandling                       = StopTargetHandling.PerEntryExecution;
                BarsRequiredToTrade                      = 20;
                IsInstantiatedOnEachOptimizationIteration = true;

                // 1. Data
                DomDepth            = 10;
                ClusterHalfLifeSec  = 60;
                AggressionBars      = 3;
                BlockTradeThreshold = 50;
                BlockLookbackBars   = 3;
                LargeOrderThreshold = 100;
                IcebergRefills      = 5;
                IcebergWindowSec    = 300;
                PullHalfLifeSec     = 120;

                // 2. Weights
                WeightAggression = 1.0;
                WeightBookLean   = 0.5;
                WeightDefence    = 1.0;
                WeightPulls      = 1.0;
                WeightBlocks     = 0.75;

                // 3. Trading
                EnableTrading   = false;
                Contracts       = 1;
                EntryBias       = 0.5;
                MinAgreement    = 0.75;
                ExitBias        = 0.3;
                StopTicks       = 20;
                TargetTicks     = 40;
                MaxTradesPerDay = 6;
                EntryStartHHMM  = 930;
                EntryEndHHMM    = 1545;

                // 4. Output
                ShowArrow   = true;
                ShowPanel   = true;
                ArrowMaxPx  = 80;
                LogToCsv    = true;
                ForwardBars = 20;
                BuyBrush    = Brushes.DeepSkyBlue;
                SellBrush   = Brushes.OrangeRed;
            }
            else if (State == State.Configure)
            {
                AddDataSeries(BarsPeriodType.Tick, 1);
                SetStopLoss(CalculationMode.Ticks, StopTicks);
                SetProfitTarget(CalculationMode.Ticks, TargetTicks);
            }
            else if (State == State.DataLoaded)
            {
                _mi = Instrument.MasterInstrument;
                if (LogToCsv)
                {
                    _csvPath = System.IO.Path.Combine(NinjaTrader.Core.Globals.UserDataDir,
                               "OrderFlowBias_" + _mi.Name + "_" + DateTime.Now.ToString("yyyyMMdd_HHmmss") + ".csv");
                    try
                    {
                        System.IO.File.WriteAllText(_csvPath,
                            "time,instrument,close,bias,agreement,aggression,booklean,defence,pulls,blocks,bidrows,askrows,fwd5,fwd10,fwd20\r\n");
                    }
                    catch { _csvPath = null; }
                }
            }
            else if (State == State.Terminated)
            {
                FlushPending(true);
                ReleaseDx();
            }
        }

        // =================================================================================
        //  MARKET DATA
        // =================================================================================
        protected override void OnMarketData(MarketDataEventArgs e)
        {
            if (e.MarketDataType == MarketDataType.Bid)      _liveBid = e.Price;
            else if (e.MarketDataType == MarketDataType.Ask) _liveAsk = e.Price;
        }

        protected override void OnMarketDepth(MarketDepthEventArgs e)
        {
            lock (_sync)
            {
                Integrate(e.Time);
                _depthEvents++;

                if (e.IsReset) { _bids.Clear(); _asks.Clear(); return; }

                List<BookLevel> side = e.MarketDataType == MarketDataType.Bid ? _bids
                                     : e.MarketDataType == MarketDataType.Ask ? _asks
                                     : null;
                if (side == null) return;

                if (e.Operation == Operation.Add)
                {
                    if (e.Position <= side.Count) side.Insert(e.Position, new BookLevel { Price = e.Price, Volume = e.Volume });
                    TrackIceberg(e.Price, e.Volume, e.Time);
                }
                else if (e.Operation == Operation.Update)
                {
                    if (e.Position < side.Count)
                    {
                        TrackPull(side[e.Position].Price, side[e.Position].Volume, e.Volume, e.Time);
                        side[e.Position].Price  = e.Price;
                        side[e.Position].Volume = e.Volume;
                    }
                    TrackIceberg(e.Price, e.Volume, e.Time);
                }
                else if (e.Operation == Operation.Remove)
                {
                    if (e.Position < side.Count)
                    {
                        double removedPrice = side[e.Position].Price;
                        long   removedSize  = side[e.Position].Volume;
                        side.RemoveAt(e.Position);
                        TrackPull(removedPrice, removedSize, 0, e.Time);
                        TrackIceberg(removedPrice, 0, e.Time);
                    }
                }
            }
            RequestRefresh();
        }

        private void Integrate(DateTime now)
        {
            if (_lastDepthTime != DateTime.MinValue)
            {
                double dt = Math.Min((now - _lastDepthTime).TotalSeconds, MaxGapSeconds);
                if (dt > 0)
                {
                    Credit(_bids, dt, now, true);
                    Credit(_asks, dt, now, false);
                }
            }
            if (now > _lastDepthTime) _lastDepthTime = now;

            if ((now - _lastCleanup).TotalSeconds > 10)
            {
                _lastCleanup = now;
                double max = 0;
                foreach (Cluster c in _clusters.Values) max = Math.Max(max, Effective(c, now));
                List<double> dead = new List<double>();
                foreach (Cluster c in _clusters.Values)
                    if (Effective(c, now) < 0.01 * max) dead.Add(c.Price);
                foreach (double p in dead) _clusters.Remove(p);
            }
        }

        private void Credit(List<BookLevel> side, double dt, DateTime now, bool isBid)
        {
            int n = Math.Min(DomDepth, side.Count);
            for (int i = 0; i < n; i++)
            {
                if (side[i].Volume <= 0) continue;
                double p = _mi.RoundToTickSize(side[i].Price);
                Cluster c;
                if (!_clusters.TryGetValue(p, out c)) { c = new Cluster { Price = p, Stamp = now }; _clusters[p] = c; }
                c.Persist = Effective(c, now) + side[i].Volume * dt;
                c.Stamp   = now;
                c.IsBid   = isBid;
            }
        }

        private double Effective(Cluster c, DateTime now)
        {
            double age = (now - c.Stamp).TotalSeconds;
            if (age <= 0) return c.Persist;
            return c.Persist * Math.Pow(0.5, age / Math.Max(ClusterHalfLifeSec, 1));
        }

        private void TrackIceberg(double price, long size, DateTime now)
        {
            double p = _mi.RoundToTickSize(price);
            Ice ice;
            if (!_ice.TryGetValue(p, out ice))
            {
                if (size < LargeOrderThreshold) return;
                _ice[p] = new Ice { Peak = size, Last = now };
                return;
            }
            if ((now - ice.Last).TotalSeconds > IcebergWindowSec) { ice.Refills = 0; ice.Dropped = false; ice.Peak = 0; }

            if (size >= LargeOrderThreshold)
            {
                if (ice.Dropped) { ice.Refills++; ice.Dropped = false; }
                ice.Peak = Math.Max(ice.Peak, size);
                ice.Last = now;
            }
            else if (ice.Peak >= LargeOrderThreshold && size <= ice.Peak / 2)
            {
                ice.Dropped = true;
                ice.Peak    = 0;
            }
        }

        // Large size that vanishes while price is not trading at that level was cancelled, not filled
        private void TrackPull(double price, long before, long after, DateTime now)
        {
            if (before < LargeOrderThreshold || after > before / 4) return;
            double p = _mi.RoundToTickSize(price);
            if (_lastPrice <= 0 || Math.Abs(p - _lastPrice) < TickSize * 0.5) return;
            if (Math.Abs(p - _lastPrice) <= TickSize && (now - _lastTradeTime).TotalSeconds < 2) return;

            DecayPulls(now);
            double pulled = before - after;
            if (p > _lastPrice) _pullAsk += pulled; else _pullBid += pulled;
        }

        private void DecayPulls(DateTime now)
        {
            if (_pullStamp != DateTime.MinValue)
            {
                double age = (now - _pullStamp).TotalSeconds;
                if (age > 0)
                {
                    double f = Math.Pow(0.5, age / Math.Max(PullHalfLifeSec, 1));
                    _pullAsk *= f; _pullBid *= f;
                }
            }
            if (now > _pullStamp) _pullStamp = now;
        }

        // =================================================================================
        //  BARS
        // =================================================================================
        protected override void OnBarUpdate()
        {
            if (BarsInProgress == 1)
            {
                if (CurrentBars[0] < 0 || !IsFirstTickOfBar) return;
                RecordTrade(Closes[1][0], Volumes[1][0], Times[1][0]);
                RequestRefresh();
                return;
            }
            if (BarsInProgress != 0) return;

            if (IsFirstTickOfBar && CurrentBar > BarsRequiredToTrade)
            {
                lock (_sync) { ComputeBias(CurrentBar - 1); }

                if (State == State.Realtime)
                {
                    FlushPending(false);
                    if (LogToCsv && _biasValid) QueueRow(CurrentBar - 1);
                    if (ShowPanel) DrawPanel();
                    ManageTrades();
                }
            }
            RequestRefresh();
        }

        private void RecordTrade(double price, double volume, DateTime time)
        {
            if (volume <= 0) return;
            int side;
            bool haveQuote = State == State.Realtime && _liveBid > 0 && _liveAsk > 0;
            if (haveQuote && price >= _liveAsk)      side = 1;
            else if (haveQuote && price <= _liveBid) side = -1;
            else if (price > _lastPrice)             side = 1;
            else if (price < _lastPrice)             side = -1;
            else                                     side = _lastSide;
            _lastPrice     = price;
            _lastSide      = side;
            _lastTradeTime = time;

            int bar = BarsArray[0].GetBar(time);
            if (bar < 0) bar = CurrentBars[0];

            double p = _mi.RoundToTickSize(price);
            lock (_sync)
            {
                Dictionary<double, Level> levels;
                if (!_trades.TryGetValue(bar, out levels)) { levels = new Dictionary<double, Level>(); _trades[bar] = levels; }
                Level lv;
                if (!levels.TryGetValue(p, out lv)) { lv = new Level { Price = p }; levels[p] = lv; }
                if (side > 0) lv.AskVol += volume; else lv.BidVol += volume;
            }
        }

        // =================================================================================
        //  BIAS
        // =================================================================================
        private void ComputeBias(int lastCompleted)
        {
            DateTime now = _lastDepthTime;
            double price = _lastPrice > 0 ? _lastPrice : Closes[0][0];

            // 1. aggression
            double askSum = 0, bidSum = 0;
            for (int b = lastCompleted - AggressionBars + 1; b <= lastCompleted; b++)
            {
                Dictionary<double, Level> levels;
                if (b < 0 || !_trades.TryGetValue(b, out levels)) continue;
                foreach (Level lv in levels.Values) { askSum += lv.AskVol; bidSum += lv.BidVol; }
            }
            _cAggression = Ratio(askSum, bidSum);

            // 2. book lean (persistence-weighted)
            double persistMax = 0;
            foreach (Cluster c in _clusters.Values) persistMax = Math.Max(persistMax, Effective(c, now));
            double bidLean = WeightedSide(_bids, now, persistMax);
            double askLean = WeightedSide(_asks, now, persistMax);
            _cBookLean = Ratio(bidLean, askLean);

            // 3. defence: icebergs by side + absorption of block prints
            double iceBid = 0, iceAsk = 0;
            foreach (KeyValuePair<double, Ice> kv in _ice)
            {
                Ice ice = kv.Value;
                if (ice.Refills < IcebergRefills || (now - ice.Last).TotalSeconds > IcebergWindowSec) continue;
                if (kv.Key < price) iceBid += ice.Refills; else iceAsk += ice.Refills;
            }
            double absorbedBuyers = 0, absorbedSellers = 0, blockAsk = 0, blockBid = 0;
            for (int b = lastCompleted - BlockLookbackBars + 1; b <= lastCompleted; b++)
            {
                Dictionary<double, Level> levels;
                if (b < 0 || !_trades.TryGetValue(b, out levels)) continue;
                foreach (Level lv in levels.Values)
                {
                    if (lv.AskVol >= BlockTradeThreshold)
                    {
                        blockAsk += lv.AskVol;
                        if (price < lv.Price - TickSize * 0.5) absorbedBuyers += lv.AskVol;   // lifted, then lost the level
                    }
                    if (lv.BidVol >= BlockTradeThreshold)
                    {
                        blockBid += lv.BidVol;
                        if (price > lv.Price + TickSize * 0.5) absorbedSellers += lv.BidVol;  // hit, then price came back
                    }
                }
            }
            double iceScore = Ratio(iceBid, iceAsk);
            double absScore = Ratio(absorbedSellers, absorbedBuyers);
            bool haveIce = iceBid + iceAsk > 0, haveAbs = absorbedBuyers + absorbedSellers > 0;
            _cDefence = haveIce && haveAbs ? 0.5 * (iceScore + absScore) : haveIce ? iceScore : haveAbs ? absScore : 0;

            // 4. pulls
            DecayPulls(now);
            _cPulls = Ratio(_pullAsk, _pullBid);

            // 5. blocks
            _cBlocks = Ratio(blockAsk, blockBid);

            double wSum = WeightAggression + WeightBookLean + WeightDefence + WeightPulls + WeightBlocks;
            _bias = wSum > 0
                ? (WeightAggression * _cAggression + WeightBookLean * _cBookLean + WeightDefence * _cDefence
                   + WeightPulls * _cPulls + WeightBlocks * _cBlocks) / wSum
                : 0;

            double[] comps = { _cAggression, _cBookLean, _cDefence, _cPulls, _cBlocks };
            int active = 0, agree = 0;
            foreach (double c in comps)
            {
                if (Math.Abs(c) < 0.1) continue;
                active++;
                if (Math.Sign(c) == Math.Sign(_bias)) agree++;
            }
            _agreement = active > 0 && Math.Abs(_bias) > 0.001 ? (double)agree / active : 0;
            _biasValid = true;

            _clusterText = DescribeClusters(now, persistMax, price);
        }

        private static double Ratio(double plus, double minus)
        {
            double sum = plus + minus;
            return sum <= 0 ? 0 : (plus - minus) / sum;
        }

        private double WeightedSide(List<BookLevel> side, DateTime now, double persistMax)
        {
            double total = 0;
            int n = Math.Min(DomDepth, side.Count);
            for (int i = 0; i < n; i++)
            {
                double p = _mi.RoundToTickSize(side[i].Price);
                Cluster c;
                double persist = _clusters.TryGetValue(p, out c) ? Effective(c, now) : 0;
                double ratio   = persistMax > 0 ? persist / persistMax : 0;
                total += side[i].Volume * (0.5 + 0.5 * ratio);
            }
            return total;
        }

        private string DescribeClusters(DateTime now, double persistMax, double price)
        {
            if (persistMax <= 0) return "clusters : -";
            List<Cluster> top = new List<Cluster>();
            foreach (Cluster c in _clusters.Values)
                if (Effective(c, now) >= 0.25 * persistMax) top.Add(c);
            top.Sort(delegate(Cluster a, Cluster b) { return Effective(b, now).CompareTo(Effective(a, now)); });
            if (top.Count > 3) top.RemoveRange(3, top.Count - 3);

            StringBuilder sb = new StringBuilder();
            foreach (Cluster c in top)
            {
                long size = 0;
                List<BookLevel> side = c.IsBid ? _bids : _asks;
                for (int i = 0; i < Math.Min(DomDepth, side.Count); i++)
                    if (Math.Abs(_mi.RoundToTickSize(side[i].Price) - c.Price) < TickSize * 0.5) size += side[i].Volume;

                Ice ice;
                bool defended = _ice.TryGetValue(c.Price, out ice) && ice.Refills >= IcebergRefills && (now - ice.Last).TotalSeconds <= IcebergWindowSec;
                string status = size == 0 ? "PULLED" : defended ? "DEFENDED" : "untested";
                sb.AppendFormat("\n  {0} {1} {2} {3}", _mi.FormatPrice(c.Price), c.IsBid ? "bid" : "ask", size, status);
            }
            return "clusters :" + (sb.Length == 0 ? " -" : sb.ToString());
        }

        // =================================================================================
        //  LOG
        // =================================================================================
        private void QueueRow(int bar)
        {
            CultureInfo ci = CultureInfo.InvariantCulture;
            string fields = string.Join(",", new string[] {
                Times[0][1].ToString("yyyy-MM-dd HH:mm:ss", ci), _mi.Name, Closes[0][1].ToString(ci),
                _bias.ToString("0.000", ci), _agreement.ToString("0.00", ci),
                _cAggression.ToString("0.000", ci), _cBookLean.ToString("0.000", ci), _cDefence.ToString("0.000", ci),
                _cPulls.ToString("0.000", ci), _cBlocks.ToString("0.000", ci),
                _bids.Count.ToString(ci), _asks.Count.ToString(ci) });
            _pending.Add(new PendingRow { Bar = bar, Time = Times[0][1], Close = Closes[0][1], Fields = fields });
        }

        private void FlushPending(bool force)
        {
            if (_csvPath == null) { _pending.Clear(); return; }
            CultureInfo ci = CultureInfo.InvariantCulture;
            for (int i = _pending.Count - 1; i >= 0; i--)
            {
                PendingRow row = _pending[i];
                int elapsed = CurrentBar - row.Bar;
                if (!force && elapsed < ForwardBars) continue;

                string f5 = Fwd(row, 5, elapsed, ci), f10 = Fwd(row, 10, elapsed, ci), f20 = Fwd(row, 20, elapsed, ci);
                try { System.IO.File.AppendAllText(_csvPath, row.Fields + "," + f5 + "," + f10 + "," + f20 + "\r\n"); } catch { }
                _pending.RemoveAt(i);
            }
        }

        private string Fwd(PendingRow row, int k, int elapsed, CultureInfo ci)
        {
            if (elapsed < k) return "";
            int barsAgo = CurrentBar - (row.Bar + k);
            if (barsAgo < 0 || barsAgo > CurrentBar) return "";
            return ((Closes[0][barsAgo] - row.Close) / TickSize).ToString("0", ci);
        }

        // =================================================================================
        //  TRADING
        // =================================================================================
        private void ManageTrades()
        {
            if (!EnableTrading || !_biasValid) return;

            DateTime t = Times[0][0];
            if (t.Date != _tradeDate) { _tradeDate = t.Date; _tradesToday = 0; }
            int hhmm = t.Hour * 100 + t.Minute;
            bool inWindow = hhmm >= EntryStartHHMM && hhmm < EntryEndHHMM;

            if (Position.MarketPosition == MarketPosition.Long && _bias <= -ExitBias)       { ExitLong("OFB_XL", "OFB_L"); return; }
            if (Position.MarketPosition == MarketPosition.Short && _bias >= ExitBias)       { ExitShort("OFB_XS", "OFB_S"); return; }
            if (Position.MarketPosition != MarketPosition.Flat || !inWindow || _tradesToday >= MaxTradesPerDay) return;
            if (_agreement < MinAgreement) return;

            if (_bias >= EntryBias)       { EnterLong(Contracts, "OFB_L");  _tradesToday++; }
            else if (_bias <= -EntryBias) { EnterShort(Contracts, "OFB_S"); _tradesToday++; }
        }

        // =================================================================================
        //  OUTPUT
        // =================================================================================
        private void DrawPanel()
        {
            string pos = Position.MarketPosition == MarketPosition.Flat ? "FLAT"
                       : string.Format("{0} {1} @ {2}", Position.MarketPosition, Position.Quantity, _mi.FormatPrice(Position.AveragePrice));
            string text = string.Format(CultureInfo.InvariantCulture,
                "ORDER FLOW BIAS  {0}\n" +
                "bias      : {1:+0.00;-0.00;0.00}   agreement {2:0%}\n" +
                "aggression: {3}\n" +
                "book lean : {4}\n" +
                "defence   : {5}\n" +
                "pulls     : {6}\n" +
                "blocks    : {7}\n" +
                "L2        : {8} bid / {9} ask rows{10}\n" +
                "{11}\n" +
                "trading   : {12}  {13}  today {14}/{15}",
                _bias >= EntryBias ? "▲ BUYERS" : _bias <= -EntryBias ? "▼ SELLERS" : "— mixed",
                _bias, _agreement,
                Bar(_cAggression), Bar(_cBookLean), Bar(_cDefence), Bar(_cPulls), Bar(_cBlocks),
                _bids.Count, _asks.Count, _depthEvents == 0 ? " (no depth yet)" : "",
                _clusterText,
                EnableTrading ? "ON" : "off (log only)", pos, _tradesToday, MaxTradesPerDay);

            Draw.TextFixed(this, "OFB_PANEL", text, TextPosition.TopLeft, Brushes.WhiteSmoke,
                           new SimpleFont("Consolas", 11), Brushes.Transparent, Brushes.Black, 70);
        }

        private static string Bar(double v)
        {
            int n = (int)Math.Round(Math.Abs(v) * 10);
            string bar = new string('█', n) + new string('·', 10 - n);
            return string.Format(CultureInfo.InvariantCulture, "{0:+0.00;-0.00;0.00} {1}{2}", v, v < 0 ? "S " : "B ", bar);
        }

        protected override void OnRender(ChartControl chartControl, ChartScale chartScale)
        {
            if (!ShowArrow || !_biasValid || RenderTarget == null || ChartBars == null || ChartBars.Bars == null) return;
            EnsureDx();

            int   lastDataBar = ChartBars.Bars.Count - 1;
            float x0   = chartControl.GetXByBarIndex(ChartBars, lastDataBar);
            float step = (float)chartControl.Properties.BarDistance;
            float x    = x0 + 3 * step;
            double price = _lastPrice > 0 ? _lastPrice : Closes[0][0];
            float yMid = chartScale.GetYByValue(price);

            double bias, agreement;
            lock (_sync) { bias = _bias; agreement = _agreement; }

            float len = (float)(Math.Abs(bias) * ArrowMaxPx);
            if (len < 4) return;
            bool up = bias > 0;
            float yTip  = up ? yMid - len : yMid + len;
            float head  = Math.Min(10f, len * 0.5f);
            float headY = up ? yTip + head : yTip - head;

            SharpDX.Direct2D1.Brush brush = up ? _buyDx : _sellDx;
            brush.Opacity = (float)(0.3 + 0.65 * agreement);
            float w = 2f + 3f * (float)agreement;
            RenderTarget.DrawLine(new SharpDX.Vector2(x, yMid), new SharpDX.Vector2(x, yTip), brush, w);
            RenderTarget.DrawLine(new SharpDX.Vector2(x, yTip), new SharpDX.Vector2(x - head, headY), brush, w);
            RenderTarget.DrawLine(new SharpDX.Vector2(x, yTip), new SharpDX.Vector2(x + head, headY), brush, w);

            string label = string.Format(CultureInfo.InvariantCulture, "{0:+0.00;-0.00} / {1:0%}", bias, agreement);
            SharpDX.DirectWrite.TextFormat tf = chartControl.Properties.LabelFont.ToDirectWriteTextFormat();
            SharpDX.DirectWrite.TextLayout tl = new SharpDX.DirectWrite.TextLayout(Core.Globals.DirectWriteFactory, label, tf, 200f, 20f);
            RenderTarget.DrawTextLayout(new SharpDX.Vector2(x + 8f, yMid - 8f), tl, brush);
            tl.Dispose();
            tf.Dispose();
        }

        private void RequestRefresh()
        {
            if (State != State.Realtime) return;
            DateTime now = DateTime.UtcNow;
            if ((now - _lastRefresh).TotalMilliseconds < 150) return;
            _lastRefresh = now;
            ForceRefresh();
        }

        private void EnsureDx()
        {
            if (_buyDx != null) return;
            _buyDx  = (BuyBrush  ?? Brushes.DeepSkyBlue).ToDxBrush(RenderTarget);
            _sellDx = (SellBrush ?? Brushes.OrangeRed).ToDxBrush(RenderTarget);
        }

        private void ReleaseDx()
        {
            if (_buyDx  != null) { _buyDx.Dispose();  _buyDx  = null; }
            if (_sellDx != null) { _sellDx.Dispose(); _sellDx = null; }
        }

        public override void OnRenderTargetChanged()
        {
            ReleaseDx();
        }

        #region Properties
        // 1. Data
        [Range(1, 50), Display(Name = "DOM depth (rows per side)", GroupName = "1. Data", Order = 1)]
        public int DomDepth { get; set; }
        [Range(5, 1800), Display(Name = "Cluster memory half-life (sec)", GroupName = "1. Data", Order = 2)]
        public int ClusterHalfLifeSec { get; set; }
        [Range(1, 50), Display(Name = "Aggression bars", Description = "Bars of ask-lifted minus bid-hit volume", GroupName = "1. Data", Order = 3)]
        public int AggressionBars { get; set; }
        [Range(1, 100000), Display(Name = "Block trade threshold (contracts)", GroupName = "1. Data", Order = 4)]
        public double BlockTradeThreshold { get; set; }
        [Range(1, 50), Display(Name = "Block look-back (bars)", GroupName = "1. Data", Order = 5)]
        public int BlockLookbackBars { get; set; }
        [Range(1, 100000), Display(Name = "Large order threshold (contracts)", Description = "Row size that counts for icebergs and pulls", GroupName = "1. Data", Order = 6)]
        public int LargeOrderThreshold { get; set; }
        [Range(1, 100), Display(Name = "Iceberg refills needed", GroupName = "1. Data", Order = 7)]
        public int IcebergRefills { get; set; }
        [Range(10, 7200), Display(Name = "Iceberg window (sec)", GroupName = "1. Data", Order = 8)]
        public int IcebergWindowSec { get; set; }
        [Range(5, 3600), Display(Name = "Pull memory half-life (sec)", GroupName = "1. Data", Order = 9)]
        public int PullHalfLifeSec { get; set; }

        // 2. Weights
        [Range(0, 10), Display(Name = "Weight: aggression", GroupName = "2. Weights", Order = 1)]
        public double WeightAggression { get; set; }
        [Range(0, 10), Display(Name = "Weight: book lean", GroupName = "2. Weights", Order = 2)]
        public double WeightBookLean { get; set; }
        [Range(0, 10), Display(Name = "Weight: defence", GroupName = "2. Weights", Order = 3)]
        public double WeightDefence { get; set; }
        [Range(0, 10), Display(Name = "Weight: pulls", GroupName = "2. Weights", Order = 4)]
        public double WeightPulls { get; set; }
        [Range(0, 10), Display(Name = "Weight: blocks", GroupName = "2. Weights", Order = 5)]
        public double WeightBlocks { get; set; }

        // 3. Trading
        [Display(Name = "Enable trading", Description = "Off = compute, draw and log only", GroupName = "3. Trading", Order = 1)]
        public bool EnableTrading { get; set; }
        [Range(1, 1000), Display(Name = "Contracts", GroupName = "3. Trading", Order = 2)]
        public int Contracts { get; set; }
        [Range(0.05, 1.0), Display(Name = "Entry bias (abs)", GroupName = "3. Trading", Order = 3)]
        public double EntryBias { get; set; }
        [Range(0.0, 1.0), Display(Name = "Min agreement", GroupName = "3. Trading", Order = 4)]
        public double MinAgreement { get; set; }
        [Range(0.0, 1.0), Display(Name = "Exit when bias flips past", GroupName = "3. Trading", Order = 5)]
        public double ExitBias { get; set; }
        [Range(1, 1000), Display(Name = "Stop (ticks)", GroupName = "3. Trading", Order = 6)]
        public int StopTicks { get; set; }
        [Range(1, 2000), Display(Name = "Target (ticks)", GroupName = "3. Trading", Order = 7)]
        public int TargetTicks { get; set; }
        [Range(1, 100), Display(Name = "Max trades per day", GroupName = "3. Trading", Order = 8)]
        public int MaxTradesPerDay { get; set; }
        [Range(0, 2359), Display(Name = "Entries from (HHMM, chart time)", GroupName = "3. Trading", Order = 9)]
        public int EntryStartHHMM { get; set; }
        [Range(0, 2359), Display(Name = "Entries until (HHMM, chart time)", GroupName = "3. Trading", Order = 10)]
        public int EntryEndHHMM { get; set; }

        // 4. Output
        [Display(Name = "Show arrow (+3 column)", GroupName = "4. Output", Order = 1)]
        public bool ShowArrow { get; set; }
        [Display(Name = "Show panel", GroupName = "4. Output", Order = 2)]
        public bool ShowPanel { get; set; }
        [Range(10, 400), Display(Name = "Arrow max length (px)", GroupName = "4. Output", Order = 3)]
        public int ArrowMaxPx { get; set; }
        [Display(Name = "Log to CSV", Description = "Documents\\NinjaTrader 8\\OrderFlowBias_<instrument>_<time>.csv, realtime bars only", GroupName = "4. Output", Order = 4)]
        public bool LogToCsv { get; set; }
        [Range(5, 200), Display(Name = "Forward bars logged", Description = "Rows are written once this many bars have passed (needs >= 20 for fwd20)", GroupName = "4. Output", Order = 5)]
        public int ForwardBars { get; set; }

        [XmlIgnore, Display(Name = "Buyers color", GroupName = "4. Output", Order = 6)]
        public Brush BuyBrush { get; set; }
        [Browsable(false)]
        public string BuyBrushSerializable { get { return Serialize.BrushToString(BuyBrush); } set { BuyBrush = Serialize.StringToBrush(value); } }

        [XmlIgnore, Display(Name = "Sellers color", GroupName = "4. Output", Order = 7)]
        public Brush SellBrush { get; set; }
        [Browsable(false)]
        public string SellBrushSerializable { get { return Serialize.BrushToString(SellBrush); } set { SellBrush = Serialize.StringToBrush(value); } }
        #endregion
    }
}
