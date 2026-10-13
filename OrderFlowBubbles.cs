// =====================================================================================
//  OrderFlowBubbles.cs  —  NinjaTrader 8 indicator
//
//  Liquidity map in the space to the RIGHT of the current bar (live Level 2):
//    • Column +1 (just right of the forming bar): every resting order row in the book,
//      asks above price in AskColor, bids below in BidColor.
//        radius  = size of that row compared with the largest row in the book
//        opacity = how long size has been sitting there (clustering), compared with the
//                  most persistent level — fresh orders are faint, stacked ones glow
//      A level whose orders were pulled stays as a fading ring (ghost) so you see where
//      liquidity WAS building.
//    • Column +6: the strongest clusters (largest persistent liquidity), with the current
//      size written next to them and a thin line back to column +1.
//    • Block-trade clusters: prices where at least BlockTradeThreshold contracts traded on
//      one side in the current bar(s), grouped within ClusterRangeTicks, drawn as a band
//      from the current bar across the right margin. Denser cluster = stronger band.
//      Trades come from the live feed, so nothing extra is loaded; only "traded volume on
//      bars" adds a 1-tick history series (slow to load on long charts).
//    • Icebergs: a book row of at least LargeOrderThreshold that gets eaten and refilled
//      IcebergRefills times is marked with a diamond at +1 (hidden size at that price).
//    • Optional: traded volume per price on the bars themselves (off by default).
//
//  Level 2 is live only — NinjaTrader stores no depth history, so nothing is drawn on
//  historical bars. Widen the chart's right margin so six bar-widths fit.
// =====================================================================================

#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Windows.Media;
using System.Xml.Serialization;
using NinjaTrader.Cbi;
using NinjaTrader.Data;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Chart;
using NinjaTrader.NinjaScript;
#endregion

namespace NinjaTrader.NinjaScript.Indicators
{
    public class OrderFlowBubbles : Indicator
    {
        #region Private types
        private class BookLevel { public double Price; public long Volume; }

        // how much size has been resting at a price (contracts x seconds, decaying)
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

        private struct Row { public long Size; public bool IsBid; }

        private class BlockCluster
        {
            public double Price, Top, Bottom, Volume;
            public int    Intensity;
        }

        // refill tracking for one book price: eaten (size collapses) then restored = one refill
        private class Ice
        {
            public long     Peak;
            public bool     Dropped;
            public int      Refills;
            public DateTime Last;
        }
        #endregion

        #region Fields
        private readonly List<BookLevel> _bids = new List<BookLevel>();
        private readonly List<BookLevel> _asks = new List<BookLevel>();
        private readonly Dictionary<double, Cluster> _clusters = new Dictionary<double, Cluster>();
        private readonly Dictionary<int, Dictionary<double, Level>> _trades = new Dictionary<int, Dictionary<double, Level>>();
        private readonly Dictionary<double, Ice> _ice = new Dictionary<double, Ice>();

        private int      _depthEvents;
        private DateTime _lastDepthTime = DateTime.MinValue;
        private DateTime _lastCleanup   = DateTime.MinValue;
        private const double MaxGapSeconds = 5.0;   // a quiet spell (reconnect) never counts as more

        // data thread (OnBarUpdate / OnMarketDepth) and UI thread (OnRender) share the above
        private readonly object _sync = new object();

        private MasterInstrument _mi;
        private double   _lastPrice, _liveBid, _liveAsk;
        private int      _lastSide = 1;
        private DateTime _lastRefresh = DateTime.MinValue;

        private SharpDX.Direct2D1.Brush _bidDx, _askDx, _blockDx, _iceDx;
        #endregion

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description              = "Live Level 2 liquidity map drawn to the right of the current bar: resting orders above/below price as bubbles that grow and brighten as they cluster, strongest clusters marked 6 bars ahead.";
                Name                     = "OrderFlowBubbles";
                Calculate                = Calculate.OnEachTick;
                IsOverlay                = true;
                DisplayInDataBox         = false;
                DrawOnPricePanel         = true;
                PaintPriceMarkers        = false;
                IsAutoScale              = false;
                IsSuspendedWhileInactive = false;

                DomDepth           = 10;
                ClusterHalfLifeSec = 60;
                TopClusters        = 3;

                MaxBubbleRadius    = 18;
                MinBubbleRadius    = 3;
                MinOpacity         = 0.20;
                MaxOpacity         = 0.95;
                ShowGhosts         = true;
                ShowTradeBubbles   = false;
                ShowStatus         = true;

                ShowBlockClusters   = true;
                BlockTradeThreshold = 50;
                ClusterRangeTicks   = 4;
                BlockLookbackBars   = 1;

                ShowIcebergs        = true;
                LargeOrderThreshold = 100;
                IcebergRefills      = 5;
                IcebergWindowSec    = 300;

                BidBrush           = Brushes.DeepSkyBlue;
                AskBrush           = Brushes.OrangeRed;
                BlockBrush         = Brushes.Gold;
                IcebergBrush       = Brushes.Red;
            }
            else if (State == State.Configure)
            {
                // only the on-bar history view needs a tick series; everything else is fed live
                if (ShowTradeBubbles) AddDataSeries(BarsPeriodType.Tick, 1);
            }
            else if (State == State.DataLoaded)
            {
                _mi = Instrument.MasterInstrument;
            }
            else if (State == State.Terminated)
            {
                ReleaseDx();
            }
        }

        // =================================================================================
        //  LEVEL 2
        // =================================================================================
        protected override void OnMarketData(MarketDataEventArgs e)
        {
            if (e.MarketDataType == MarketDataType.Bid)      _liveBid = e.Price;
            else if (e.MarketDataType == MarketDataType.Ask) _liveAsk = e.Price;
            else if (e.MarketDataType == MarketDataType.Last && !ShowTradeBubbles && State == State.Realtime)
            {
                RecordTrade(e.Price, e.Volume, e.Time, e.Bid, e.Ask);
                RequestRefresh();
            }
        }

        protected override void OnMarketDepth(MarketDepthEventArgs e)
        {
            lock (_sync)
            {
                // credit the book as it stood up to this event, before changing it
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
                    if (ShowIcebergs) TrackIceberg(e.Price, e.Volume, e.Time);
                }
                else if (e.Operation == Operation.Update)
                {
                    if (e.Position < side.Count) { side[e.Position].Price = e.Price; side[e.Position].Volume = e.Volume; }
                    if (ShowIcebergs) TrackIceberg(e.Price, e.Volume, e.Time);
                }
                else if (e.Operation == Operation.Remove)
                {
                    if (e.Position < side.Count)
                    {
                        double removed = side[e.Position].Price;
                        side.RemoveAt(e.Position);
                        if (ShowIcebergs) TrackIceberg(removed, 0, e.Time);
                    }
                }
            }
            RequestRefresh();
        }

        private void TrackIceberg(double price, long size, DateTime now)
        {
            double p = _mi.RoundToTickSize(price);
            Ice ice;
            if (!_ice.TryGetValue(p, out ice))
            {
                if (size < LargeOrderThreshold) return;
                ice = new Ice { Peak = size, Last = now };
                _ice[p] = ice;
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

        // persistence decays with the configured half-life
        private double Effective(Cluster c, DateTime now)
        {
            double age = (now - c.Stamp).TotalSeconds;
            if (age <= 0) return c.Persist;
            return c.Persist * Math.Pow(0.5, age / Math.Max(ClusterHalfLifeSec, 1));
        }

        // =================================================================================
        //  TRADES (optional bubbles on the bars)
        // =================================================================================
        protected override void OnBarUpdate()
        {
            if (BarsInProgress == 1)
            {
                if (CurrentBars[0] < 0 || !IsFirstTickOfBar) return;
                bool live = State == State.Realtime;
                RecordTrade(Closes[1][0], Volumes[1][0], Times[1][0], live ? _liveBid : 0, live ? _liveAsk : 0);
                RequestRefresh();
                return;
            }
            if (BarsInProgress == 0) RequestRefresh();
        }

        // bid/ask = the quote at trade time when known (live); 0 = unknown, fall back to the tick rule
        private void RecordTrade(double price, double volume, DateTime time, double bid, double ask)
        {
            if (volume <= 0) return;

            int side;
            bool haveQuote = bid > 0 && ask > 0;
            if (haveQuote && price >= ask)      side = 1;
            else if (haveQuote && price <= bid) side = -1;
            else if (price > _lastPrice)             side = 1;
            else if (price < _lastPrice)             side = -1;
            else                                     side = _lastSide;
            _lastPrice = price;
            _lastSide  = side;

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

        private void RequestRefresh()
        {
            if (State != State.Realtime) return;
            DateTime now = DateTime.UtcNow;
            if ((now - _lastRefresh).TotalMilliseconds < 150) return;
            _lastRefresh = now;
            ForceRefresh();
        }

        // =================================================================================
        //  RENDER
        // =================================================================================
        protected override void OnRender(ChartControl chartControl, ChartScale chartScale)
        {
            if (RenderTarget == null || ChartBars == null || ChartBars.Bars == null) return;
            EnsureDx();

            int   lastDataBar = ChartBars.Bars.Count - 1;
            float x0          = chartControl.GetXByBarIndex(ChartBars, lastDataBar);
            float step        = (float)chartControl.Properties.BarDistance;
            float xRightEdge  = ChartPanel.X + ChartPanel.W;
            int   colsThatFit = step > 0 ? (int)Math.Floor((xRightEdge - x0) / step) : 0;

            lock (_sync)
            {
                if (ShowTradeBubbles) DrawTradeBubbles(chartControl, chartScale);

                DateTime now = _lastDepthTime;

                List<BlockCluster> blocks = ShowBlockClusters ? FindBlockClusters(lastDataBar) : new List<BlockCluster>();
                if (blocks.Count > 0) DrawBlockClusters(chartControl, chartScale, blocks, x0, step);

                // current rows (top DomDepth per side)
                Dictionary<double, Row> rows = new Dictionary<double, Row>();
                long sizeMax = 0;
                for (int i = 0; i < Math.Min(DomDepth, _bids.Count); i++) AddRow(rows, _bids[i], true,  ref sizeMax);
                for (int i = 0; i < Math.Min(DomDepth, _asks.Count); i++) AddRow(rows, _asks[i], false, ref sizeMax);

                double persistMax = 0;
                foreach (Cluster c in _clusters.Values) persistMax = Math.Max(persistMax, Effective(c, now));

                // ---- column +1: the book now, brightness = how long it has been there ----
                float x1 = x0 + step;
                foreach (KeyValuePair<double, Row> kv in rows)
                {
                    Cluster c;
                    double persist = _clusters.TryGetValue(kv.Key, out c) ? Effective(c, now) : 0;
                    double sizeRatio    = sizeMax > 0 ? (double)kv.Value.Size / sizeMax : 0;
                    double persistRatio = persistMax > 0 ? persist / persistMax : 0;

                    SharpDX.Direct2D1.Brush brush = kv.Value.IsBid ? _bidDx : _askDx;
                    float radius  = (float)(MinBubbleRadius + sizeRatio * (MaxBubbleRadius - MinBubbleRadius));
                    brush.Opacity = (float)(MinOpacity + persistRatio * (MaxOpacity - MinOpacity));
                    float y = chartScale.GetYByValue(kv.Key);
                    RenderTarget.FillEllipse(new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(x1, y), radius, radius), brush);
                }

                // ghosts: liquidity that was clustering here but has been pulled
                if (ShowGhosts && persistMax > 0)
                {
                    foreach (Cluster c in _clusters.Values)
                    {
                        if (rows.ContainsKey(c.Price)) continue;
                        double persistRatio = Effective(c, now) / persistMax;
                        if (persistRatio < 0.15) continue;
                        SharpDX.Direct2D1.Brush brush = c.IsBid ? _bidDx : _askDx;
                        float radius  = (float)(MinBubbleRadius + persistRatio * (MaxBubbleRadius - MinBubbleRadius) * 0.5);
                        brush.Opacity = (float)(MinOpacity + persistRatio * (MaxOpacity - MinOpacity)) * 0.5f;
                        float y = chartScale.GetYByValue(c.Price);
                        RenderTarget.DrawEllipse(new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(x1, y), radius, radius), brush, 1.0f);
                    }
                }

                // ---- column +6: strongest clusters ----
                List<Cluster> top = TopByPersistence(now, persistMax);
                float x6 = x0 + 6 * step;
                foreach (Cluster c in top)
                {
                    double persistRatio = Effective(c, now) / persistMax;
                    SharpDX.Direct2D1.Brush brush = c.IsBid ? _bidDx : _askDx;
                    float y      = chartScale.GetYByValue(c.Price);
                    float radius = (float)(MinBubbleRadius + persistRatio * (MaxBubbleRadius - MinBubbleRadius));

                    brush.Opacity = 0.30f;
                    RenderTarget.DrawLine(new SharpDX.Vector2(x1, y), new SharpDX.Vector2(x6, y), brush, 1.0f);

                    brush.Opacity = (float)MaxOpacity;
                    RenderTarget.FillEllipse(new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(x6, y), radius, radius), brush);

                    Row r;
                    string label = rows.TryGetValue(c.Price, out r) ? r.Size.ToString() : "pulled";
                    DrawText(chartControl, label, x6 + radius + 4f, y - 8f, brush);
                }

                int icebergs = ShowIcebergs ? DrawIcebergs(chartScale, chartControl, x1, now) : 0;

                if (ShowStatus) DrawStatus(chartControl, rows.Count, top, rows, colsThatFit, blocks.Count, icebergs);
            }
        }

        // ---- block-trade clusters: big one-sided prints in the last bar(s), grouped by price ----
        private List<BlockCluster> FindBlockClusters(int lastDataBar)
        {
            Dictionary<double, Level> sum = new Dictionary<double, Level>();
            for (int b = lastDataBar - BlockLookbackBars + 1; b <= lastDataBar; b++)
            {
                Dictionary<double, Level> levels;
                if (b < 0 || !_trades.TryGetValue(b, out levels)) continue;
                foreach (Level lv in levels.Values)
                {
                    Level s;
                    if (!sum.TryGetValue(lv.Price, out s)) { s = new Level { Price = lv.Price }; sum[lv.Price] = s; }
                    s.BidVol += lv.BidVol;
                    s.AskVol += lv.AskVol;
                }
            }

            List<Level> blocks = new List<Level>();
            foreach (Level s in sum.Values)
                if (s.BidVol >= BlockTradeThreshold || s.AskVol >= BlockTradeThreshold) blocks.Add(s);
            blocks.Sort(delegate(Level a, Level b) { return b.Price.CompareTo(a.Price); });

            double range = ClusterRangeTicks * TickSize;
            List<BlockCluster> result = new List<BlockCluster>();
            List<Level> remaining = new List<Level>(blocks);
            while (remaining.Count > 0)
            {
                double anchor = remaining[0].Price;
                double priceSum = 0, volume = 0, top = double.MinValue, bottom = double.MaxValue;
                int n = 0;
                for (int i = remaining.Count - 1; i >= 0; i--)
                {
                    Level lv = remaining[i];
                    if (Math.Abs(lv.Price - anchor) > range) continue;
                    priceSum += lv.Price; volume += lv.Total; n++;
                    top = Math.Max(top, lv.Price); bottom = Math.Min(bottom, lv.Price);
                    remaining.RemoveAt(i);
                }
                BlockCluster c = new BlockCluster { Price = priceSum / n, Top = top, Bottom = bottom, Volume = volume };
                foreach (Level lv in blocks) if (Math.Abs(lv.Price - c.Price) <= range) c.Intensity++;
                result.Add(c);
            }
            return result;
        }

        private void DrawBlockClusters(ChartControl chartControl, ChartScale chartScale, List<BlockCluster> blocks, float x0, float step)
        {
            int maxIntensity = 1;
            foreach (BlockCluster c in blocks) maxIntensity = Math.Max(maxIntensity, c.Intensity);

            float xLeft  = x0 - step * 0.5f;
            float xRight = x0 + 6.5f * step;
            foreach (BlockCluster c in blocks)
            {
                float yTop    = chartScale.GetYByValue(c.Top    + 0.4 * TickSize);
                float yBottom = chartScale.GetYByValue(c.Bottom - 0.4 * TickSize);
                double ratio  = (double)c.Intensity / maxIntensity;

                _blockDx.Opacity = (float)(0.10 + 0.35 * ratio);
                RenderTarget.FillRectangle(new SharpDX.RectangleF(xLeft, yTop, xRight - xLeft, yBottom - yTop), _blockDx);
                _blockDx.Opacity = 0.9f;
                DrawText(chartControl, string.Format("{0:0} x{1}", c.Volume, c.Intensity), xRight + 4f, (yTop + yBottom) * 0.5f - 8f, _blockDx);
            }
        }

        private int DrawIcebergs(ChartScale chartScale, ChartControl chartControl, float x1, DateTime now)
        {
            int count = 0;
            float r = (float)(MaxBubbleRadius * 0.8);
            foreach (KeyValuePair<double, Ice> kv in _ice)
            {
                Ice ice = kv.Value;
                if (ice.Refills < IcebergRefills || (now - ice.Last).TotalSeconds > IcebergWindowSec) continue;
                count++;
                float y = chartScale.GetYByValue(kv.Key);
                _iceDx.Opacity = 0.95f;
                RenderTarget.DrawLine(new SharpDX.Vector2(x1, y - r), new SharpDX.Vector2(x1 + r, y), _iceDx, 2f);
                RenderTarget.DrawLine(new SharpDX.Vector2(x1 + r, y), new SharpDX.Vector2(x1, y + r), _iceDx, 2f);
                RenderTarget.DrawLine(new SharpDX.Vector2(x1, y + r), new SharpDX.Vector2(x1 - r, y), _iceDx, 2f);
                RenderTarget.DrawLine(new SharpDX.Vector2(x1 - r, y), new SharpDX.Vector2(x1, y - r), _iceDx, 2f);
                DrawText(chartControl, "ICE x" + ice.Refills, x1 + r + 4f, y - 8f, _iceDx);
            }
            return count;
        }

        private void AddRow(Dictionary<double, Row> rows, BookLevel b, bool isBid, ref long sizeMax)
        {
            if (b.Volume <= 0) return;
            double p = _mi.RoundToTickSize(b.Price);
            Row r;
            rows.TryGetValue(p, out r);
            r.Size += b.Volume;
            r.IsBid = isBid;
            rows[p] = r;
            if (r.Size > sizeMax) sizeMax = r.Size;
        }

        private List<Cluster> TopByPersistence(DateTime now, double persistMax)
        {
            List<Cluster> all = new List<Cluster>();
            if (persistMax <= 0) return all;
            foreach (Cluster c in _clusters.Values)
                if (Effective(c, now) >= 0.25 * persistMax) all.Add(c);
            all.Sort(delegate(Cluster a, Cluster b) { return Effective(b, now).CompareTo(Effective(a, now)); });
            if (all.Count > TopClusters) all.RemoveRange(TopClusters, all.Count - TopClusters);
            return all;
        }

        private void DrawTradeBubbles(ChartControl chartControl, ChartScale chartScale)
        {
            int first = ChartBars.FromIndex, last = ChartBars.ToIndex;

            double visibleMax = 0;
            for (int b = first; b <= last; b++)
            {
                Dictionary<double, Level> levels;
                if (!_trades.TryGetValue(b, out levels)) continue;
                foreach (Level lv in levels.Values) visibleMax = Math.Max(visibleMax, lv.Total);
            }

            for (int b = first; b <= last; b++)
            {
                Dictionary<double, Level> levels;
                if (!_trades.TryGetValue(b, out levels) || levels.Count == 0) continue;

                double barMax = 0;
                foreach (Level lv in levels.Values) barMax = Math.Max(barMax, lv.Total);
                if (barMax <= 0) continue;

                float x = chartControl.GetXByBarIndex(ChartBars, b);
                foreach (Level lv in levels.Values)
                {
                    float  y         = chartScale.GetYByValue(lv.Price);
                    double sizeRatio = lv.Total / barMax;
                    double heatRatio = visibleMax > 0 ? lv.Total / visibleMax : sizeRatio;
                    float  radius    = (float)(MinBubbleRadius + sizeRatio * (MaxBubbleRadius - MinBubbleRadius));
                    SharpDX.Direct2D1.Brush brush = lv.BidVol > lv.AskVol ? _bidDx : _askDx;
                    brush.Opacity = (float)(MinOpacity + heatRatio * (MaxOpacity - MinOpacity));
                    RenderTarget.FillEllipse(new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(x, y), radius, radius), brush);
                }
            }
        }

        private void DrawStatus(ChartControl chartControl, int rowCount, List<Cluster> top, Dictionary<double, Row> rows, int colsThatFit, int blockClusters, int icebergs)
        {
            string l2 = _depthEvents == 0
                ? "L2: nothing received yet (needs a live connection with Level 2)"
                : string.Format("L2: {0} bid / {1} ask rows, last update {2:HH:mm:ss}", _bids.Count, _asks.Count, _lastDepthTime);

            string strongest = "-";
            if (top.Count > 0)
            {
                Row r;
                strongest = string.Format("{0} ({1} {2})", _mi.FormatPrice(top[0].Price), top[0].IsBid ? "bid" : "ask",
                                          rows.TryGetValue(top[0].Price, out r) ? r.Size.ToString() : "pulled");
            }
            string margin = colsThatFit >= 6 ? "" : string.Format("  |  right margin fits {0}/6 columns - widen it", Math.Max(colsThatFit, 0));

            string text = string.Format("OrderFlowBubbles  |  {0}  |  {1}  |  levels tracked: {2}  |  strongest cluster: {3}  |  block clusters: {4}  |  icebergs: {5}{6}",
                                        State, l2, _clusters.Count, strongest, blockClusters, icebergs, margin);

            // bottom-right: bottom-left and top-right are where other indicators put their panels
            SharpDX.Direct2D1.Brush textBrush = chartControl.Properties.ChartText.ToDxBrush(RenderTarget);
            DrawText(chartControl, text, ChartPanel.X + ChartPanel.W - 10f, ChartPanel.Y + ChartPanel.H - 24f, textBrush, true);
            textBrush.Dispose();
        }

        private void DrawText(ChartControl chartControl, string text, float x, float y, SharpDX.Direct2D1.Brush brush)
        {
            DrawText(chartControl, text, x, y, brush, false);
        }

        private void DrawText(ChartControl chartControl, string text, float x, float y, SharpDX.Direct2D1.Brush brush, bool rightAlign)
        {
            SharpDX.DirectWrite.TextFormat tf = chartControl.Properties.LabelFont.ToDirectWriteTextFormat();
            SharpDX.DirectWrite.TextLayout tl = new SharpDX.DirectWrite.TextLayout(Core.Globals.DirectWriteFactory, text, tf, 1600f, 24f);
            if (rightAlign) x -= tl.Metrics.Width;
            RenderTarget.DrawTextLayout(new SharpDX.Vector2(x, y), tl, brush);
            tl.Dispose();
            tf.Dispose();
        }

        private void EnsureDx()
        {
            if (_bidDx != null) return;
            _bidDx   = (BidBrush     ?? Brushes.DeepSkyBlue).ToDxBrush(RenderTarget);
            _askDx   = (AskBrush     ?? Brushes.OrangeRed).ToDxBrush(RenderTarget);
            _blockDx = (BlockBrush   ?? Brushes.Gold).ToDxBrush(RenderTarget);
            _iceDx   = (IcebergBrush ?? Brushes.Red).ToDxBrush(RenderTarget);
        }

        private void ReleaseDx()
        {
            if (_bidDx   != null) { _bidDx.Dispose();   _bidDx   = null; }
            if (_askDx   != null) { _askDx.Dispose();   _askDx   = null; }
            if (_blockDx != null) { _blockDx.Dispose(); _blockDx = null; }
            if (_iceDx   != null) { _iceDx.Dispose();   _iceDx   = null; }
        }

        public override void OnRenderTargetChanged()
        {
            ReleaseDx();
        }

        #region Properties
        // 1. Level 2
        [Range(1, 50), Display(Name = "DOM depth (rows per side)", Description = "Book rows per side shown in the +1 column", GroupName = "1. Level 2", Order = 1)]
        public int DomDepth { get; set; }
        [Range(5, 1800), Display(Name = "Cluster memory half-life (sec)", Description = "How fast a level forgets size that sat there. Shorter = reacts faster, longer = steadier clusters", GroupName = "1. Level 2", Order = 2)]
        public int ClusterHalfLifeSec { get; set; }
        [Range(1, 10), Display(Name = "Clusters shown at +6", GroupName = "1. Level 2", Order = 3)]
        public int TopClusters { get; set; }

        // 2. Bubbles
        [Range(1, 80), Display(Name = "Max bubble radius (px)", GroupName = "2. Bubbles", Order = 1)]
        public int MaxBubbleRadius { get; set; }
        [Range(1, 80), Display(Name = "Min bubble radius (px)", GroupName = "2. Bubbles", Order = 2)]
        public int MinBubbleRadius { get; set; }
        [Range(0.05, 1.0), Display(Name = "Min opacity", Description = "Opacity of a brand-new order", GroupName = "2. Bubbles", Order = 3)]
        public double MinOpacity { get; set; }
        [Range(0.05, 1.0), Display(Name = "Max opacity", Description = "Opacity of the most persistent level", GroupName = "2. Bubbles", Order = 4)]
        public double MaxOpacity { get; set; }
        [Display(Name = "Show pulled-order ghosts", Description = "Fading rings where orders were clustering but have been pulled", GroupName = "2. Bubbles", Order = 5)]
        public bool ShowGhosts { get; set; }
        [Display(Name = "Show traded volume on bars", Description = "Also plot bid/ask traded volume per price on each bar. Loads 1-tick history for the whole chart - slow on long charts, and the chart looks frozen while it loads", GroupName = "2. Bubbles", Order = 6)]
        public bool ShowTradeBubbles { get; set; }
        [Display(Name = "Show status line", GroupName = "2. Bubbles", Order = 7)]
        public bool ShowStatus { get; set; }

        // 3. Colors
        [XmlIgnore, Display(Name = "Bid color", Description = "Resting buy orders (below price)", GroupName = "3. Colors", Order = 1)]
        public Brush BidBrush { get; set; }
        [Browsable(false)]
        public string BidBrushSerializable { get { return Serialize.BrushToString(BidBrush); } set { BidBrush = Serialize.StringToBrush(value); } }

        [XmlIgnore, Display(Name = "Ask color", Description = "Resting sell orders (above price)", GroupName = "3. Colors", Order = 2)]
        public Brush AskBrush { get; set; }
        [Browsable(false)]
        public string AskBrushSerializable { get { return Serialize.BrushToString(AskBrush); } set { AskBrush = Serialize.StringToBrush(value); } }

        [XmlIgnore, Display(Name = "Block cluster color", GroupName = "3. Colors", Order = 3)]
        public Brush BlockBrush { get; set; }
        [Browsable(false)]
        public string BlockBrushSerializable { get { return Serialize.BrushToString(BlockBrush); } set { BlockBrush = Serialize.StringToBrush(value); } }

        [XmlIgnore, Display(Name = "Iceberg color", GroupName = "3. Colors", Order = 4)]
        public Brush IcebergBrush { get; set; }
        [Browsable(false)]
        public string IcebergBrushSerializable { get { return Serialize.BrushToString(IcebergBrush); } set { IcebergBrush = Serialize.StringToBrush(value); } }

        // 4. Block trades
        [Display(Name = "Show block-trade clusters", Description = "Bands across the right margin where large one-sided prints clustered", GroupName = "4. Block trades", Order = 1)]
        public bool ShowBlockClusters { get; set; }
        [Range(1, 100000), Display(Name = "Block trade threshold (contracts)", Description = "Traded at bid OR at ask on one price to count as a block level", GroupName = "4. Block trades", Order = 2)]
        public double BlockTradeThreshold { get; set; }
        [Range(1, 100), Display(Name = "Cluster range (ticks)", Description = "Block levels this close together form one cluster", GroupName = "4. Block trades", Order = 3)]
        public double ClusterRangeTicks { get; set; }
        [Range(1, 50), Display(Name = "Bars included", Description = "1 = current bar only", GroupName = "4. Block trades", Order = 4)]
        public int BlockLookbackBars { get; set; }

        // 5. Icebergs
        [Display(Name = "Show icebergs", Description = "Diamond at +1 where a large book row keeps getting eaten and refilled", GroupName = "5. Icebergs", Order = 1)]
        public bool ShowIcebergs { get; set; }
        [Range(1, 100000), Display(Name = "Large order threshold (contracts)", GroupName = "5. Icebergs", Order = 2)]
        public int LargeOrderThreshold { get; set; }
        [Range(1, 100), Display(Name = "Refills needed", Description = "Times the row must collapse and come back", GroupName = "5. Icebergs", Order = 3)]
        public int IcebergRefills { get; set; }
        [Range(10, 7200), Display(Name = "Iceberg window (sec)", Description = "Refills older than this are forgotten", GroupName = "5. Icebergs", Order = 4)]
        public int IcebergWindowSec { get; set; }
        #endregion
    }
}

#region NinjaScript generated code. Neither change nor remove.

namespace NinjaTrader.NinjaScript.Indicators
{
	public partial class Indicator : NinjaTrader.Gui.NinjaScript.IndicatorRenderBase
	{
		private OrderFlowBubbles[] cacheOrderFlowBubbles;
		public OrderFlowBubbles OrderFlowBubbles()
		{
			return OrderFlowBubbles(Input);
		}

		public OrderFlowBubbles OrderFlowBubbles(ISeries<double> input)
		{
			if (cacheOrderFlowBubbles != null)
				for (int idx = 0; idx < cacheOrderFlowBubbles.Length; idx++)
					if (cacheOrderFlowBubbles[idx] != null &&  cacheOrderFlowBubbles[idx].EqualsInput(input))
						return cacheOrderFlowBubbles[idx];
			return CacheIndicator<OrderFlowBubbles>(new OrderFlowBubbles(), input, ref cacheOrderFlowBubbles);
		}
	}
}

namespace NinjaTrader.NinjaScript.MarketAnalyzerColumns
{
	public partial class MarketAnalyzerColumn : MarketAnalyzerColumnBase
	{
		public Indicators.OrderFlowBubbles OrderFlowBubbles()
		{
			return indicator.OrderFlowBubbles(Input);
		}

		public Indicators.OrderFlowBubbles OrderFlowBubbles(ISeries<double> input )
		{
			return indicator.OrderFlowBubbles(input);
		}
	}
}

namespace NinjaTrader.NinjaScript.Strategies
{
	public partial class Strategy : NinjaTrader.Gui.NinjaScript.StrategyRenderBase
	{
		public Indicators.OrderFlowBubbles OrderFlowBubbles()
		{
			return indicator.OrderFlowBubbles(Input);
		}

		public Indicators.OrderFlowBubbles OrderFlowBubbles(ISeries<double> input )
		{
			return indicator.OrderFlowBubbles(input);
		}
	}
}

#endregion
