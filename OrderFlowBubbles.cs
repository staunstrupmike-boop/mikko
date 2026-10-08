// =====================================================================================
//  OrderFlowBubbles.cs  —  NinjaTrader 8 indicator
//
//  Order-flow bubbles on a NORMAL candle chart:
//    • Filled bubble at every price where contracts TRADED in that bar (from a hidden
//      1-tick series, so history is filled in). Bid-side trades in BidColor, ask-side in
//      AskColor. Radius = share of the bar's volume at that price; opacity = that volume
//      compared with the heaviest level on screen. Big and bright = cluster.
//    • Rings on the forming bar for orders RESTING in the Level 2 book (live only — NT
//      stores no depth history). Ring radius/opacity = size relative to the largest row.
//    • "+6" marker 6 bars to the right: the price that has attracted the most volume over
//      the last ClusterLookback bars, recency weighted.
//    • Status line (bottom-left) shows what data the indicator is receiving.
//
//  Colors are standard NinjaTrader brush pickers under "3. Colors".
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
        private class Level
        {
            public double Price;
            public double BidVol;
            public double AskVol;
            public double Total { get { return BidVol + AskVol; } }
        }

        private class BookLevel { public double Price; public long Volume; }
        #endregion

        #region Fields
        // traded volume: primary bar index -> price -> level
        private readonly Dictionary<int, Dictionary<double, Level>> _trades = new Dictionary<int, Dictionary<double, Level>>();

        // Level 2 book, position-ordered (depth events address rows by Position)
        private readonly List<BookLevel> _bids = new List<BookLevel>();
        private readonly List<BookLevel> _asks = new List<BookLevel>();
        private int      _depthEvents;
        private DateTime _lastDepthTime = DateTime.MinValue;

        // data thread (OnBarUpdate / OnMarketDepth) and UI thread (OnRender) share the above
        private readonly object _sync = new object();

        private MasterInstrument _mi;
        private double _lastPrice, _liveBid, _liveAsk;
        private int    _lastSide = 1;
        private DateTime _lastRefresh = DateTime.MinValue;

        private double _projectedPrice, _projectedStrength;
        private bool   _projectionValid;

        private SharpDX.Direct2D1.Brush _bidDx, _askDx, _projDx;
        #endregion

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description              = "Order-flow bubbles: traded volume per price on every bar, live Level 2 rings on the forming bar, +6 bar cluster projection.";
                Name                     = "OrderFlowBubbles";
                Calculate                = Calculate.OnEachTick;
                IsOverlay                = true;
                DisplayInDataBox         = false;
                DrawOnPricePanel         = true;
                PaintPriceMarkers        = false;
                IsAutoScale              = false;
                IsSuspendedWhileInactive = false;

                DomDepth        = 10;
                ClusterLookback = 10;

                MaxBubbleRadius = 18;
                MinBubbleRadius = 3;
                MinOpacity      = 0.25;
                MaxOpacity      = 0.90;
                ShowDomRings    = true;
                DomRingWidth    = 2.0;
                ShowProjection  = true;
                ShowStatus      = true;

                BidBrush        = Brushes.DeepSkyBlue;
                AskBrush        = Brushes.OrangeRed;
                ProjectionBrush = Brushes.Gold;
            }
            else if (State == State.Configure)
            {
                AddDataSeries(BarsPeriodType.Tick, 1);
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
        //  DATA
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
                _depthEvents++;
                _lastDepthTime = e.Time;

                if (e.IsReset) { _bids.Clear(); _asks.Clear(); return; }

                List<BookLevel> side = e.MarketDataType == MarketDataType.Bid ? _bids
                                     : e.MarketDataType == MarketDataType.Ask ? _asks
                                     : null;
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
            RequestRefresh();
        }

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

            if (IsFirstTickOfBar && CurrentBar > 0)
                lock (_sync) { UpdateClusterProjection(CurrentBar - 1); }

            RequestRefresh();
        }

        private void RecordTrade(double price, double volume, DateTime time)
        {
            if (volume <= 0) return;

            // live: classify against the quote; history (no quotes stored): tick rule
            int side;
            bool haveQuote = State == State.Realtime && _liveBid > 0 && _liveAsk > 0;
            if (haveQuote && price >= _liveAsk)      side = 1;
            else if (haveQuote && price <= _liveBid) side = -1;
            else if (price > _lastPrice)             side = 1;
            else if (price < _lastPrice)             side = -1;
            else                                     side = _lastSide;
            _lastPrice = price;
            _lastSide  = side;

            // the primary bar this tick falls into; CurrentBars[0] lags by one bar in history
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

        // Price with the largest recency-weighted share of volume over the look-back
        private void UpdateClusterProjection(int lastCompleted)
        {
            Dictionary<double, double> score = new Dictionary<double, double>();
            double recencySum = 0;

            for (int i = 0; i < ClusterLookback; i++)
            {
                int bar = lastCompleted - i;
                Dictionary<double, Level> levels;
                if (bar < 0 || !_trades.TryGetValue(bar, out levels)) continue;

                double barTotal = 0;
                foreach (Level lv in levels.Values) barTotal += lv.Total;
                if (barTotal <= 0) continue;

                double recency = (double)(ClusterLookback - i) / ClusterLookback;
                recencySum += recency;
                foreach (Level lv in levels.Values)
                {
                    double s;
                    score.TryGetValue(lv.Price, out s);
                    score[lv.Price] = s + recency * lv.Total / barTotal;
                }
            }

            double bestPrice = 0, best = 0;
            foreach (KeyValuePair<double, double> kv in score)
                if (kv.Value > best) { best = kv.Value; bestPrice = kv.Key; }

            if (best <= 0 || recencySum <= 0) { _projectionValid = false; return; }
            _projectedPrice    = bestPrice;
            _projectedStrength = Math.Min(1.0, 4.0 * best / recencySum);   // 25% share = full size
            _projectionValid   = true;
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

            int first       = ChartBars.FromIndex;
            int last        = ChartBars.ToIndex;
            int lastDataBar = ChartBars.Bars.Count - 1;
            int barsWithTrades = 0;

            lock (_sync)
            {
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
                    barsWithTrades++;

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

                if (ShowDomRings && (_bids.Count > 0 || _asks.Count > 0))
                {
                    long bookMax = 0;
                    for (int i = 0; i < Math.Min(DomDepth, _bids.Count); i++) bookMax = Math.Max(bookMax, _bids[i].Volume);
                    for (int i = 0; i < Math.Min(DomDepth, _asks.Count); i++) bookMax = Math.Max(bookMax, _asks[i].Volume);
                    if (bookMax > 0)
                    {
                        float x = chartControl.GetXByBarIndex(ChartBars, lastDataBar);
                        DrawRings(_bids, _bidDx, x, chartScale, bookMax);
                        DrawRings(_asks, _askDx, x, chartScale, bookMax);
                    }
                }

                if (ShowProjection && _projectionValid) DrawProjection(chartControl, chartScale, lastDataBar);
                if (ShowStatus) DrawStatus(chartControl, barsWithTrades);
            }
        }

        private void DrawRings(List<BookLevel> side, SharpDX.Direct2D1.Brush brush, float x, ChartScale chartScale, long bookMax)
        {
            int n = Math.Min(DomDepth, side.Count);
            for (int i = 0; i < n; i++)
            {
                double ratio  = (double)side[i].Volume / bookMax;
                float  y      = chartScale.GetYByValue(side[i].Price);
                float  radius = (float)(MinBubbleRadius + ratio * (MaxBubbleRadius - MinBubbleRadius));
                brush.Opacity = (float)(MinOpacity + ratio * (MaxOpacity - MinOpacity));
                RenderTarget.DrawEllipse(new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(x, y), radius, radius), brush, (float)DomRingWidth);
            }
        }

        private void DrawProjection(ChartControl chartControl, ChartScale chartScale, int lastDataBar)
        {
            // GetXByBarIndex keeps working past the last bar (right margin)
            float x      = chartControl.GetXByBarIndex(ChartBars, lastDataBar + 6);
            float y      = chartScale.GetYByValue(_projectedPrice);
            float radius = (float)(MinBubbleRadius + _projectedStrength * (MaxBubbleRadius - MinBubbleRadius));

            SharpDX.Direct2D1.Ellipse e = new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(x, y), radius, radius);
            _projDx.Opacity = 0.25f;
            RenderTarget.FillEllipse(e, _projDx);
            _projDx.Opacity = 0.90f;
            RenderTarget.DrawEllipse(e, _projDx, 1.5f);
            DrawText(chartControl, "+6", x - 8f, y - radius - 18f, _projDx);
        }

        private void DrawStatus(ChartControl chartControl, int barsWithTrades)
        {
            string l2 = _depthEvents == 0
                ? "L2: nothing received yet (needs a live connection with Level 2)"
                : string.Format("L2: {0} bid / {1} ask rows, last update {2:HH:mm:ss}", _bids.Count, _asks.Count, _lastDepthTime);
            string text = string.Format("OrderFlowBubbles  |  {0}  |  bars with trades on screen: {1}  |  {2}", State, barsWithTrades, l2);

            SharpDX.Direct2D1.Brush textBrush = chartControl.Properties.ChartText.ToDxBrush(RenderTarget);
            DrawText(chartControl, text, ChartPanel.X + 10f, ChartPanel.Y + ChartPanel.H - 24f, textBrush);
            textBrush.Dispose();
        }

        private void DrawText(ChartControl chartControl, string text, float x, float y, SharpDX.Direct2D1.Brush brush)
        {
            SharpDX.DirectWrite.TextFormat tf = chartControl.Properties.LabelFont.ToDirectWriteTextFormat();
            SharpDX.DirectWrite.TextLayout tl = new SharpDX.DirectWrite.TextLayout(Core.Globals.DirectWriteFactory, text, tf, 1600f, 24f);
            RenderTarget.DrawTextLayout(new SharpDX.Vector2(x, y), tl, brush);
            tl.Dispose();
            tf.Dispose();
        }

        private void EnsureDx()
        {
            if (_bidDx != null) return;
            _bidDx  = (BidBrush        ?? Brushes.DeepSkyBlue).ToDxBrush(RenderTarget);
            _askDx  = (AskBrush        ?? Brushes.OrangeRed).ToDxBrush(RenderTarget);
            _projDx = (ProjectionBrush ?? Brushes.Gold).ToDxBrush(RenderTarget);
        }

        private void ReleaseDx()
        {
            if (_bidDx  != null) { _bidDx.Dispose();  _bidDx  = null; }
            if (_askDx  != null) { _askDx.Dispose();  _askDx  = null; }
            if (_projDx != null) { _projDx.Dispose(); _projDx = null; }
        }

        public override void OnRenderTargetChanged()
        {
            ReleaseDx();
        }

        #region Properties
        // 1. Data
        [Range(1, 50), Display(Name = "DOM depth (rows per side)", Description = "Level 2 rows per side drawn as rings on the forming bar", GroupName = "1. Data", Order = 1)]
        public int DomDepth { get; set; }
        [Range(1, 100), Display(Name = "Cluster look-back (bars)", Description = "Bars used for the +6 projection", GroupName = "1. Data", Order = 2)]
        public int ClusterLookback { get; set; }

        // 2. Bubbles
        [Range(1, 80), Display(Name = "Max bubble radius (px)", GroupName = "2. Bubbles", Order = 1)]
        public int MaxBubbleRadius { get; set; }
        [Range(1, 80), Display(Name = "Min bubble radius (px)", GroupName = "2. Bubbles", Order = 2)]
        public int MinBubbleRadius { get; set; }
        [Range(0.05, 1.0), Display(Name = "Min opacity", Description = "Opacity of the lightest level", GroupName = "2. Bubbles", Order = 3)]
        public double MinOpacity { get; set; }
        [Range(0.05, 1.0), Display(Name = "Max opacity", Description = "Opacity of the heaviest level on screen", GroupName = "2. Bubbles", Order = 4)]
        public double MaxOpacity { get; set; }
        [Display(Name = "Show Level 2 rings (live)", GroupName = "2. Bubbles", Order = 5)]
        public bool ShowDomRings { get; set; }
        [Range(0.5, 8.0), Display(Name = "Level 2 ring thickness (px)", GroupName = "2. Bubbles", Order = 6)]
        public double DomRingWidth { get; set; }
        [Display(Name = "Show +6 projection", GroupName = "2. Bubbles", Order = 7)]
        public bool ShowProjection { get; set; }
        [Display(Name = "Show status line", GroupName = "2. Bubbles", Order = 8)]
        public bool ShowStatus { get; set; }

        // 3. Colors
        [XmlIgnore, Display(Name = "Bid color", Description = "Levels where more traded at the bid (sellers hitting) and bid-side Level 2 rings", GroupName = "3. Colors", Order = 1)]
        public Brush BidBrush { get; set; }
        [Browsable(false)]
        public string BidBrushSerializable { get { return Serialize.BrushToString(BidBrush); } set { BidBrush = Serialize.StringToBrush(value); } }

        [XmlIgnore, Display(Name = "Ask color", Description = "Levels where more traded at the ask (buyers lifting) and ask-side Level 2 rings", GroupName = "3. Colors", Order = 2)]
        public Brush AskBrush { get; set; }
        [Browsable(false)]
        public string AskBrushSerializable { get { return Serialize.BrushToString(AskBrush); } set { AskBrush = Serialize.StringToBrush(value); } }

        [XmlIgnore, Display(Name = "Projection color", GroupName = "3. Colors", Order = 3)]
        public Brush ProjectionBrush { get; set; }
        [Browsable(false)]
        public string ProjectionBrushSerializable { get { return Serialize.BrushToString(ProjectionBrush); } set { ProjectionBrush = Serialize.StringToBrush(value); } }
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
