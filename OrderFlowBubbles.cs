#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Windows.Media;
using NinjaTrader.Cbi;
using NinjaTrader.Data;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Chart;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.DrawingTools;
using SharpDX;
using SharpDX.Direct2D1;
using SharpDX.DirectWrite;
#endregion

// ──────────────────────────────────────────────────────────────────────────────
// OrderFlowBubbles — NinjaTrader 8 Indicator
//
// Visualises live order-flow and L2 (DOM) positioning on a standard candle chart.
// The full order book is mirrored position-by-position from OnMarketDepth. For
// each bar, every price in the top DomDepth rows is credited with size × seconds
// resting on the book, so orders that sit there outweigh orders that flash in and
// out. The resulting "bubble" is rendered directly on the chart panel: radius and
// opacity both scale with that resting size relative to the bar's maximum, so
// clusters glow large and bright while thin levels stay small and faint.
//
// Cluster projection: a weighted-average of the last N bars' dominant levels is
// used to draw a projected cluster zone 6 bars to the right of the last painted
// bar. This gives an early visual hint of where order interest may be building.
// ──────────────────────────────────────────────────────────────────────────────

namespace NinjaTrader.NinjaScript.Indicators
{
    [Description("Order-flow bubble map — visualises L2/DOM clustering on a candle chart with a 6-bar forward projection")]
    public class OrderFlowBubbles : Indicator
    {
        // ── internal structures ───────────────────────────────────────────────

        private struct BubbleEntry
        {
            public double Price;
            public double BidVol;
            public double AskVol;
            public double TotalVol;  // bid + ask
        }

        // One slot per completed bar; keyed by bar index → list of price levels
        private Dictionary<int, List<BubbleEntry>> _barBubbles;

        // Accumulator for the bar currently forming (price → size-seconds on book)
        private Dictionary<double, BubbleEntry> _liveLevels;

        private class BookLevel { public double Price; public long Volume; }

        // Depth operations address rows by Position, so the whole book is kept even
        // though only the top DomDepth rows are read.
        private readonly List<BookLevel> _bids = new List<BookLevel>();
        private readonly List<BookLevel> _asks = new List<BookLevel>();
        private DateTime _lastBookTime = DateTime.MinValue;

        // Caps the credit for a quiet spell (session gap, reconnect) so it can't swamp a bar
        private const double MaxBookGapSeconds = 5.0;

        // Depth/bar events and OnRender run on different threads
        private readonly object _sync = new object();

        private MasterInstrument _mi;

        // Cluster-projection state (updated when a bar closes)
        private double _projectedPrice;
        private double _projectedStrength;   // 0-1 normalised
        private bool   _projectionValid;

        // SharpDX resources (created once, released on cleanup)
        private SharpDX.Direct2D1.Brush _bidBrush;
        private SharpDX.Direct2D1.Brush _askBrush;
        private SharpDX.Direct2D1.Brush _projBrush;
        private SharpDX.Direct2D1.Brush _projOutlineBrush;

        // ── parameters ───────────────────────────────────────────────────────

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "DOM Depth", Description = "Number of DOM price levels to absorb per update", Order = 1, GroupName = "Order Flow")]
        public int DomDepth { get; set; }

        [NinjaScriptProperty]
        [Range(1, 50)]
        [Display(Name = "Cluster Look-back (bars)", Description = "Bars used to compute the 6-bar forward cluster projection", Order = 2, GroupName = "Order Flow")]
        public int ClusterLookback { get; set; }

        [NinjaScriptProperty]
        [Range(1, 40)]
        [Display(Name = "Max Bubble Radius (px)", Description = "Pixel radius of the largest bubble", Order = 3, GroupName = "Visuals")]
        public int MaxBubbleRadius { get; set; }

        [NinjaScriptProperty]
        [Range(1, 40)]
        [Display(Name = "Min Bubble Radius (px)", Description = "Pixel radius of the smallest visible bubble", Order = 4, GroupName = "Visuals")]
        public int MinBubbleRadius { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Bid Bubble Color", Order = 5, GroupName = "Visuals")]
        public System.Windows.Media.Color BidColor { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Ask Bubble Color", Order = 6, GroupName = "Visuals")]
        public System.Windows.Media.Color AskColor { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Projection Color", Order = 7, GroupName = "Visuals")]
        public System.Windows.Media.Color ProjectionColor { get; set; }

        [NinjaScriptProperty]
        [Range(0.1, 1.0)]
        [Display(Name = "Min Bubble Opacity", Description = "Opacity for the thinnest visible bubble (0.1–1.0)", Order = 8, GroupName = "Visuals")]
        public double MinOpacity { get; set; }

        // ── lifecycle ─────────────────────────────────────────────────────────

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description          = "Order-flow bubble map — live DOM clustering with 6-bar forward projection";
                Name                 = "OrderFlowBubbles";
                Calculate            = Calculate.OnEachTick;
                IsOverlay            = true;
                DisplayInDataBox     = false;
                DrawOnPricePanel     = true;
                IsAutoScale          = false;
                IsSuspendedWhileInactive = false;

                DomDepth        = 10;
                ClusterLookback = 10;
                MaxBubbleRadius = 20;
                MinBubbleRadius = 3;
                BidColor        = Colors.DeepSkyBlue;
                AskColor        = Colors.OrangeRed;
                ProjectionColor = Colors.Yellow;
                MinOpacity      = 0.2;
            }
            else if (State == State.DataLoaded)
            {
                _barBubbles  = new Dictionary<int, List<BubbleEntry>>();
                _liveLevels  = new Dictionary<double, BubbleEntry>();
                _mi          = Instrument.MasterInstrument;
                _projectionValid = false;
            }
            else if (State == State.Terminated)
            {
                ReleaseSharpDXResources();
            }
        }

        // ── DOM (L2) feed ─────────────────────────────────────────────────────

        protected override void OnMarketDepth(MarketDepthEventArgs e)
        {
            lock (_sync)
            {
                // Credit the book as it stood up to this event, before mutating it
                IntegrateBook(e.Time);

                if (e.IsReset) { _bids.Clear(); _asks.Clear(); return; }

                List<BookLevel> side = e.MarketDataType == MarketDataType.Bid ? _bids
                                     : e.MarketDataType == MarketDataType.Ask ? _asks
                                     : null;
                if (side == null) return;

                switch (e.Operation)
                {
                    case Operation.Add:
                        if (e.Position <= side.Count)
                            side.Insert(e.Position, new BookLevel { Price = e.Price, Volume = e.Volume });
                        break;
                    case Operation.Update:
                        if (e.Position < side.Count) { side[e.Position].Price = e.Price; side[e.Position].Volume = e.Volume; }
                        break;
                    case Operation.Remove:
                        if (e.Position < side.Count) side.RemoveAt(e.Position);
                        break;
                }
            }
        }

        private void IntegrateBook(DateTime now)
        {
            if (_lastBookTime != DateTime.MinValue)
            {
                double dt = Math.Min((now - _lastBookTime).TotalSeconds, MaxBookGapSeconds);
                if (dt > 0)
                {
                    AccumulateSide(_bids, dt, true);
                    AccumulateSide(_asks, dt, false);
                }
            }
            if (now > _lastBookTime) _lastBookTime = now;
        }

        private void AccumulateSide(List<BookLevel> side, double dt, bool isBid)
        {
            int n = Math.Min(DomDepth, side.Count);
            for (int i = 0; i < n; i++)
            {
                double p = _mi.RoundToTickSize(side[i].Price);
                BubbleEntry entry;
                if (!_liveLevels.TryGetValue(p, out entry))
                    entry = new BubbleEntry { Price = p };
                if (isBid) entry.BidVol += side[i].Volume * dt;
                else       entry.AskVol += side[i].Volume * dt;
                entry.TotalVol = entry.BidVol + entry.AskVol;
                _liveLevels[p] = entry;
            }
        }

        // ── tick / bar processing ─────────────────────────────────────────────

        protected override void OnBarUpdate()
        {
            if (BarsInProgress != 0) return;  // only process primary series

            // On bar close snapshot the live levels into the completed-bar store
            if (IsFirstTickOfBar && CurrentBar > 0)
            {
                lock (_sync)
                {
                    SnapshotLiveBar(CurrentBar - 1);
                    UpdateClusterProjection();
                }
            }

            // Always force a repaint so the live bubble updates each tick
            ForceRefresh();
        }

        private void SnapshotLiveBar(int barIndex)
        {
            if (_liveLevels.Count == 0) return;

            var list = new List<BubbleEntry>(_liveLevels.Values);
            _barBubbles[barIndex] = list;
            _liveLevels.Clear();
        }

        // ── cluster projection ────────────────────────────────────────────────

        private void UpdateClusterProjection()
        {
            if (CurrentBar < ClusterLookback) { _projectionValid = false; return; }

            double weightedPrice = 0;
            double totalWeight   = 0;

            for (int i = 1; i <= ClusterLookback; i++)
            {
                int barIndex = CurrentBar - i;
                if (!_barBubbles.TryGetValue(barIndex, out var levels)) continue;

                double barMax = 0;
                foreach (var e in levels) barMax = Math.Max(barMax, e.TotalVol);
                if (barMax <= 0) continue;

                // Weight by recency (more recent = higher weight)
                double recencyWeight = (double)(ClusterLookback - i + 1) / ClusterLookback;

                foreach (var e in levels)
                {
                    double volWeight = (e.TotalVol / barMax) * recencyWeight;
                    weightedPrice += e.Price * volWeight;
                    totalWeight   += volWeight;
                }
            }

            if (totalWeight <= 0) { _projectionValid = false; return; }

            _projectedPrice    = weightedPrice / totalWeight;
            _projectedStrength = Math.Min(1.0, totalWeight / ClusterLookback);
            _projectionValid   = true;
        }

        // ── SharpDX rendering ─────────────────────────────────────────────────

        protected override void OnRender(ChartControl chartControl, ChartScale chartScale)
        {
            if (RenderTarget == null) return;

            EnsureBrushes();

            int firstBar    = ChartBars.FromIndex;
            int lastBar     = ChartBars.ToIndex;
            int lastDataBar = ChartBars.Count - 1;

            // Copy under the lock, draw outside it; completed-bar lists are never mutated
            var visible = new List<KeyValuePair<int, List<BubbleEntry>>>();
            List<BubbleEntry> live;
            lock (_sync)
            {
                for (int barIndex = firstBar; barIndex <= lastBar; barIndex++)
                {
                    List<BubbleEntry> levels;
                    if (_barBubbles.TryGetValue(barIndex, out levels))
                        visible.Add(new KeyValuePair<int, List<BubbleEntry>>(barIndex, levels));
                }
                live = new List<BubbleEntry>(_liveLevels.Values);
            }

            // ── render historical bars ────────────────────────────────────────
            foreach (var bar in visible)
            {
                double barMax = 0;
                foreach (var e in bar.Value) barMax = Math.Max(barMax, e.TotalVol);
                if (barMax <= 0) continue;

                float xCenter = (float)chartControl.GetXByBarIndex(ChartBars, bar.Key);

                foreach (var entry in bar.Value)
                    DrawBubble(chartScale, xCenter, entry, barMax);
            }

            // ── render live bar (current forming bar) ─────────────────────────
            double liveMax = 0;
            foreach (var e in live) liveMax = Math.Max(liveMax, e.TotalVol);
            if (liveMax > 0)
            {
                float xCenter = (float)chartControl.GetXByBarIndex(ChartBars, lastDataBar);
                foreach (var e in live)
                    DrawBubble(chartScale, xCenter, e, liveMax);
            }

            // ── render 6-bar forward cluster projection ───────────────────────
            if (_projectionValid)
                DrawProjection(chartControl, chartScale, lastDataBar);
        }

        private void DrawBubble(ChartScale chartScale, float xCenter, BubbleEntry entry, double barMax)
        {
            float yCenter = (float)chartScale.GetYByValue(entry.Price);
            double ratio  = entry.TotalVol / barMax;   // 0..1

            float radius  = MinBubbleRadius + (float)(ratio * (MaxBubbleRadius - MinBubbleRadius));
            float opacity = (float)(MinOpacity + ratio * (1.0 - MinOpacity));

            bool isBidDominant = entry.BidVol >= entry.AskVol;

            // Set alpha on the appropriate brush
            if (isBidDominant)
            {
                ((SharpDX.Direct2D1.SolidColorBrush)_bidBrush).Color =
                    new SharpDX.Color4(
                        ((SharpDX.Direct2D1.SolidColorBrush)_bidBrush).Color.Red,
                        ((SharpDX.Direct2D1.SolidColorBrush)_bidBrush).Color.Green,
                        ((SharpDX.Direct2D1.SolidColorBrush)_bidBrush).Color.Blue,
                        opacity);
                RenderTarget.FillEllipse(
                    new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(xCenter, yCenter), radius, radius),
                    _bidBrush);
            }
            else
            {
                ((SharpDX.Direct2D1.SolidColorBrush)_askBrush).Color =
                    new SharpDX.Color4(
                        ((SharpDX.Direct2D1.SolidColorBrush)_askBrush).Color.Red,
                        ((SharpDX.Direct2D1.SolidColorBrush)_askBrush).Color.Green,
                        ((SharpDX.Direct2D1.SolidColorBrush)_askBrush).Color.Blue,
                        opacity);
                RenderTarget.FillEllipse(
                    new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(xCenter, yCenter), radius, radius),
                    _askBrush);
            }
        }

        private void DrawProjection(ChartControl chartControl, ChartScale chartScale, int lastDataBar)
        {
            // Anchored to the forming bar, not the last visible one, so scrolling doesn't move it
            int projBar = lastDataBar + 6;

            // GetXByBarIndex returns valid coordinates even beyond the last rendered bar
            // because NT8 keeps the x-axis extended for right margin
            float xCenter = (float)chartControl.GetXByBarIndex(ChartBars, projBar);
            float yCenter = (float)chartScale.GetYByValue(_projectedPrice);

            float radius  = MinBubbleRadius + (float)(_projectedStrength * (MaxBubbleRadius - MinBubbleRadius));

            // Pulsing dashed ring — fill with low opacity, then draw an outline
            ((SharpDX.Direct2D1.SolidColorBrush)_projBrush).Color =
                new SharpDX.Color4(
                    ((SharpDX.Direct2D1.SolidColorBrush)_projBrush).Color.Red,
                    ((SharpDX.Direct2D1.SolidColorBrush)_projBrush).Color.Green,
                    ((SharpDX.Direct2D1.SolidColorBrush)_projBrush).Color.Blue,
                    0.25f);

            var ellipse = new SharpDX.Direct2D1.Ellipse(new SharpDX.Vector2(xCenter, yCenter), radius, radius);
            RenderTarget.FillEllipse(ellipse, _projBrush);

            ((SharpDX.Direct2D1.SolidColorBrush)_projOutlineBrush).Color =
                new SharpDX.Color4(
                    ((SharpDX.Direct2D1.SolidColorBrush)_projOutlineBrush).Color.Red,
                    ((SharpDX.Direct2D1.SolidColorBrush)_projOutlineBrush).Color.Green,
                    ((SharpDX.Direct2D1.SolidColorBrush)_projOutlineBrush).Color.Blue,
                    0.85f);

            RenderTarget.DrawEllipse(ellipse, _projOutlineBrush, 1.5f);

            // Small label
            using (var tf = new SharpDX.DirectWrite.TextFormat(
                    Core.Globals.DirectWriteFactory,
                    "Arial", FontWeight.Normal, FontStyle.Normal, FontStretch.Normal, 9f))
            using (var tl = new SharpDX.DirectWrite.TextLayout(
                    Core.Globals.DirectWriteFactory, "+6", tf, 40f, 14f))
            {
                RenderTarget.DrawTextLayout(
                    new SharpDX.Vector2(xCenter - 8f, yCenter - radius - 14f),
                    tl, _projOutlineBrush);
            }
        }

        // ── brush management ──────────────────────────────────────────────────

        private void EnsureBrushes()
        {
            if (_bidBrush != null) return;

            _bidBrush = new SharpDX.Direct2D1.SolidColorBrush(
                RenderTarget,
                new SharpDX.Color4(BidColor.R / 255f, BidColor.G / 255f, BidColor.B / 255f, 1f));

            _askBrush = new SharpDX.Direct2D1.SolidColorBrush(
                RenderTarget,
                new SharpDX.Color4(AskColor.R / 255f, AskColor.G / 255f, AskColor.B / 255f, 1f));

            _projBrush = new SharpDX.Direct2D1.SolidColorBrush(
                RenderTarget,
                new SharpDX.Color4(ProjectionColor.R / 255f, ProjectionColor.G / 255f, ProjectionColor.B / 255f, 0.25f));

            _projOutlineBrush = new SharpDX.Direct2D1.SolidColorBrush(
                RenderTarget,
                new SharpDX.Color4(ProjectionColor.R / 255f, ProjectionColor.G / 255f, ProjectionColor.B / 255f, 0.85f));
        }

        private void ReleaseSharpDXResources()
        {
            _bidBrush?.Dispose();         _bidBrush         = null;
            _askBrush?.Dispose();         _askBrush         = null;
            _projBrush?.Dispose();        _projBrush        = null;
            _projOutlineBrush?.Dispose(); _projOutlineBrush = null;
        }

        // Called by NT8 when the chart control is recreated (e.g. theme change)
        public override void OnRenderTargetChanged()
        {
            ReleaseSharpDXResources();
        }
    }
}

#region NinjaScript generated code. Neither change nor remove.
namespace NinjaTrader.NinjaScript.Indicators
{
    public partial class Indicator : NinjaTrader.Gui.NinjaScript.IndicatorRenderBase
    {
        private OrderFlowBubbles[] cacheOrderFlowBubbles;
        public OrderFlowBubbles OrderFlowBubbles(int domDepth, int clusterLookback, int maxBubbleRadius, int minBubbleRadius,
            System.Windows.Media.Color bidColor, System.Windows.Media.Color askColor,
            System.Windows.Media.Color projectionColor, double minOpacity)
        {
            return OrderFlowBubbles(Input, domDepth, clusterLookback, maxBubbleRadius, minBubbleRadius,
                bidColor, askColor, projectionColor, minOpacity);
        }

        public OrderFlowBubbles OrderFlowBubbles(ISeries<double> input, int domDepth, int clusterLookback,
            int maxBubbleRadius, int minBubbleRadius,
            System.Windows.Media.Color bidColor, System.Windows.Media.Color askColor,
            System.Windows.Media.Color projectionColor, double minOpacity)
        {
            if (cacheOrderFlowBubbles != null)
                foreach (var cached in cacheOrderFlowBubbles)
                    if (cached.DomDepth == domDepth && cached.ClusterLookback == clusterLookback &&
                        cached.MaxBubbleRadius == maxBubbleRadius && cached.MinBubbleRadius == minBubbleRadius &&
                        cached.MinOpacity == minOpacity && cached.EqualsInput(input))
                        return cached;

            return CacheIndicator<OrderFlowBubbles>(
                new OrderFlowBubbles
                {
                    DomDepth        = domDepth,
                    ClusterLookback = clusterLookback,
                    MaxBubbleRadius = maxBubbleRadius,
                    MinBubbleRadius = minBubbleRadius,
                    BidColor        = bidColor,
                    AskColor        = askColor,
                    ProjectionColor = projectionColor,
                    MinOpacity      = minOpacity
                },
                input, ref cacheOrderFlowBubbles);
        }
    }
}

namespace NinjaTrader.NinjaScript.MarketAnalyzerColumns
{
    public partial class MarketAnalyzerColumn : MarketAnalyzerColumnBase
    {
        public Indicators.OrderFlowBubbles OrderFlowBubbles(int domDepth, int clusterLookback, int maxBubbleRadius,
            int minBubbleRadius, System.Windows.Media.Color bidColor, System.Windows.Media.Color askColor,
            System.Windows.Media.Color projectionColor, double minOpacity)
        {
            return indicator.OrderFlowBubbles(Input, domDepth, clusterLookback, maxBubbleRadius, minBubbleRadius,
                bidColor, askColor, projectionColor, minOpacity);
        }
    }
}

namespace NinjaTrader.NinjaScript.Strategies
{
    public partial class Strategy : NinjaTrader.Gui.NinjaScript.StrategyRenderBase
    {
        public Indicators.OrderFlowBubbles OrderFlowBubbles(int domDepth, int clusterLookback, int maxBubbleRadius,
            int minBubbleRadius, System.Windows.Media.Color bidColor, System.Windows.Media.Color askColor,
            System.Windows.Media.Color projectionColor, double minOpacity)
        {
            return indicator.OrderFlowBubbles(Input, domDepth, clusterLookback, maxBubbleRadius, minBubbleRadius,
                bidColor, askColor, projectionColor, minOpacity);
        }
    }
}
#endregion
