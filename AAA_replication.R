


# ============================================================
# Adaptive Asset Allocation Replication
# Butler, Philbrick, Gordillo, Varadi-style framework
# Momentum selection + minimum-variance weighting
# ============================================================

stratStats <- function(rets, digits = 4) {
  
  require(PerformanceAnalytics)
  
  rets <- na.omit(rets)
  
  stats <- rbind(
    "Annualized Return" = Return.annualized(rets),
    "Annualized Std Dev" = StdDev.annualized(rets),
    "Annualized Sharpe (Rf=0%)" = SharpeRatio.annualized(rets, Rf = 0),
    "Worst Drawdown" = maxDrawdown(rets),
    "Calmar Ratio" = CalmarRatio(rets)
  )
  
  return(round(stats, digits))
}



# ============================================================
# Long-only minimum-variance optimizer
# Fully invested, no shorting
# ============================================================

min_var_weights <- function(R, ridge = 1e-6) {
  
  require(quadprog)
  
  R <- na.omit(R)
  
  if (NCOL(R) == 1) {
    w <- 1
    names(w) <- colnames(R)
    return(w)
  }
  
  covMat <- cov(R)
  covMat <- as.matrix(covMat)
  
  # Small ridge adjustment helps avoid numerical problems
  covMat <- covMat + diag(ridge, ncol(covMat))
  
  n <- ncol(covMat)
  
  # solve.QP solves:
  # min 1/2 b'Db - d'b
  # subject to A'b >= b0
  Dmat <- 2 * covMat
  dvec <- rep(0, n)
  
  # Fully invested: sum weights = 1
  # Long only: each weight >= 0
  Amat <- cbind(
    rep(1, n),
    diag(n)
  )
  
  bvec <- c(
    1,
    rep(0, n)
  )
  
  sol <- solve.QP(
    Dmat = Dmat,
    dvec = dvec,
    Amat = Amat,
    bvec = bvec,
    meq = 1
  )
  
  w <- sol$solution
  w <- pmax(w, 0)
  w <- w / sum(w)
  
  names(w) <- colnames(R)
  
  return(w)
}



run_adaptive_asset_allocation <- function(dataStartDate = "2006-01-01",
                                          analysisStartDate = "2007-07-01",
                                          endDate = Sys.Date(),
                                          assets = c(
                                            "SPY",
                                            "VGK",
                                            "EWJ",
                                            "EEM",
                                            "VNQ",
                                            "RWX",
                                            "IEF",
                                            "TLT",
                                            "DBC",
                                            "GLD"
                                          ),
                                          topAssets = 5,
                                          momentumLookbackMonths = 6,
                                          covarianceLookbackMonths = 6,
                                          benchmarkStock = "SPY",
                                          benchmarkBond = "TLT",
                                          include6040 = TRUE,
                                          verbose = TRUE) {
  
  require(quantmod)
  require(PerformanceAnalytics)
  require(xts)
  require(zoo)
  require(quadprog)
  
  # -----------------------------
  # Input checks
  # -----------------------------
  if (topAssets > length(assets)) {
    stop("topAssets cannot be greater than the number of assets.")
  }
  
  if (include6040) {
    if (!(benchmarkStock %in% assets) | !(benchmarkBond %in% assets)) {
      stop("benchmarkStock and benchmarkBond must both be included in assets.")
    }
  }
  
  allSymbols <- unique(assets)
  
  # -----------------------------
  # Download adjusted prices
  # -----------------------------
  priceList <- list()
  
  for (sym in allSymbols) {
    
    if (verbose) {
      message("Downloading: ", sym)
    }
    
    tmp <- getSymbols(
      sym,
      from = dataStartDate,
      to = endDate,
      auto.assign = FALSE,
      warnings = FALSE
    )
    
    px <- Ad(tmp)
    colnames(px) <- sym
    priceList[[sym]] <- px
  }
  
  dailyPrices <- do.call(merge, priceList)
  dailyPrices <- na.omit(dailyPrices[, allSymbols])
  
  dailyReturns <- Return.calculate(dailyPrices)
  dailyReturns <- na.omit(dailyReturns)
  dailyReturns <- dailyReturns[, assets]
  
  if (verbose) {
    message("Daily return data begins: ", as.character(first(index(dailyReturns))))
    message("Daily return data ends:   ", as.character(last(index(dailyReturns))))
  }
  
  # -----------------------------
  # Monthly rebalance dates
  # -----------------------------
  monthEnds <- endpoints(dailyReturns, on = "months")
  monthEnds <- monthEnds[monthEnds > 0]
  monthEnds <- monthEnds[monthEnds <= NROW(dailyReturns)]
  
  maxLookback <- max(momentumLookbackMonths, covarianceLookbackMonths)
  
  if (length(monthEnds) <= maxLookback) {
    stop("Not enough monthly data for the requested lookback windows.")
  }
  
  # -----------------------------
  # Helper: cumulative return
  # -----------------------------
  cumulative_return <- function(x) {
    prod(1 + as.numeric(x), na.rm = FALSE) - 1
  }
  
  # -----------------------------
  # Preallocate weights
  # -----------------------------
  nRows <- NROW(dailyReturns)
  nAssets <- length(assets)
  
  weightsMat <- matrix(
    NA_real_,
    nrow = nRows,
    ncol = nAssets
  )
  
  colnames(weightsMat) <- assets
  
  selectionRecords <- vector(
    "list",
    length(monthEnds) - maxLookback
  )
  
  recordCounter <- 1
  
  # -----------------------------
  # Main monthly signal loop
  # -----------------------------
  for (k in (maxLookback + 1):length(monthEnds)) {
    
    signalIndex <- monthEnds[k]
    signalDate <- index(dailyReturns)[signalIndex]
    
    if (verbose && recordCounter %% 25 == 0) {
      message("Processing rebalance ", recordCounter, " | ", as.character(signalDate))
    }
    
    # Momentum window: previous N months of daily returns
    momStart <- monthEnds[k - momentumLookbackMonths] + 1
    momEnd <- monthEnds[k]
    
    momentumWindow <- dailyReturns[momStart:momEnd, assets]
    
    momentums <- apply(
      momentumWindow,
      2,
      cumulative_return
    )
    
    rankedAssets <- names(sort(momentums, decreasing = TRUE))
    selectedAssets <- rankedAssets[1:topAssets]
    
    # Covariance window: previous N months of daily returns
    covStart <- monthEnds[k - covarianceLookbackMonths] + 1
    covEnd <- monthEnds[k]
    
    covarianceWindow <- dailyReturns[covStart:covEnd, selectedAssets]
    
    selectedWeights <- min_var_weights(covarianceWindow)
    
    # Full universe weights
    w <- rep(0, nAssets)
    names(w) <- assets
    w[selectedAssets] <- selectedWeights[selectedAssets]
    
    # Signal is created at month-end close.
    # It will be lagged before calculating returns.
    weightsMat[signalIndex, ] <- w[assets]
    
    selectionRecords[[recordCounter]] <- data.frame(
      date = as.Date(signalDate),
      selectedAssets = paste(selectedAssets, collapse = ", "),
      topAsset = selectedAssets[1],
      maxWeight = max(w),
      minSelectedWeight = min(w[selectedAssets]),
      effectiveAssets = 1 / sum(w^2),
      stringsAsFactors = FALSE
    )
    
    recordCounter <- recordCounter + 1
  }
  
  # -----------------------------
  # Convert signal weights to daily weights
  # -----------------------------
  weights <- xts(
    weightsMat,
    order.by = index(dailyReturns)
  )
  
  weights <- na.locf(weights, na.rm = FALSE)
  
  # Lag one day so month-end signals are applied after the close
  weightsLag <- lag(weights, k = 1)
  
  # -----------------------------
  # AAA strategy returns
  # -----------------------------
  aaaReturns <- xts(
    rowSums(weightsLag * dailyReturns[, assets], na.rm = FALSE),
    order.by = index(dailyReturns)
  )
  
  colnames(aaaReturns) <- "AAA"
  
  # -----------------------------
  # Equal-weight benchmark
  # Monthly rebalanced equal weight across same universe
  # -----------------------------
  equalWeightReturns <- Return.portfolio(
    R = dailyReturns[, assets],
    weights = rep(1 / nAssets, nAssets),
    rebalance_on = "months"
  )
  
  colnames(equalWeightReturns) <- "EqualWeight"
  
  # -----------------------------
  # Optional 60/40 reference
  # Not the main benchmark, only a familiar reference
  # -----------------------------
  if (include6040) {
    
    sixtyFortyReturns <- Return.portfolio(
      R = dailyReturns[, c(benchmarkStock, benchmarkBond)],
      weights = c(0.60, 0.40),
      rebalance_on = "months"
    )
    
    colnames(sixtyFortyReturns) <- "Benchmark_60_40"
    
    referenceReturns <- merge(
      aaaReturns,
      equalWeightReturns,
      sixtyFortyReturns
    )
    
  } else {
    
    referenceReturns <- merge(
      aaaReturns,
      equalWeightReturns
    )
  }
  
  # Main reported returns
  returns <- merge(
    aaaReturns,
    equalWeightReturns
  )
  
  returns <- returns[paste0(analysisStartDate, "/")]
  returns <- na.omit(returns)
  
  referenceReturns <- referenceReturns[paste0(analysisStartDate, "/")]
  referenceReturns <- na.omit(referenceReturns)
  
  # -----------------------------
  # Clean selection log
  # -----------------------------
  selectionRecords <- selectionRecords[!sapply(selectionRecords, is.null)]
  selectionLog <- do.call(rbind, selectionRecords)
  
  selectionLog <- subset(
    selectionLog,
    date >= as.Date(first(index(returns))) &
      date <= as.Date(last(index(returns)))
  )
  
  # -----------------------------
  # Annual returns
  # -----------------------------
  annualReturns <- apply.yearly(returns, Return.cumulative)
  
  # -----------------------------
  # Turnover
  # -----------------------------
  turnover <- rowSums(
    abs(weightsLag - lag(weightsLag, 1)),
    na.rm = TRUE
  )
  
  turnover <- xts(turnover, order.by = index(weightsLag))
  colnames(turnover) <- "AAA_Turnover"
  
  liveTurnover <- turnover[index(returns)]
  annualTurnover <- apply.yearly(liveTurnover, sum, na.rm = TRUE)
  
  turnoverSummary <- rbind(
    "Average Annual Turnover" = mean(annualTurnover, na.rm = TRUE),
    "Maximum Annual Turnover" = max(annualTurnover, na.rm = TRUE)
  )
  
  turnoverSummary <- round(turnoverSummary, 4)
  
  # -----------------------------
  # Weight and concentration stats
  # -----------------------------
  liveWeights <- weightsLag[index(returns), assets]
  
  averageWeights <- colMeans(liveWeights, na.rm = TRUE)
  averageWeights <- round(averageWeights, 4)
  
  liveEffectiveAssets <- 1 / rowSums(liveWeights^2, na.rm = TRUE)
  
  exposureStats <- data.frame(
    avgEffectiveAssets = mean(liveEffectiveAssets, na.rm = TRUE),
    avgMaxWeight = mean(apply(liveWeights, 1, max, na.rm = TRUE), na.rm = TRUE),
    avgMinHeldWeight = mean(
      apply(liveWeights, 1, function(x) min(x[x > 0], na.rm = TRUE)),
      na.rm = TRUE
    )
  )
  
  exposureStats <- round(exposureStats, 4)
  
  # -----------------------------
  # Selection counts
  # -----------------------------
  selectedAssetVector <- unlist(strsplit(selectionLog$selectedAssets, ", "))
  
  selectionCounts <- table(selectedAssetVector)
  selectionWeights <- round(prop.table(selectionCounts), 4)
  
  # -----------------------------
  # Return object
  # -----------------------------
  return(list(
    returns = returns,
    referenceReturns = referenceReturns,
    summary = stratStats(returns),
    annualReturns = round(annualReturns, 4),
    selectionCounts = selectionCounts,
    selectionWeights = selectionWeights,
    averageWeights = averageWeights,
    exposureStats = exposureStats,
    turnoverSummary = turnoverSummary,
    dailyPrices = dailyPrices,
    dailyReturns = dailyReturns,
    weights = weights,
    weightsLag = weightsLag,
    selectionLog = selectionLog,
    turnover = turnover,
    settings = list(
      dataStartDate = dataStartDate,
      analysisStartDate = as.character(first(index(returns))),
      endDate = as.character(last(index(returns))),
      assets = assets,
      topAssets = topAssets,
      momentumLookbackMonths = momentumLookbackMonths,
      covarianceLookbackMonths = covarianceLookbackMonths,
      benchmark = "Monthly rebalanced equal weight portfolio using the same assets",
      include6040 = include6040
    )
  ))
}


aaaTest <- run_adaptive_asset_allocation(
  dataStartDate = "2006-01-01",
  analysisStartDate = "2007-07-01",
  endDate = "2026-07-09",
  assets = c("SPY", "VGK", "EWJ", "EEM", "VNQ", "RWX", "IEF", "TLT", "DBC", "GLD"),
  topAssets = 5,
  momentumLookbackMonths = 6,
  covarianceLookbackMonths = 6,
  benchmarkStock = "SPY",
  benchmarkBond = "TLT",
  include6040 = TRUE,
  verbose = TRUE
)




aaaTest$summary
aaaTest$annualReturns
aaaTest$exposureStats
aaaTest$turnoverSummary
aaaTest$selectionCounts
aaaTest$selectionWeights
aaaTest$averageWeights
aaaTest$settings




charts.PerformanceSummary(
  aaaTest$returns,
  main = "Adaptive Asset Allocation vs. Equal Weight Benchmark",
  wealth.index = T,
  colorset = c("darkgreen", "darkorange")
)



chart.CumReturns(
  aaaTest$returns,
  wealth.index = TRUE,
  main = "Adaptive Asset Allocation vs. Equal Weight Benchmark"
)




chart.Drawdown(
  aaaTest$returns,
  main = "Adaptive Asset Allocation Drawdowns vs. Equal Weight Benchmark",
  legend.loc = "bottomright",
  colorset = c("darkgreen", "darkorange")
)




table.CalendarReturns(aaaTest$returns)




charts.PerformanceSummary(
  aaaTest$referenceReturns,
  main = "AAA Strategy, Equal Weight Benchmark, and 60/40 Reference"
)

































