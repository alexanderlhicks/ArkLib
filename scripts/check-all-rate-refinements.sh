#!/usr/bin/env bash

# Focused local-only build, axiom audit, and exact finite regression checks.
set -euo pipefail

review_repo_root="$(git rev-parse --show-toplevel)"
cd "$review_repo_root"

# Keep the focused audit local rather than consulting or populating a remote artifact cache.
export LAKE_ARTIFACT_CACHE=false
export LAKE_NO_CACHE=true

lake build \
  ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.RefinedBand \
  ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.StrongBand \
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.SharperBandNormalizedRank \
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.SharperBandComparison \
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SharperBandEndpoint \
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.TunableBandEndpoint \
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexPartitionCounting \
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexMaximumTail \
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexTailBounds

lake env lean --trust=0 scripts/AllRateRefinementAudit.lean
python3 scripts/all_rate_partition_experiments.py
