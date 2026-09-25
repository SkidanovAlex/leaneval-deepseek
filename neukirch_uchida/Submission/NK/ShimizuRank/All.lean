import Submission.NK.ShimizuRank.Basic
import Submission.NK.ShimizuRank.ComplexPlace.nrComplexPlaces_lt_of_finrank_lt
import Submission.NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt
import Submission.NK.ShimizuRank.HausRank
import Submission.NK.ShimizuRank.ResRank
import Submission.NK.ShimizuRank.StrictMono
import Submission.NK.ShimizuRank.Package
import Submission.NK.ShimizuRank.hausQuot_torsionFree
import Submission.NK.ShimizuRank.rankGamma_self
import Submission.NK.ShimizuRank.not_rankFormulaInput_self

/-!
# `Submission/Work/ShimizuRank/` — umbrella

Import this module to get the whole chapter: the residual named inputs of the Iwasawa-theoretic rank
computation of Shimizu's §4 (arXiv:2009.10431), the proofs of the reductions of
`NK.Reconstruct.HausRankInput`, `NK.Reconstruct.RankStrictMonoLevelInputGen` and
`NK.Reconstruct.ResRankInputGen` to them, and the consumer-facing corollaries.

Start from `NK.ShimizuRank.Residuals`, `NK.ShimizuRank.rankInputs` and
`NK.ShimizuRank.rankStrictMono_of_complex` (all in `Package.lean`); see `README.md` in this
directory for the full account, including the audit of each residual and the two findings reported
there (the finiteness of `rankGamma` is an independent input, and
`NK.Reconstruct.RankFormulaInput` is false for small `K'`).
-/
