import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodAssembly
import Submission.Work.NumberTheory.Chen.BTermCount.BLodGeomSum
import Submission.Work.NumberTheory.Chen.BTermCount.BLodCut
import Submission.Work.NumberTheory.Chen.BTermCount.CorrectionDefs

open Finset Filter
open scoped BigOperators Topology

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# Shared vocabulary for the *unweighted* bilinear level of distribution

This module collects the quantities that the unweighted analogue of
`Work.NumberTheory.Chen.BTermCount.bRemCorrLevelOfDistribution` uses, so that the
dyadic assembly (`BLodLargeRSumUnweightedDyadic`) and the arithmetic evaluation
(`BLodLargeRSumArith`) can be stated against the *same* explicit expression.

The unweighted reduction of the target (the character expansion of `bRemCorr`, the Möbius
decomposition of the lifted character sums and the `1/φ`-weighted reindexing) leaves the
double sum

  `Σ_{t ≤ D} (1/φ t) · Σ_{r ≤ D, 2 ≤ r} (1/φ r) · bProdCharSumDivSum x M Y t r`,

which is then split at a conductor threshold `R₀` (small conductors: Siegel–Walfisz, via
`BLodSmallRSum`; large conductors: the bilinear large sieve `BLodCutLS`).

For the large-conductor range `R₀ < r ≤ D` one writes, for each triple
`(t, j, k)` with `j < blockCount M Y` a dyadic `a`-block and `2^k` the dyadic size of the
conductor, the large-sieve bound

  `(2^k)⁻¹ · √((U_j + 4·(2^k)²)·U_j) · √((V_j + 4·(2^k)²)·B₂(j)) · log(2 U_j V_j + 2)`

with `U_j = 2 * blockStart M j` (twice the block start: the `a`-range),
`V_j = (x+2)/blockStart M j + 1` (the `b`-range) and `B₂(j) = bPairCount Y V_j`
(the sum of squares of the `b`-coefficients).  Summing the geometric series in `k`
(`BLodGeomSum`) turns this into

  `√(U_j · B₂(j)) · (2√(U_j V_j)/2^{k₀} + 2√U_j·K + 2√V_j·K + 4·2^K) · log(2 U_j V_j + 2)`

where `k₀ = Nat.log 2 R₀` is the first dyadic exponent above `R₀` and
`K = Nat.log 2 D + 1` is the last one (so that `2^K > D`).  `blodLSBlockSum` is the sum of
these expressions over the blocks `j < blockCount M Y`: it is the quantity produced by the
dyadic assembly and consumed by the arithmetic evaluation.
-/

/-- The `a`-range of the dyadic block `j`: twice the block start. -/
noncomputable def blodU (M : ℕ) (j : ℕ) : ℕ := 2 * blockStart M j

/-- The `b`-range of the dyadic block `j`. -/
noncomputable def blodV (x : ℕ) (M : ℕ) (j : ℕ) : ℕ := (x + 2) / blockStart M j + 1

/-- **The large-conductor large-sieve block sum.**  Sum over the dyadic `a`-blocks of the
geometric-series bound for the maximal bilinear character large sieve over the conductor
blocks `2^k`, `Nat.log 2 R₀ ≤ k ≤ Nat.log 2 D`. -/
noncomputable def blodLSBlockSum (x M Y D R₀ : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (blockCount M Y),
    Real.sqrt ((blodU M j : ℝ) * (bPairCount Y (blodV x M j) : ℝ)) *
      (2 * Real.sqrt ((blodU M j : ℝ) * (blodV x M j : ℝ)) / (2 : ℝ) ^ (Nat.log 2 R₀)
        + 2 * Real.sqrt (blodU M j : ℝ) * ((Nat.log 2 D + 1 : ℕ) : ℝ)
        + 2 * Real.sqrt (blodV x M j : ℝ) * ((Nat.log 2 D + 1 : ℕ) : ℝ)
        + 4 * (2 : ℝ) ^ (Nat.log 2 D + 1)) *
      Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2)

/-- The `1/φ`-weighted modulus sum `Σ_{t ≤ D} 1/φ t`. -/
noncomputable def blodW1 (D : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹

/-- The large-conductor part of the unweighted bilinear level of distribution:
the `t`-weighted sum of the `1/φ(r)`-weighted conductor sums over `R₀ < r ≤ D`. -/
noncomputable def blodLargeUnw (x M Y D R₀ : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ *
    ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r),
      (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r

/-- The small-conductor part of the unweighted bilinear level of distribution:
the `t`-weighted sum of the `1/φ(r)`-weighted conductor sums over `2 ≤ r ≤ R₀`. -/
noncomputable def blodSmallUnw (x M Y D R₀ : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ *
    ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
      (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r

/-- The `3^{ω r}`-weighted large-conductor sum, the quantity bounded by `BLodSmallRSum`
(whose LHS is the *weighted* small-conductor sum). -/
noncomputable def blodSmallWtd (x M Y D R₀ : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 D, ((3 : ℝ) ^ (t.primeFactors.card) / (Nat.totient t : ℝ)) *
    ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
      ((3 : ℝ) ^ (r.primeFactors.card) / (Nat.totient r : ℝ)) * bProdCharSumDivSum x M Y t r

/-- The `1/φ`-weighted conductor sum over **all** `2 ≤ r ≤ D`: the sum produced by the
unweighted reduction. -/
noncomputable def blodAllUnw (x M Y D : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ *
    ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
      (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r

end Work.NumberTheory.Chen.BTermCount
