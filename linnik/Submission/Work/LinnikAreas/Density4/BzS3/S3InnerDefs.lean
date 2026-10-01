/-
# Objects for the inner `m`-sum of An's `S₃` (arXiv:2206.10104, §5, `k = ℚ`, `w = y = z`)

Namespace `Work.LinnikAreas.Density4.BzS3`.

In the reindexed second moment
`Σ_{n ≤ N} B_z(n)² = Σ_{q,r,t} μ(r)μ(t)[(r,t) = 1] ·
     Σ_{m ≤ ⌊N/(qrt)⌋, (m,rt)=1, m sqfree, mt > z, mr > z} log(mt/z)·log(mr/z)`
(see `BzHard.Bz_sq_reindex` / `BzHard.S3_eq_quadruple`) the innermost `m`-sum is, on the range
`M' < m ≤ M` with `M = ⌊N/(qrt)⌋` and `M' = max(⌊z/t⌋,⌊z/r⌋)`, the difference
`s3G (r*t) (log(z/t)) (log(z/r)) M − s3G (r*t) (log(z/t)) (log(z/r)) M'` of the two sums defined
here (because `log m − log(z/t) = log(mt/z)`).

The main term of `s3G c α β X` is `s3main c α β X = C_c·X·((log X − α − 1)(log X − β − 1) + 1)`
with `C_c = ζ(2)^{-1}∏_{p | c} p/(p+1)`, obtained by two Abel summations against the count
`Σ_{m ≤ M, (m,c)=1} μ²(m) = C_c·M + O(√M·σ_{-1/2}(c))`
(`Work.LinnikAreas.Density4.squarefree_coprime_count`).
-/
import Mathlib

namespace Work.LinnikAreas.Density4.BzS3

open Finset

noncomputable section

/-- `C_c = ζ(2)^{-1}·∏_{p | c} p/(p+1)`, the density of the squarefree integers coprime to `c`. -/
def s3c (c : ℕ) : ℝ := (Real.pi ^ 2 / 6)⁻¹ * ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

/-- `s3G c α β X = Σ_{m ≤ X, (m,c)=1, m squarefree} (log m − α)·(log m − β)`. -/
def s3G (c : ℕ) (α β : ℝ) (X : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m c ∧ Squarefree m),
    (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)

/-- The main term `C_c·X·((log X − α − 1)(log X − β − 1) + 1)` of `s3G`. -/
def s3main (c : ℕ) (α β : ℝ) (X : ℕ) : ℝ :=
  s3c c * (X : ℝ)
    * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)

end

end Work.LinnikAreas.Density4.BzS3
