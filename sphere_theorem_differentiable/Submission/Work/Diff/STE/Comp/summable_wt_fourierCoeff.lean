import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CSq_le_ENormSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Comp

/-- Route: copy the proof of `Work.Diff.STE.CSq_le_ENormSq` (same file family):
`wt_pow_le_wordSum` bounds `wt m ^ s` by `2^s (1 + Σ_l ∏_i (2π m_{l i})²)`, `fourierCoeff_pdVec_normSq`
turns each `∏_i (2π m_{l i})² ‖û m‖²` into `‖\widehat{∂^l f}(m)‖²`, and Bessel
(`bessel_continuous`) plus `continuous_pdVec` show that the resulting majorant
`2^s ‖û m‖² + 2^s Σ_l ‖\widehat{∂^l f}(m)‖²` is summable.  (The sibling file
`CSq_le_ENormSq.lean` proves exactly this summability internally as `hLHS`.) -/
theorem summable_wt_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ s f) (hper : Work.Diff.STE.Periodic1 f) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.fourierCoeff f k‖ ^ 2) := by
  -- Bessel for `f` itself
  have hbase : Summable (fun m : ι → ℤ => ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2) :=
    (Work.Diff.STE.bessel_continuous f hf.continuous).1
  -- Bessel for the iterated derivatives
  have hderiv : ∀ l : Fin s → ι,
      Summable (fun m : ι → ℤ => ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec s l f) m‖ ^ 2) :=
    fun l => (Work.Diff.STE.bessel_continuous (Work.Diff.STE.pdVec s l f)
      (Work.Diff.STE.continuous_pdVec s l f hf)).1
  have hsum_l : Summable (fun m : ι → ℤ =>
      ∑ l : Fin s → ι, ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec s l f) m‖ ^ 2) :=
    summable_sum (fun l _ => hderiv l)
  -- the pointwise weight comparison
  have hpt : ∀ m : ι → ℤ, Work.Diff.STE.wt m ^ s * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2
      ≤ 2 ^ s * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2
        + 2 ^ s * ∑ l : Fin s → ι,
            ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec s l f) m‖ ^ 2 := by
    intro m
    have h1 := Work.Diff.STE.wt_pow_le_wordSum s m
    have h2 : ∀ l : Fin s → ι,
        (∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2) * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2
        = ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec s l f) m‖ ^ 2 :=
      fun l => (Work.Diff.STE.fourierCoeff_pdVec_normSq s l f hf hper m).symm
    calc Work.Diff.STE.wt m ^ s * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2
        ≤ (2 ^ s * (1 + ∑ l : Fin s → ι,
            ∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2))
            * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 2 ^ s * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2
            + 2 ^ s * ((∑ l : Fin s → ι,
                ∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2)
                  * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2) := by
          ring
      _ = 2 ^ s * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2
            + 2 ^ s * ∑ l : Fin s → ι,
                ((∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2)
                  * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2) := by
          rw [Finset.sum_mul]
      _ = 2 ^ s * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2
            + 2 ^ s * ∑ l : Fin s → ι,
                ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec s l f) m‖ ^ 2 := by
          simp only [h2]
  -- the majorant family is summable, hence so is the weighted family
  have hmaj : Summable (fun m : ι → ℤ => 2 ^ s * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2
      + 2 ^ s * ∑ l : Fin s → ι,
          ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec s l f) m‖ ^ 2) :=
    (hbase.mul_left _).add (hsum_l.mul_left _)
  exact Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos m).le s) (sq_nonneg _)) hpt hmaj

end Work.Diff.STE.Comp
