import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.Defs
import Submission.Work.Diff.STE.B3.flat_diag_pairing_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.conv_CSq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-- **Pointwise multiplication by a smooth `1`-periodic function is bounded on the weighted coefficient scale `CSq s`.**  (Route: `Work.Diff.STE.B3.fourierCoeff_mul` identifies the coefficients of `f * w` with `conv (fourierCoeff w) (fourierCoeff f)`, and `Work.Diff.STE.B3.SymCalcStep1.conv_CSq_le` bounds that convolution, using `summable_wt_pow_mul_norm_fourierCoeff` for the moment bounds of `fourierCoeff f`.) -/
theorem mul_CSq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : Work.Diff.STE.Periodic1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) w → Work.Diff.STE.Periodic1 w →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => f x * w x))
        ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff w) := by
  classical
  -- The convolution kernel is `fourierCoeff f`, which has finite weighted `ℓ¹`-moments because
  -- `f` is smooth and `1`-periodic.
  obtain ⟨C, hC0, hC⟩ := Work.Diff.STE.B3.SymCalcStep1.conv_CSq_le s
    (Work.Diff.STE.fourierCoeff f)
    (fun N => Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff N f hf hfp)
  refine ⟨C, hC0, ?_⟩
  intro w hw hwp
  -- `fourierCoeff_mul` identifies the coefficients of the pointwise product with the convolution.
  have hcoef : Work.Diff.STE.fourierCoeff (fun x => f x * w x)
      = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff f) (Work.Diff.STE.fourierCoeff w) := by
    have h := Work.Diff.STE.B3.fourierCoeff_mul w f hw hf hfp
    rw [show (fun x : ι → ℝ => w x * f x) = (fun x => f x * w x) from
      funext (fun x => mul_comm _ _)] at h
    exact funext h
  rw [hcoef]
  exact hC (Work.Diff.STE.fourierCoeff w)
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff w hw hwp s)

end Work.Diff.STE.B3.SymCalcStep7
