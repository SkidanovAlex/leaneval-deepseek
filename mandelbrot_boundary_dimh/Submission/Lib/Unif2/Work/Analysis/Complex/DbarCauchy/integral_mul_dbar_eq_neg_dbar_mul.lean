import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.integral_dbar_eq_zero
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.dbar_representation

/-!
# Integration by parts for `∂̄`: the formal adjoint of `dbar` is `-dbar`

Lemma (S1) of the weak Weyl lemma `Work.Analysis.Complex.DbarCauchy.analyticOnNhd_of_weak_dbar`
(sub-lemma 1 of the first item of the divisor chapter's work-queue,
`NOTES_divisor_chapter_plan.md` §20/§23.6).  It is the bridge that turns a *weak* `∂̄`-equation into
an honest one.

The proof is the one both reviewers of the statement gave: apply the proved
`integral_dbar_eq_zero` to `G := f * φ` (which is `C¹` and compactly supported), expand the
integrand with the product rule `dbar_mul`, and split the integral (legal because both summands are
continuous with compact support, hence integrable).  The two `C¹`-input lemmas
`continuous_dbar`/`hasCompactSupport_dbar` supply continuity respectively compact support of `dbar`
applied to a `C¹` compactly supported function.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- **Integration by parts for `∂̄`** (compactly supported `C¹` version):
`∫ f · ∂̄φ = − ∫ ∂̄f · φ`, i.e. the formal adjoint of `dbar` is `-dbar`. -/
theorem integral_mul_dbar_eq_neg_dbar_mul {f φ : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ z, f z * dbar φ z = - ∫ z, dbar f z * φ z := by
  have hG : ContDiff ℝ 1 (fun z : ℂ => f z * φ z) := hf.mul hφ
  have hGc : HasCompactSupport (fun z : ℂ => f z * φ z) := hfc.mul_right
  have h0 : ∫ z, dbar (fun z : ℂ => f z * φ z) z = 0 := integral_dbar_eq_zero _ hG hGc
  have hsplit : (fun z : ℂ => dbar (fun w : ℂ => f w * φ w) z)
      = fun z : ℂ => f z * dbar φ z + dbar f z * φ z := by
    funext z
    rw [dbar_mul f φ z ((hf.differentiable (by norm_num)).differentiableAt)
      ((hφ.differentiable (by norm_num)).differentiableAt)]
    ring
  have hint1 : Integrable (fun z : ℂ => f z * dbar φ z) :=
    (hf.continuous.mul (continuous_dbar φ hφ)).integrable_of_hasCompactSupport hfc.mul_right
  have hint2 : Integrable (fun z : ℂ => dbar f z * φ z) :=
    ((continuous_dbar f hf).mul hφ.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_dbar f hfc).mul_right
  rw [hsplit, integral_add hint1 hint2] at h0
  exact eq_neg_of_add_eq_zero_left h0

end Work.Analysis.Complex.DbarCauchy
