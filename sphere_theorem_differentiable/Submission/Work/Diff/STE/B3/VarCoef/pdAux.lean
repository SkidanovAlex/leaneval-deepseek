import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.garding_base
import Submission.Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary facts about `pd` and `star` on the flat torus

This module collects the two "structural" facts needed by the integration-by-parts proof of the
`L²`-adjointness of the variable-coefficient Laplacian `varLap A B`
(`Work.Diff.STE.B3.VarCoef.POp_adjoint_L2re`):

* `pd_pd_swap` — Clairaut's theorem: the mixed second partial derivatives of a smooth function on
  the unit torus commute (this is where the *sign* of the second-order integration by parts has to
  be pinned down: `∫ f ∂_a∂_b w = ∫ ∂_a∂_b f · w`);
* `star_fderiv` / `star_pd` — complex conjugation commutes with the Fréchet derivative, hence with
  `pd`, **unconditionally** (both sides are the junk value `0` at a point where the function is not
  differentiable).  This is what makes the pointwise identity `star (varLapStar A B g) =
  varLapStar A B (star ∘ g)` a purely algebraic statement, with no differentiability side
  conditions.
-/

noncomputable section

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Clairaut's theorem** for smooth complex-valued functions on the torus: mixed second partial
derivatives commute. -/
theorem pd_pd_swap {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ι) :
    Work.Diff.STE.pd b (Work.Diff.STE.pd a f) = Work.Diff.STE.pd a (Work.Diff.STE.pd b f) := by
  funext z
  have h2 : ContDiffOn ℝ (2 : WithTop ℕ∞) f Set.univ := hf.contDiffOn.of_le (by simp)
  exact Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
    isOpen_univ (Set.mem_univ z) h2 (Pi.single a 1) (Pi.single b 1)

/-- Complex conjugation commutes with the Fréchet derivative (unconditionally: where `f` is not
differentiable both sides vanish). -/
theorem star_fderiv {f : (ι → ℝ) → ℂ} (x v : ι → ℝ) :
    star ((fderiv ℝ f x) v) = (fderiv ℝ (fun y => star (f y)) x) v := by
  by_cases hf : DifferentiableAt ℝ f x
  · have hfd : fderiv ℝ (fun y => star (f y)) x
        = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f x) := by
      have h := (Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
      have h2 : (fun y => star (f y)) = (⇑Complex.conjCLE ∘ f) := by
        funext y
        exact (starRingEnd_apply (f y)).symm.trans (Complex.conjCLE_apply (f y)).symm
      rw [h2]; exact h
    rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, starRingEnd_apply]
  · have hg : ¬ DifferentiableAt ℝ (fun y => star (f y)) x := by
      intro h
      refine hf ?_
      have hcomp := (Complex.conjCLE.differentiableAt (x := (star (f x)))).comp x h
      have heq : (fun y => Complex.conjCLE (star (f y))) = f := by
        funext y
        simp only [Complex.conjCLE_apply]
        exact star_star (f y)
      simpa only [Function.comp_def, heq] using hcomp
    rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hg]
    simp

/-- Complex conjugation commutes with `pd` (unconditionally). -/
theorem star_pd (i : ι) (f : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    star (Work.Diff.STE.pd i f x) = Work.Diff.STE.pd i (fun y => star (f y)) x :=
  star_fderiv x (Pi.single i 1)

/-- The complexification of a real-valued function is real-valued. -/
theorem star_cm (m : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    star (((m x : ℝ) : ℂ)) = ((m x : ℝ) : ℂ) :=
  Complex.conj_ofReal (m x)

/-- Conjugation of a product of the complexification of a real function with a complex function. -/
theorem star_cm_mul (m : (ι → ℝ) → ℝ) (w : (ι → ℝ) → ℂ) :
    (fun x => star (((m x : ℝ) : ℂ) * w x)) = fun x => ((m x : ℝ) : ℂ) * star (w x) := by
  funext x
  rw [star_mul, star_cm]
  ring

end Work.Diff.STE.B3.VarCoef
