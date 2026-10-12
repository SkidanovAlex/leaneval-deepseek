import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `bsOneBody` is homogeneous of degree two in its state argument

`Work.BSKinetic.bsOneBody ℓ F u ψ` is the one-body big-box kinetic form
`(2π)⁻³∫_p F(‖p‖)·‖kinFT (χ_u·Q_{Λ(u)}ψ)‖²`, where `Q_{Λ(u)}ψ = ψ − (box mean of ψ)`
is the mean-free projection in the moving box `Λ(u)`.  Since both the box mean and the
Fourier transform `kinFT` are linear, and the momentum weight is quadratic in the
Fourier transform, the form is homogeneous of degree two:

`bsOneBody ℓ F u (c·ψ) = c² · bsOneBody ℓ F u ψ`.

This is used to tidy the scaling factors of the `N`-body slot liftings.

The proof has three elementary ingredients, all recorded below:
* `kinFT_const_mul` — `kinFT` is complex-linear in its argument
  (`kinFT (c·f) p = c·kinFT f p`), by `integral_const_mul` and pointwise `ring`;
* `bsMean_const_mul` / `bsQ_const_mul` — the box mean and the mean-free projection
  are real-linear (the mean is a normalised integral, again `integral_const_mul`);
* the norm square of a complex multiple of a real scalar: `‖(c : ℂ)·K‖² = c²·‖K‖²`.
-/

namespace Work.BoseKinLoc.Word

/-- `kinFT` is complex-linear in its argument: `kinFT (c·f) p = c·kinFT f p`.  (No
integrability hypothesis is needed: for the Bochner integral `∫ a, c • f a = c • ∫ a, f a`
holds unconditionally.) -/
lemma kinFT_const_mul (c : ℂ) (f : EuclideanSpace ℝ (Fin 3) → ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z => c * f z) p = c * Submission.BoseGases.kinFT f p := by
  unfold Submission.BoseGases.kinFT
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (c * f y))
        = (fun y : EuclideanSpace ℝ (Fin 3) =>
          c * (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * f y)) from
      funext fun y => by ring]
  rw [MeasureTheory.integral_const_mul]

/-- The box mean `Work.BSKinetic.bsMean` is linear in the state. -/
lemma bsMean_const_mul (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BSKinetic.bsMean ℓ u (fun z => c * ψ z) = c * Work.BSKinetic.bsMean ℓ u ψ := by
  unfold Work.BSKinetic.bsMean
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The mean-free projection `Work.BSKinetic.bsQ` is linear in the state. -/
lemma bsQ_const_mul (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BSKinetic.bsQ ℓ u (fun z => c * ψ z) = fun x => c * Work.BSKinetic.bsQ ℓ u ψ x := by
  funext x
  simp only [Work.BSKinetic.bsQ]
  rw [bsMean_const_mul]
  ring

/-- `‖(c : ℂ)‖² = c²` for a real `c`. -/
lemma norm_sq_ofReal_cast (c : ℝ) : ‖((c : ℂ))‖ ^ 2 = c ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_ofReal]; ring

theorem bsOneBody_const_mul {ℓ : ℝ} (F : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin 3)) (c : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BSKinetic.bsOneBody ℓ F u (fun z => c * ψ z) = c ^ 2 * Work.BSKinetic.bsOneBody ℓ F u ψ := by
  -- the windowed mean-free state of `c·ψ` is `c` times that of `ψ`
  have hfun : (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
        (Work.BSKinetic.bsQ ℓ u (fun z => c * ψ z) z : ℂ))
      = fun z : EuclideanSpace ℝ (Fin 3) => (c : ℂ) *
        ((Work.BSKinetic.bsWin ℓ u z : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)) := by
    funext z
    rw [congrFun (bsQ_const_mul ℓ u c ψ) z]
    push_cast
    ring
  -- the `p`-integral scales by `c ^ 2`
  have hstep : (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          (c : ℂ) * ((Work.BSKinetic.bsWin ℓ u z : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ))) p‖ ^ 2)
      = c ^ 2 * ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          (Work.BSKinetic.bsWin ℓ u z : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)) p‖ ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [kinFT_const_mul, norm_mul, mul_pow, norm_sq_ofReal_cast]
    ring
  unfold Work.BSKinetic.bsOneBody
  rw [hfun, hstep]
  ring

end Work.BoseKinLoc.Word
