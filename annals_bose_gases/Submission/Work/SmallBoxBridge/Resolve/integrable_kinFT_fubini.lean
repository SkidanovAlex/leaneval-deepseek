import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the two-particle kinetic Fubini integrand

The `p`-space Fubini reduction of the kinetic energy of a pair of particles
produces the integrand

`a ↦ F‖a.1‖ · (e^{−i⟪a.1,a.2.1⟫} g a.2.1) · (e^{i⟪a.1,a.2.2⟫} g a.2.2)`

on `ℝ³ × (ℝ³ × ℝ³)`.  Its modulus is the pure product
`‖F‖a.1‖‖ · ‖g a.2.1‖ · ‖g a.2.2‖`, so integrability of `F‖·‖` and of `g`
on `ℝ³` gives integrability of the integrand for the product measure
(dominated convergence is not needed: the phases have modulus one).
-/

namespace Work.SmallBoxBridge.Resolve

open MeasureTheory

local notation "X" => EuclideanSpace ℝ (Fin 3)

/-- The exponential of a purely imaginary real number cast to `ℂ` has modulus one. -/
lemma norm_exp_neg_I_mul (r : ℝ) : ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (r : ℂ)) = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-r)

/-- The exponential of a purely imaginary real number cast to `ℂ` has modulus one. -/
lemma norm_exp_I_mul (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [mul_comm Complex.I (r : ℂ), Complex.norm_exp_ofReal_mul_I]

/-- The norm of a real number cast to `ℂ` is the norm of the number. -/
lemma cnorm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = ‖r‖ := by
  have h : ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r := rfl
  rw [h, RCLike.norm_ofReal]
  rfl

theorem integrable_kinFT_fubini {F : ℝ → ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable (fun a : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      ((F ‖a.1‖ : ℝ) : ℂ) *
        ((Complex.exp (-(Complex.I * (inner ℝ a.1 a.2.1 : ℂ))) * (g a.2.1 : ℂ)) *
         (Complex.exp (Complex.I * (inner ℝ a.1 a.2.2 : ℂ)) * (g a.2.2 : ℂ))))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- the (a.e.) strong measurability of the integrand: everything is either
  -- continuous or a pullback of the measurable functions `F ‖·‖` and `g`.
  have hmeas : AEStronglyMeasurable (fun a : X × (X × X) =>
      ((F ‖a.1‖ : ℝ) : ℂ) *
        ((Complex.exp (-(Complex.I * (inner ℝ a.1 a.2.1 : ℂ))) * (g a.2.1 : ℂ)) *
         (Complex.exp (Complex.I * (inner ℝ a.1 a.2.2 : ℂ)) * (g a.2.2 : ℂ))))
      (volume.prod (volume.prod volume)) := by
    have h1 : AEStronglyMeasurable (fun a : X × (X × X) => ((F ‖a.1‖ : ℝ) : ℂ))
        (volume.prod (volume.prod volume)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (hF.1.comp_fst (ν := volume))
    have h2 : AEStronglyMeasurable (fun a : X × (X × X) => (g a.2.1 : ℂ))
        (volume.prod (volume.prod volume)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (hg.1.comp_fst.comp_snd)
    have h3 : AEStronglyMeasurable (fun a : X × (X × X) => (g a.2.2 : ℂ))
        (volume.prod (volume.prod volume)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (hg.1.comp_snd.comp_snd)
    have h4 : Continuous
        (fun a : X × (X × X) => Complex.exp (-(Complex.I * (inner ℝ a.1 a.2.1 : ℂ)))) := by
      apply Complex.continuous_exp.comp
      apply Continuous.neg
      apply continuous_const.mul
      exact Complex.continuous_ofReal.comp (continuous_inner.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
    have h5 : Continuous
        (fun a : X × (X × X) => Complex.exp (Complex.I * (inner ℝ a.1 a.2.2 : ℂ))) := by
      apply Complex.continuous_exp.comp
      apply continuous_const.mul
      exact Complex.continuous_ofReal.comp (continuous_inner.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    exact h1.mul ((h4.aestronglyMeasurable.mul h2).mul (h5.aestronglyMeasurable.mul h3))
  -- the dominating function is a genuine product of integrable functions
  have hdom : Integrable (fun a : X × (X × X) => ‖F ‖a.1‖‖ * (‖g a.2.1‖ * ‖g a.2.2‖))
      (volume.prod (volume.prod volume)) :=
    hF.norm.mul_prod (hg.norm.mul_prod hg.norm)
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with a
  -- the modulus of the integrand is exactly the dominating function
  rw [norm_mul, norm_mul, norm_mul, norm_mul,
      norm_exp_neg_I_mul, norm_exp_I_mul, cnorm_ofReal, cnorm_ofReal, cnorm_ofReal]
  exact le_of_eq (by ring)

end Work.SmallBoxBridge.Resolve
