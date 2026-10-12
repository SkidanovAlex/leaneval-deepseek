import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.integrable_mul_kinFT_re`

The `p`-convention Fourier transform `kinFT u p = ∫_y e^{−i⟪p,y⟫} u y dy` is bounded uniformly in
`p` by the `L¹`-norm of `u` (`‖kinFT u p‖ ≤ ∫ ‖u y‖`), and it is a.e. strongly measurable whenever
`u` is.  Consequently, for a radial weight `F(‖·‖) ∈ L¹(ℝ³)` and any two `L¹` functions `g, h`, the
product `F(‖p‖)·Re(kinFT g p · conj(kinFT h p))` is integrable: the second factor is bounded by
`‖g‖₁‖h‖₁`, so the integrand is dominated by a constant multiple of `|F(‖p‖)|`, which is
integrable. -/

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

/-- `kinFT` is a.e. strongly measurable as soon as its argument is: it is the Bochner integral of a
jointly strongly measurable integrand. -/
lemma kinFT_aeStronglyMeasurable {u : ℝ³ → ℂ} (hu : AEStronglyMeasurable u) :
    AEStronglyMeasurable (Submission.BoseGases.kinFT u) := by
  have hcont : Continuous
      (fun z : ℝ³ × ℝ³ => Complex.exp (-(Complex.I * (inner ℝ z.1 z.2 : ℂ)))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_inner)).neg
  have hjoint : AEStronglyMeasurable
      (fun z : ℝ³ × ℝ³ => Complex.exp (-(Complex.I * (inner ℝ z.1 z.2 : ℂ))) * u z.2)
      (volume.prod volume) :=
    (hcont.aestronglyMeasurable).mul hu.comp_snd
  have h2 := (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := volume) (E := ℂ) hjoint)
  rw [show Submission.BoseGases.kinFT u
      = (fun x : ℝ³ => ∫ y, Complex.exp (-(Complex.I * (inner ℝ x y : ℂ))) * u y) from rfl]
  exact h2

/-- The `p`-convention Fourier transform is bounded by the `L¹`-norm of its argument. -/
lemma norm_kinFT_le_integral_norm (u : ℝ³ → ℂ) (p : ℝ³) :
    ‖Submission.BoseGases.kinFT u p‖ ≤ ∫ y, ‖u y‖ := by
  rw [Submission.BoseGases.kinFT]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [norm_mul, Complex.norm_exp]
  simp

theorem integrable_mul_kinFT_re {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    {g h : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : MeasureTheory.Integrable g)
    (hh : MeasureTheory.Integrable h) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖ *
      (Submission.BoseGases.kinFT g p * star (Submission.BoseGases.kinFT h p)).re) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ³ => (Submission.BoseGases.kinFT g p *
        star (Submission.BoseGases.kinFT h p)).re) :=
    Complex.continuous_re.comp_aestronglyMeasurable
      ((kinFT_aeStronglyMeasurable hg.aestronglyMeasurable).mul
        (kinFT_aeStronglyMeasurable hh.aestronglyMeasurable).star)
  refine hFi.mul_bdd (c := (∫ y, ‖g y‖) * (∫ y, ‖h y‖)) hmeas ?_
  refine Filter.Eventually.of_forall fun p => ?_
  rw [Real.norm_eq_abs]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_star]
  exact mul_le_mul (norm_kinFT_le_integral_norm g p) (norm_kinFT_le_integral_norm h p)
    (norm_nonneg _) (integral_nonneg fun y => norm_nonneg _)

end Work.OneBodyKin
