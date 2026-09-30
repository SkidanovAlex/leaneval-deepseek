import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The `2πi`-normalized complex exponential is the real Fourier character. -/
lemma exp_two_pi_I_eq_fourierChar (a : ℝ) :
    Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * (a : ℂ)) = (Real.fourierChar a : ℂ) := by
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The `2πi`-normalized exponential has unit norm. -/
lemma norm_exp_two_pi_I (a : ℝ) :
    ‖Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * (a : ℂ))‖ = 1 := by
  rw [exp_two_pi_I_eq_fourierChar, Circle.norm_coe]

/-- Multiplicativity of the `2πi`-normalized exponential. -/
lemma exp_two_pi_I_mul_add (a b : ℝ) :
    Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * (a : ℂ))
      * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * (b : ℂ))
    = Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((a + b : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Continuity of the `2πi`-normalized exponential. -/
lemma continuous_exp_two_pi_I :
    Continuous (fun a : ℝ => Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * (a : ℂ))) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem fourierIntegral_mul_measure_eq_zero (n : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (S : Set (EuclideanSpace ℝ (Fin n))) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hφ : ∀ ξ, ρ < ‖ξ‖ →
      ∫ x, φ x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) = 0)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) [MeasureTheory.IsFiniteMeasure μ]
    (hμ : μ Sᶜ = 0) (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : ∀ x, g x = ∫ η, Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x η : ℝ) : ℂ)) ∂μ)
    {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ∀ s ∈ S, ρ < ‖ξ - s‖) :
    ∫ x, (φ x * g x) * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) = 0 := by
  -- μ is supported on `S`
  have hS_ae : ∀ᵐ η ∂μ, η ∈ S := by
    rw [MeasureTheory.ae_iff]
    have : {a : EuclideanSpace ℝ (Fin n) | ¬ a ∈ S} = Sᶜ := by ext a; simp
    rw [this]; exact hμ
  -- the integrand of the double integral
  set F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℂ := fun x η =>
    φ x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x η : ℝ) : ℂ))
      * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) with hF
  -- combining the two exponentials
  have hF_eq : ∀ x η, F x η
      = φ x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x (ξ - η))) : ℝ)) := by
    intro x η
    have harg : (inner ℝ x η : ℝ) + (-(inner ℝ x ξ)) = -(inner ℝ x (ξ - η)) := by
      rw [inner_sub_right]; ring
    simp only [hF]
    rw [mul_assoc, exp_two_pi_I_mul_add, harg]
  -- integrability on the product
  have hcont_lam : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      φ p.1 * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ p.1 p.2 : ℝ) : ℂ))
        * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ p.1 ξ)) : ℝ))) := by
    refine Continuous.mul (Continuous.mul (φ.continuous.comp continuous_fst) ?_) ?_
    · exact continuous_exp_two_pi_I.comp continuous_inner
    · exact continuous_exp_two_pi_I.comp
        (Continuous.neg (continuous_inner.comp (continuous_fst.prodMk continuous_const)))
  have hcontF : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => F p.1 p.2) := by
    simp only [hF]
    exact hcont_lam
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod μ) :=
    hcontF.aestronglyMeasurable
  have hInt : Integrable (Function.uncurry F) (volume.prod μ) := by
    rw [MeasureTheory.integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards with x
      have hcx : Continuous (fun η : EuclideanSpace ℝ (Fin n) => F x η) := by
        simp only [hF]
        refine Continuous.mul (Continuous.mul continuous_const ?_) continuous_const
        exact continuous_exp_two_pi_I.comp (continuous_const.inner continuous_id)
      refine MeasureTheory.Integrable.of_bound hcx.aestronglyMeasurable (‖φ x‖)
        (Filter.Eventually.of_forall (fun η => ?_))
      change ‖F x η‖ ≤ ‖φ x‖
      simp only [hF]
      rw [norm_mul, norm_mul, norm_exp_two_pi_I, norm_exp_two_pi_I, mul_one, mul_one]
    · have hnorm_eq : (fun x => ∫ η, ‖F x η‖ ∂μ) = fun x => ‖φ x‖ * μ.real Set.univ := by
        funext x
        have hb : ∀ η, ‖F x η‖ = ‖φ x‖ := by
          intro η
          simp only [hF]
          rw [norm_mul, norm_mul, norm_exp_two_pi_I, norm_exp_two_pi_I, mul_one, mul_one]
        rw [show (fun η => ‖F x η‖) = (fun _ => ‖φ x‖) from funext hb]
        rw [MeasureTheory.integral_const, smul_eq_mul, mul_comm]
      change Integrable (fun x => ∫ η, ‖F x η‖ ∂μ) volume
      rw [hnorm_eq]
      exact (φ.integrable.norm).mul_const _
  -- pointwise identification of the target integral with the inner integral
  have hpoint : ∀ x, (φ x * g x) * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ))
      = ∫ η, F x η ∂μ := by
    intro x
    calc (φ x * g x) * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ))
        = (φ x * ∫ η, Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x η : ℝ) : ℂ)) ∂μ)
            * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) := by rw [hg x]
      _ = (∫ η, φ x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x η : ℝ) : ℂ)) ∂μ)
            * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) := by
            rw [MeasureTheory.integral_const_mul]
      _ = ∫ η, (φ x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x η : ℝ) : ℂ)))
              * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) ∂μ := by
            rw [MeasureTheory.integral_mul_const]
      _ = ∫ η, F x η ∂μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with η
            simp only [hF]
  -- Fubini
  have hfub := MeasureTheory.integral_integral_swap hInt
  -- the inner x-integral vanishes μ-a.e.
  have hzero : ∀ᵐ η ∂μ, (∫ x, F x η ∂volume) = 0 := by
    filter_upwards [hS_ae] with η hη
    have : (∫ x, F x η ∂volume)
        = ∫ x, φ x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x (ξ - η))) : ℝ)) ∂volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact hF_eq x η
    rw [this]
    exact hφ (ξ - η) (hξ η hη)
  have hfinal : ∫ η, (∫ x, F x η ∂volume) ∂μ = 0 := by
    rw [MeasureTheory.integral_congr_ae hzero]
    simp
  calc ∫ x, (φ x * g x) * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) ∂volume
      = ∫ x, (∫ η, F x η ∂μ) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          exact hpoint x
    _ = ∫ η, (∫ x, F x η ∂volume) ∂μ := hfub
    _ = 0 := hfinal

end Commons.Analysis.Fourier