import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Commons.Analysis.Fourier

open scoped FourierTransform InnerProductSpace RealInnerProductSpace
open MeasureTheory

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- Fourier transform of a dilation in a finite-dimensional real inner product space:
the Fourier transform of `x ↦ f (a⁻¹ • x)` is `a ^ dim` times the Fourier transform of `f`
evaluated at `a • ξ`. -/
lemma fourier_comp_inv_smul (f : V → ℂ) {a : ℝ} (ha : 0 < a) (ξ : V) :
    𝓕 (fun x => f (a⁻¹ • x)) ξ = (a ^ Module.finrank ℝ V) • 𝓕 f (a • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hinner : ∀ x : V, ⟪a⁻¹ • x, a • ξ⟫_ℝ = ⟪x, ξ⟫_ℝ := by
    intro x
    rw [real_inner_smul_left, real_inner_smul_right, inv_mul_cancel_left₀ ha.ne']
  have key : (∫ x, 𝐞 (-⟪x, ξ⟫_ℝ) • f (a⁻¹ • x))
      = ∫ x, (fun y => 𝐞 (-⟪y, a • ξ⟫_ℝ) • f y) (a⁻¹ • x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hinner x]
  rw [key, Measure.integral_comp_inv_smul_of_nonneg volume (fun y => 𝐞 (-⟪y, a • ξ⟫_ℝ) • f y) ha.le]

/-- Fourier transform of a translation in a finite-dimensional real inner product space. -/
lemma fourier_comp_sub (g : V → ℂ) (c ξ : V) :
    𝓕 (fun x => g (x - c)) ξ = (𝐞 (-⟪c, ξ⟫_ℝ) : ℂ) • 𝓕 g ξ := by
  rw [Real.fourier_eq, Real.fourier_eq]
  simp only [Circle.smul_def, smul_eq_mul]
  have hpt : ∀ x : V, (𝐞 (-⟪x + c, ξ⟫_ℝ) : ℂ) * g x
      = (𝐞 (-⟪c, ξ⟫_ℝ) : ℂ) * ((𝐞 (-⟪x, ξ⟫_ℝ) : ℂ) * g x) := by
    intro x
    have h1 : -⟪x + c, ξ⟫_ℝ = -⟪x, ξ⟫_ℝ + -⟪c, ξ⟫_ℝ := by
      rw [inner_add_left]; ring
    rw [h1, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  rw [← integral_add_right_eq_self (fun x : V => (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ) * g (x - c)) c]
  simp only [add_sub_cancel_right]
  rw [funext hpt, integral_const_mul]

end General

theorem fourier_scaled_translate {n : ℕ} (χ : EuclideanSpace ℝ (Fin n) → ℝ) (a : ℝ) (ha : 0 < a)
    (c : EuclideanSpace ℝ (Fin n)) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x => ((χ (a⁻¹ • (x - c)) : ℝ) : ℂ)) ξ = (a ^ n : ℂ) * (𝐞 (-⟪c, ξ⟫_ℝ) : ℂ) * 𝓕 (fun x => (χ x : ℂ)) (a • ξ) := by
  change 𝓕 (fun x : EuclideanSpace ℝ (Fin n) =>
      (fun u => (χ (a⁻¹ • u) : ℂ)) (x - c)) ξ
      = (a ^ n : ℂ) * (𝐞 (-⟪c, ξ⟫_ℝ) : ℂ) * 𝓕 (fun x => (χ x : ℂ)) (a • ξ)
  have step1 := fourier_comp_sub (V := EuclideanSpace ℝ (Fin n))
    (fun u => (χ (a⁻¹ • u) : ℂ)) c ξ
  have step2 := fourier_comp_inv_smul (V := EuclideanSpace ℝ (Fin n))
    (fun u => (χ u : ℂ)) ha ξ
  rw [step1, step2, finrank_euclideanSpace, Fintype.card_fin]
  rw [smul_eq_mul]
  have hsmul : ∀ (r : ℝ) (z : ℂ), r • z = (r : ℂ) * z := by
    intro r z; rw [Algebra.smul_def]; rfl
  rw [hsmul, Complex.ofReal_pow]
  ring

end Commons.Analysis.Fourier