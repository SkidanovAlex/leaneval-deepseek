import Mathlib
import Submission.Work.KMTContract.fourierDecayRefl

open MeasureTheory
open scoped FourierTransform

namespace Work.KMTAreas.A7

/-
# Quadratic decay of the Fourier transform with an explicit constant

`Work.KMTContract.fourierDecayRefl` proves that a `C²` compactly supported `g : ℝ → ℂ` obeys
`∃ C > 0, ∀ x, ‖𝓕 g x‖ ≤ C/(1+|x|)²`; its proof constructs `C = 4 · max ‖g‖₁ ‖g''‖₁ + 1` where
`‖g‖₁ = ∫ y, ‖g y‖` and `‖g''‖₁ = ∫ y, ‖iteratedDeriv 2 g y‖`, and terminates with
`refine ⟨4 * max A B + 1, _, _⟩`. The declaration below simply exposes that explicit constant
(the proof is the body of `fourierDecayRefl` with `A` and `B` unfolded). It is needed because a
bound valid for a family of kernels indexed by `ρ ∈ (0,1]` requires controlling the constant,
which the `∃`-formulation does not allow.
-/
theorem FourierDecayExplicit {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    ∀ x : ℝ, ‖FourierTransform.fourier g x‖ ≤
      (4 * max (∫ y, ‖g y‖) (∫ y, ‖iteratedDeriv 2 g y‖) + 1) / (1 + |x|) ^ 2 := by
  set A := ∫ y, ‖g y‖ with hA
  set B := ∫ y, ‖iteratedDeriv 2 g y‖ with hB
  have hAnn : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun y => norm_nonneg _)
  -- Integrability of `g` and of its first two iterated derivatives.
  have hg0 : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have h2eq : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hcomp2 : HasCompactSupport (iteratedDeriv 2 g) := by
    rw [h2eq]; exact hc.deriv.deriv
  have hg2 : Integrable (iteratedDeriv 2 g) :=
    (hg.continuous_iteratedDeriv 2 (by norm_num)).integrable_of_hasCompactSupport hcomp2
  have hInt : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n g) := by
    intro n hn
    have hn' : n ≤ 2 := by exact_mod_cast hn
    interval_cases n
    · rw [iteratedDeriv_zero]; exact hg0
    · have hc1 : HasCompactSupport (iteratedDeriv 1 g) := by
        rw [iteratedDeriv_one]; exact hc.deriv
      exact (hg.continuous_iteratedDeriv 1 (by norm_num)).integrable_of_hasCompactSupport hc1
    · exact hg2
  -- The Fourier transform of the second derivative.
  have hF2 : 𝓕 (iteratedDeriv 2 g) =
      fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))^2 • 𝓕 g x :=
    Real.fourier_iteratedDeriv (N := 2) (n := 2) hg hInt (by norm_num)
  intro x
  -- `L¹` bound for `g` itself.
  have hbd1 : ‖𝓕 g x‖ ≤ A := by
    rw [hA]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  -- `L¹` bound for the second derivative, transferred to `𝓕 g x`.
  have hF2x : 𝓕 (iteratedDeriv 2 g) x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))^2 • 𝓕 g x := congr_fun hF2 x
  have hnorm : ‖𝓕 (iteratedDeriv 2 g) x‖ = (2 * Real.pi * |x|)^2 * ‖𝓕 g x‖ := by
    rw [hF2x, norm_smul, norm_pow]
    congr 1
    have h1 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h2 : ‖(Real.pi : ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
    have h3 : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal x
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, h1, h2, h3,
      abs_of_nonneg Real.pi_pos.le]
  have hbd2 : (2 * Real.pi * |x|)^2 * ‖𝓕 g x‖ ≤ B := by
    rw [← hnorm, hB]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + |x|)^2)]
  by_cases hx : |x| ≤ 1
  · -- Small `x`: the `L¹` bound for `g` suffices.
    have h4 : (1 + |x|)^2 ≤ 4 := by nlinarith [abs_nonneg x, hx]
    have hstep : ‖𝓕 g x‖ * (1 + |x|)^2 ≤ A * 4 := by
      calc ‖𝓕 g x‖ * (1 + |x|)^2 ≤ A * (1 + |x|)^2 :=
            mul_le_mul_of_nonneg_right hbd1 (by positivity)
        _ ≤ A * 4 := mul_le_mul_of_nonneg_left h4 hAnn
    have hm : A ≤ max A B := le_max_left A B
    linarith
  · -- Large `x`: the `L¹` bound for the second derivative.
    have hx' : 1 < |x| := not_le.mp hx
    have h4 : (1 + |x|)^2 ≤ 4 * x^2 := by nlinarith [abs_nonneg x, hx', sq_abs x]
    have hkey : (2 * Real.pi * |x|)^2 = 4 * Real.pi^2 * x^2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    have hbd2' : 4 * x^2 * ‖𝓕 g x‖ ≤ B := by
      have hpi1 : (1 : ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
      have hmono : 4 * x^2 * ‖𝓕 g x‖ ≤ 4 * Real.pi^2 * x^2 * ‖𝓕 g x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        nlinarith [sq_nonneg x, hpi1]
      calc 4 * x^2 * ‖𝓕 g x‖ ≤ 4 * Real.pi^2 * x^2 * ‖𝓕 g x‖ := hmono
        _ = (2 * Real.pi * |x|)^2 * ‖𝓕 g x‖ := by rw [hkey]
        _ ≤ B := hbd2
    calc ‖𝓕 g x‖ * (1 + |x|)^2 ≤ ‖𝓕 g x‖ * (4 * x^2) :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = 4 * x^2 * ‖𝓕 g x‖ := by ring
      _ ≤ B := hbd2'
      _ ≤ 4 * max A B + 1 := by
          have hm : B ≤ max A B := le_max_right A B
          have hm2 : 0 ≤ max A B := le_max_of_le_left hAnn
          linarith

end Work.KMTAreas.A7
