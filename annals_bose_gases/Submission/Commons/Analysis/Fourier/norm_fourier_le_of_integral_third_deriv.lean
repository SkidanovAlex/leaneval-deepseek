import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace Real

private lemma le_of_le_and_mul_pow_le (A r z : ℝ) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (h1 : z ≤ A) (h2 : r ^ 3 * z ≤ A) : z ≤ 8 * A / (1 + r) ^ 3 := by
  rcases le_total r 1 with hr1 | hr1
  · have hpos : 0 < (1 + r) ^ 3 := by positivity
    have h8 : (1 + r) ^ 3 ≤ 8 := by
      have hle : (1 : ℝ) + r ≤ 2 := by linarith
      calc (1 + r) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by positivity) hle 3
        _ = 8 := by norm_num
    rw [le_div_iff₀ hpos]
    calc z * (1 + r) ^ 3 ≤ A * (1 + r) ^ 3 := mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      _ ≤ A * 8 := mul_le_mul_of_nonneg_left h8 hA
      _ = 8 * A := by ring
  · have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
    have hz : z ≤ A / r ^ 3 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < r ^ 3)]
      calc z * r ^ 3 = r ^ 3 * z := by ring
        _ ≤ A := h2
    refine hz.trans ?_
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < r ^ 3) (by positivity : (0:ℝ) < (1+r)^3)]
    have hle : (1 + r) ^ 3 ≤ 8 * r ^ 3 := by
      have h2r : (1 : ℝ) + r ≤ 2 * r := by linarith
      calc (1 + r) ^ 3 ≤ (2 * r) ^ 3 := pow_le_pow_left₀ (by positivity) h2r 3
        _ = 8 * r ^ 3 := by ring
    nlinarith [hA, hle]

theorem norm_fourier_le_of_integral_third_deriv (f : EuclideanSpace ℝ (Fin 3) → ℂ) (A : ℝ)
    (hA : 0 ≤ A) (hf : ContDiff ℝ 3 f) (hcs : HasCompactSupport f)
    (h0 : ∫ x, ‖f x‖ ≤ A) (h3 : ∫ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ A) :
    ∀ ξ : EuclideanSpace ℝ (Fin 3),
      ‖FourierTransform.fourier f ξ‖ ≤ 8 * A / (1 + ‖ξ‖) ^ 3 := by
  intro ξ
  have hint : ∀ n, n ≤ 3 → Integrable (iteratedFDeriv ℝ n f) volume := fun n hn =>
    (ContDiff.continuous_iteratedFDeriv (𝕜 := ℝ) (m := n) (n := (3 : WithTop ℕ∞))
      (by exact_mod_cast hn) hf).integrable_of_hasCompactSupport (hcs.iteratedFDeriv n)
  have hb1 : ‖FourierTransform.fourier f ξ‖ ≤ A := by
    have h := VectorFourier.norm_fourierIntegral_le_integral_norm (𝕜 := ℝ) Real.fourierChar volume
      (innerₗ (EuclideanSpace ℝ (Fin 3))) f ξ
    exact h.trans h0
  have hb2 : ‖ξ‖ ^ 3 * ‖FourierTransform.fourier f ξ‖ ≤ A := by
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp [hA]
    · have hξpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      have hfourier : (𝓕 (iteratedFDeriv ℝ 3 f)) =
          fun w => VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w 3 :=
        Real.fourier_iteratedFDeriv (N := (3:ℕ∞)) (f := f) (n := 3)
          (by norm_num; exact hf) (fun n hn => hint n (by exact_mod_cast hn)) le_rfl
      set m : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun _ => (‖ξ‖)⁻¹ • ξ with hm
      have hm_apply : ∀ i, m i = (‖ξ‖)⁻¹ • ξ := fun i => rfl
      have hinner : ∀ i : Fin 3, ((-innerSL ℝ) ξ) (m i) = -‖ξ‖ := by
        intro i
        simp only [hm_apply i, neg_apply, innerSL_apply_apply, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp
      have hprod : (∏ i : Fin 3, ((-innerSL ℝ) ξ) (m i)) = -(‖ξ‖ ^ 3) := by
        rw [Finset.prod_congr rfl (fun i _ => hinner i)]
        simp [Finset.prod_const, Fintype.card_fin]
        ring
      have hval : (𝓕 (iteratedFDeriv ℝ 3 f)) ξ m =
          (-(2 * π * I)) ^ 3 • (∏ i : Fin 3, ((-innerSL ℝ) ξ) (m i)) • (𝓕 f) ξ := by
        rw [hfourier, VectorFourier.fourierPowSMulRight_apply]
      have hnorm1 : ‖(-(2 * (π:ℂ) * I)) ^ 3‖ = (2*π)^3 := by
        rw [norm_pow, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_of_nonneg Real.pi_nonneg, Complex.norm_two]
      have hnorm2 : ‖(-(‖ξ‖ ^ 3) : ℝ)‖ = ‖ξ‖ ^ 3 := by
        rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3)]
      have hnorm : ‖(𝓕 (iteratedFDeriv ℝ 3 f)) ξ m‖ = (2*π)^3 * ‖ξ‖^3 * ‖(𝓕 f) ξ‖ := by
        rw [hval, hprod, norm_smul, norm_smul, hnorm1, hnorm2]
        ring
      have hmnorm : ∀ i : Fin 3, ‖m i‖ = 1 := by
        intro i
        rw [hm_apply i, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ)),
          inv_mul_cancel₀ (ne_of_gt hξpos)]
      have hleop : ‖(𝓕 (iteratedFDeriv ℝ 3 f)) ξ m‖ ≤ ‖(𝓕 (iteratedFDeriv ℝ 3 f)) ξ‖ := by
        have h := ContinuousMultilinearMap.le_opNorm ((𝓕 (iteratedFDeriv ℝ 3 f)) ξ) m
        simpa [hmnorm] using h
      have hbnd3 : ‖(𝓕 (iteratedFDeriv ℝ 3 f)) ξ‖ ≤ A := by
        have h := VectorFourier.norm_fourierIntegral_le_integral_norm (𝕜 := ℝ) Real.fourierChar volume
          (innerₗ (EuclideanSpace ℝ (Fin 3))) (iteratedFDeriv ℝ 3 f) ξ
        exact h.trans h3
      have hmain : (2*π)^3 * ‖ξ‖^3 * ‖(𝓕 f) ξ‖ ≤ A := by
        rw [← hnorm]
        exact hleop.trans hbnd3
      have h2pi : 1 ≤ (2*π)^3 := by
        have h3p : (1:ℝ) ≤ 2*π := by linarith [Real.pi_gt_three]
        calc (1:ℝ) = 1^3 := by ring
          _ ≤ (2*π)^3 := pow_le_pow_left₀ (by norm_num) h3p 3
      have hnn : 0 ≤ ‖ξ‖^3 * ‖(𝓕 f) ξ‖ :=
        mul_nonneg (pow_nonneg (norm_nonneg ξ) 3) (norm_nonneg _)
      calc ‖ξ‖^3 * ‖(𝓕 f) ξ‖ ≤ (2*π)^3 * (‖ξ‖^3 * ‖(𝓕 f) ξ‖) := by nlinarith [h2pi, hnn]
        _ = (2*π)^3 * ‖ξ‖^3 * ‖(𝓕 f) ξ‖ := by ring
        _ ≤ A := hmain
  exact le_of_le_and_mul_pow_le A ‖ξ‖ _ hA (norm_nonneg ξ) hb1 hb2

end Commons.Analysis.Fourier