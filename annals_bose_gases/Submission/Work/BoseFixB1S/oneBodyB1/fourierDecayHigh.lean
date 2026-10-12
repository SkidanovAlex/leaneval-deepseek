import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.oneBodyB1.fourierDecayHigh`

**High-order Fourier decay of a `C^N` compactly supported function**, the `N`-th order version of
the elementary third-derivative bound `Commons.Analysis.Fourier.norm_fourier_le_of_integral_third_deriv`:

    `∫‖f‖ ≤ A`  and  `∫‖D^N f‖ ≤ A`   ⟹   `‖𝓕 f ξ‖ ≤ 2^N A / (1 + ‖ξ‖)^N`.

It is proved by the standard `N`-fold integration by parts: `𝓕(D^N f)(ξ)` is
`(-2πi ⟪·,ξ⟫)^N 𝓕 f` — Mathlib's `Real.fourier_iteratedFDeriv`, applied to the `N`-tuple
`(u, …, u)` with `u := ‖ξ‖⁻¹ • ξ` — and the Fourier integral is bounded by the `L¹` norm of its
input function (`VectorFourier.norm_fourierIntegral_le_integral_norm`).  The two bounds
`z ≤ A` (from `∫‖f‖`) and `‖ξ‖^N z ≤ A` (from `∫‖D^N f‖`, paying `(2π)^N ≥ 1`) combine into
`z ≤ 2^N A/(1+‖ξ‖)^N`.

This is the analytic engine of the window-decay estimate `winDecayB1`: applied to a window
rescaled so that its derivatives are uniformly bounded, it produces the scale-sharp bound
`‖\hat f(p)‖ ≤ C (ℓd)³ (1 + (ℓd)‖p‖)^{-N}` used by `windowCutAuxB1`.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Work.BoseFixB1S.oneBodyB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Two-bound interpolation.**  If `z ≤ A` and `r^N z ≤ A` with `A ≥ 0`, then
`z ≤ 2^N A / (1+r)^N`. -/
lemma le_of_le_and_mul_pow_le (N : ℕ) (A r z : ℝ) (hA : 0 ≤ A) (hr : 0 ≤ r) (hN : 1 ≤ N)
    (h1 : z ≤ A) (h2 : r ^ N * z ≤ A) : z ≤ 2 ^ N * A / (1 + r) ^ N := by
  rcases le_total r 1 with hr1 | hr1
  · have hpos : 0 < (1 + r) ^ N := by positivity
    have h2N : (1 + r) ^ N ≤ 2 ^ N := by
      have hle : (1 : ℝ) + r ≤ 2 := by linarith
      exact pow_le_pow_left₀ (by positivity) hle N
    rw [le_div_iff₀ hpos]
    calc z * (1 + r) ^ N ≤ A * (1 + r) ^ N := mul_le_mul_of_nonneg_right h1 hpos.le
      _ ≤ A * 2 ^ N := mul_le_mul_of_nonneg_left h2N hA
      _ = 2 ^ N * A := by ring
  · have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
    have hz : z ≤ A / r ^ N := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < r ^ N)]
      calc z * r ^ N = r ^ N * z := by ring
        _ ≤ A := h2
    refine hz.trans ?_
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < r ^ N) (by positivity : (0:ℝ) < (1+r)^N)]
    have hle : (1 + r) ^ N ≤ 2 ^ N * r ^ N := by
      have h2r : (1 : ℝ) + r ≤ 2 * r := by linarith
      calc (1 + r) ^ N ≤ (2 * r) ^ N := pow_le_pow_left₀ (by positivity) h2r N
        _ = 2 ^ N * r ^ N := by rw [mul_pow]
    calc A * (1 + r) ^ N ≤ A * (2 ^ N * r ^ N) := mul_le_mul_of_nonneg_left hle hA
      _ = 2 ^ N * A * r ^ N := by ring

/-- **`N`-th order Fourier decay.**  For `f : ℝ³ → ℂ`, `C^N` with compact support, if
`∫‖f‖ ≤ A` and `∫‖D^N f‖ ≤ A`, then `‖𝓕 f ξ‖ ≤ 2^N A/(1+‖ξ‖)^N` for every frequency `ξ`. -/
theorem norm_fourier_le_of_integral_iteratedFDeriv (N : ℕ) (hN : 1 ≤ N)
    (f : E3 → ℂ) (A : ℝ) (hA : 0 ≤ A) (hf : ContDiff ℝ N f) (hcs : HasCompactSupport f)
    (h0 : ∫ x, ‖f x‖ ≤ A) (hN' : ∫ x, ‖iteratedFDeriv ℝ N f x‖ ≤ A) :
    ∀ ξ : E3, ‖FourierTransform.fourier f ξ‖ ≤ 2 ^ N * A / (1 + ‖ξ‖) ^ N := by
  intro ξ
  have hint : ∀ n, n ≤ N → Integrable (iteratedFDeriv ℝ n f) volume := fun n hn =>
    (hf.continuous_iteratedFDeriv (by exact_mod_cast hn)).integrable_of_hasCompactSupport
      (hcs.iteratedFDeriv n)
  have hb1 : ‖FourierTransform.fourier f ξ‖ ≤ A :=
    (VectorFourier.norm_fourierIntegral_le_integral_norm (𝕜 := ℝ) Real.fourierChar volume
      (innerₗ E3) f ξ).trans h0
  have hb2 : ‖ξ‖ ^ N * ‖FourierTransform.fourier f ξ‖ ≤ A := by
    rcases eq_or_ne ξ 0 with hξ0 | hξ
    · subst hξ0
      rw [norm_zero, zero_pow (by omega : N ≠ 0), zero_mul]
      exact hA
    · have hξpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      have hfourier : (𝓕 (iteratedFDeriv ℝ N f)) =
          fun w => VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w N :=
        Real.fourier_iteratedFDeriv (N := (N : ℕ∞)) (f := f) (n := N)
          (by simpa using hf) (fun n hn => hint n (by exact_mod_cast hn)) le_rfl
      set m : Fin N → E3 := fun _ => (‖ξ‖)⁻¹ • ξ with hm
      have hinner : ∀ i : Fin N, ((-innerSL ℝ) ξ) (m i) = -‖ξ‖ := by
        intro i
        simp only [hm, neg_apply, innerSL_apply_apply, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp
      have hprod : (∏ i : Fin N, ((-innerSL ℝ) ξ) (m i)) = (-‖ξ‖) ^ N := by
        rw [Finset.prod_congr rfl (fun i _ => hinner i)]
        simp [Finset.prod_const, Fintype.card_fin]
      have hval : (𝓕 (iteratedFDeriv ℝ N f)) ξ m =
          (-(2 * (Real.pi : ℂ) * Complex.I)) ^ N •
            (((-‖ξ‖) ^ N : ℝ)) • (𝓕 f) ξ := by
        rw [hfourier, VectorFourier.fourierPowSMulRight_apply, hprod]
      have hc1 : ‖(-(2 * (Real.pi : ℂ) * Complex.I))‖ = 2 * Real.pi := by
        rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
        congr 1
        have h := RCLike.norm_ofReal (K := ℂ) Real.pi
        rwa [abs_of_nonneg Real.pi_pos.le] at h
      have hc2 : ‖(((-‖ξ‖) ^ N : ℝ))‖ = ‖ξ‖ ^ N := by
        rw [Real.norm_eq_abs, abs_pow, abs_neg, abs_of_nonneg (norm_nonneg ξ)]
      have hnorm : ‖(𝓕 (iteratedFDeriv ℝ N f)) ξ m‖
          = (2*Real.pi)^N * ‖ξ‖^N * ‖(𝓕 f) ξ‖ := by
        rw [hval, norm_smul, norm_smul, norm_pow, hc1, hc2]
        ring
      have hmnorm : ∀ i : Fin N, ‖m i‖ = 1 := by
        intro i
        rw [hm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ)),
          inv_mul_cancel₀ (ne_of_gt hξpos)]
      have hleop : ‖(𝓕 (iteratedFDeriv ℝ N f)) ξ m‖ ≤ ‖(𝓕 (iteratedFDeriv ℝ N f)) ξ‖ := by
        have h := ContinuousMultilinearMap.le_opNorm ((𝓕 (iteratedFDeriv ℝ N f)) ξ) m
        simpa [hmnorm] using h
      have hbndN : ‖(𝓕 (iteratedFDeriv ℝ N f)) ξ‖ ≤ A :=
        (VectorFourier.norm_fourierIntegral_le_integral_norm (𝕜 := ℝ) Real.fourierChar volume
          (innerₗ E3) (iteratedFDeriv ℝ N f) ξ).trans hN'
      have hmain : (2*Real.pi)^N * ‖ξ‖^N * ‖(𝓕 f) ξ‖ ≤ A := by
        rw [← hnorm]; exact hleop.trans hbndN
      have h2pi : 1 ≤ (2*Real.pi)^N :=
        one_le_pow₀ (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ 2*Real.pi)
      have hnn : 0 ≤ ‖ξ‖^N * ‖(𝓕 f) ξ‖ :=
        mul_nonneg (pow_nonneg (norm_nonneg ξ) N) (norm_nonneg _)
      nlinarith [hmain, h2pi, hnn]
  exact le_of_le_and_mul_pow_le N A ‖ξ‖ _ hA (norm_nonneg ξ) hN hb1 hb2

end Work.BoseFixB1S.oneBodyB1
