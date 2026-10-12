import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Fourier.FourierTransformDeriv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform

/-- Integrability of the norm of an iterated derivative of a `C^3` compactly supported function. -/
private lemma integrable_norm_iteratedFDeriv
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) (hf : ContDiff ℝ 3 f) (hcs : HasCompactSupport f)
    {n : ℕ} (hn : n ≤ 3) :
    Integrable (fun x => ‖iteratedFDeriv ℝ n f x‖) := by
  have hcont : Continuous (iteratedFDeriv ℝ n f) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast hn)
  exact (hcont.integrable_of_hasCompactSupport (hcs.iteratedFDeriv n)).norm

/-- Bound on the integral of the norm of an iterated derivative, in terms of the volume of the
ball containing the support. -/
private lemma integral_norm_iteratedFDeriv_le
    (M R : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hsupp : ∀ x : EuclideanSpace ℝ (Fin 3), f x ≠ 0 → ‖x‖ ≤ R)
    (hb : ∀ j, j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    {j : ℕ} (hj : j ≤ 3) :
    ∫ x, ‖iteratedFDeriv ℝ j f x‖
      ≤ M * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
  have hsub : Function.support (iteratedFDeriv ℝ j f)
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R := by
    refine (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) j).trans ?_
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    simp only [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hsupp x hx
  have hzero : ∀ x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R,
      ‖iteratedFDeriv ℝ j f x‖ = 0 := by
    intro x hx
    have hx' : x ∉ Function.support (iteratedFDeriv ℝ j f) := fun h => hx (hsub h)
    simp only [Function.mem_support, not_not] at hx'
    rw [hx', norm_zero]
  have hfin : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) < ⊤ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R).measure_lt_top
  have h1 : ‖∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R,
      ‖iteratedFDeriv ℝ j f x‖‖
      ≤ M * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) :=
    norm_setIntegral_le_of_norm_le_const hfin
      (fun x _ => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hb j hj x)
  have hnn : 0 ≤ ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R,
      ‖iteratedFDeriv ℝ j f x‖ :=
    setIntegral_nonneg measurableSet_closedBall (fun x _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnn] at h1
  calc ∫ x, ‖iteratedFDeriv ℝ j f x‖
      = ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R,
          ‖iteratedFDeriv ℝ j f x‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ M * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := h1

theorem fourier_decay_of_bounded_support (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
      ContDiff ℝ 3 f → HasCompactSupport f →
      (∀ x : EuclideanSpace ℝ (Fin 3), f x ≠ 0 → ‖x‖ ≤ R) →
      (∀ x, ‖f x‖ ≤ M) →
      (∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ M) →
      (∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M) →
      (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ M) →
      ∀ ξ : EuclideanSpace ℝ (Fin 3),
        ‖FourierTransform.fourier f ξ‖ ≤ C / (1 + ‖ξ‖) ^ 3 := by
  set D : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) with hD
  have hDnn : 0 ≤ D := by
    rw [hD]; exact measureReal_nonneg
  refine ⟨256 * M * D, by nlinarith, ?_⟩
  intro f hf hcs hsupp hb0 hb1 hb2 hb3 ξ
  have hb : ∀ j, j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M := by
    intro j hj x
    interval_cases j
    · simpa only [norm_iteratedFDeriv_zero] using hb0 x
    · exact hb1 x
    · exact hb2 x
    · exact hb3 x
  have hint : ∀ j, j ≤ 3 → ∫ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M * D := by
    intro j hj
    rw [hD]
    exact integral_norm_iteratedFDeriv_le M R f hsupp hb hj
  -- low frequency bound
  have hlow : ‖FourierTransform.fourier f ξ‖ ≤ M * D := by
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume
      (innerₗ (EuclideanSpace ℝ (Fin 3))) f ξ).trans ?_
    have := hint 0 (by norm_num)
    simpa only [norm_iteratedFDeriv_zero] using this
  by_cases hξ : ‖ξ‖ ≤ 1
  · rw [le_div_iff₀ (by positivity)]
    have hmul : ‖FourierTransform.fourier f ξ‖ * (1 + ‖ξ‖) ^ 3 ≤ (M * D) * (1 + ‖ξ‖) ^ 3 :=
      mul_le_mul_of_nonneg_right hlow (by positivity)
    have h2 : (1 + ‖ξ‖) ^ 3 ≤ 256 := by
      have hle : 1 + ‖ξ‖ ≤ 2 := by linarith [norm_nonneg ξ]
      nlinarith [hle, norm_nonneg ξ, sq_nonneg (1 + ‖ξ‖)]
    have h3 : (M * D) * (1 + ‖ξ‖) ^ 3 ≤ (M * D) * 256 :=
      mul_le_mul_of_nonneg_left h2 (by nlinarith [hM, hDnn])
    nlinarith [hmul, h3]
  · rw [not_le] at hξ
    have hξpos : 0 < ‖ξ‖ := lt_trans zero_lt_one hξ
    set u : EuclideanSpace ℝ (Fin 3) := (‖ξ‖)⁻¹ • ξ with hu
    have hu_norm : ‖u‖ = 1 := by
      rw [hu, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ))]
      exact inv_mul_cancel₀ (ne_of_gt hξpos)
    have hu_inner : inner ℝ u ξ = ‖ξ‖ := by
      rw [hu, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    have hif : ∀ k n : ℕ, (k : ℕ∞) ≤ (0 : ℕ∞) → (n : ℕ∞) ≤ (3 : ℕ∞) →
        Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) := by
      intro k n hk hn
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      simpa only [pow_zero, one_mul] using
        integrable_norm_iteratedFDeriv f hf hcs (by exact_mod_cast hn)
    have hkey := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
      (L := innerSL ℝ) (f := f) (K := (0 : ℕ∞)) (N := (3 : ℕ∞)) hf hif
      (k := 0) (n := 3) le_rfl le_rfl u ξ
    have hkey' : ‖ξ‖ ^ 3 * ‖FourierTransform.fourier f ξ‖
        ≤ 8 * (∑ p ∈ Finset.range 1 ×ˢ Finset.range 4,
              ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) := by
      rw [norm_iteratedFDeriv_zero, innerSL_apply_apply, hu_inner,
        abs_of_nonneg (norm_nonneg ξ), hu_norm] at hkey
      have hc : (2 * ((0 : ℕ) : ℝ) + 2) ^ (3 : ℕ) = 8 := by norm_num
      simp only [one_pow, mul_one, one_mul, pow_zero, hc] at hkey
      exact hkey
    have hsum : (∑ p ∈ Finset.range 1 ×ˢ Finset.range 4,
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) ≤ 4 * (M * D) := by
      calc (∑ p ∈ Finset.range 1 ×ˢ Finset.range 4,
              ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖)
          ≤ ∑ p ∈ Finset.range 1 ×ˢ Finset.range 4, (M * D) := by
            apply Finset.sum_le_sum
            intro p hp
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
            have hp1' : p.1 = 0 := Nat.lt_one_iff.mp hp.1
            simp only [hp1', pow_zero, one_mul]
            exact hint p.2 (by omega)
        _ = 4 * (M * D) := by
            rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range]
            norm_num
    have hmain : ‖ξ‖ ^ 3 * ‖FourierTransform.fourier f ξ‖ ≤ 32 * M * D := by
      nlinarith [hkey', hsum]
    have hξc : (0 : ℝ) < ‖ξ‖ ^ 3 := pow_pos hξpos 3
    have hdec : ‖FourierTransform.fourier f ξ‖ ≤ 32 * M * D / ‖ξ‖ ^ 3 := by
      rw [le_div_iff₀ hξc]
      nlinarith [hmain]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖ξ‖) ^ 3)]
    have h8 : (1 + ‖ξ‖) ^ 3 ≤ 8 * ‖ξ‖ ^ 3 := by
      have hle : 1 + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith [hξ]
      have h1 : 0 ≤ 1 + ‖ξ‖ := by positivity
      have h := pow_le_pow_left₀ h1 hle 3
      rw [mul_pow] at h
      norm_num at h
      exact h
    have h32 : 0 ≤ 32 * M * D := by nlinarith [hM, hDnn]
    calc ‖FourierTransform.fourier f ξ‖ * (1 + ‖ξ‖) ^ 3
        ≤ (32 * M * D / ‖ξ‖ ^ 3) * (1 + ‖ξ‖) ^ 3 :=
          mul_le_mul_of_nonneg_right hdec (by positivity)
      _ = 32 * M * D * ((1 + ‖ξ‖) ^ 3 / ‖ξ‖ ^ 3) := by
          field_simp
      _ ≤ 32 * M * D * 8 := by
          apply mul_le_mul_of_nonneg_left _ h32
          rw [div_le_iff₀ hξc]
          exact h8
      _ = 256 * M * D := by ring

end Commons.Analysis.Fourier