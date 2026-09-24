import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.FarCx_aux

/-!
# GM §9: the far-sampling crux in the `t`-variable form

`Submission.Work.GM.Affine.FarCx_aux` proves the crux inequality in the normalised variable `u`:
the `‖ψ̂₁‖²`-weighted mass of `u ↦ Σ_ℓ H ℓ e(-ℓu/M₃)` outside `|u| ≤ 2` is at most a constant
times its unweighted mass on `|u| ≤ 2`.

Here we transfer it to the variable `t = u/M₃` in which the paper states the estimate, i.e. for
the trigonometric polynomial `t ↦ Σ_ℓ H ℓ e(ℓ t)` with weight `‖ψ̂₁(K M₃ t)‖²` and window
`|t| ≤ 2/M₃`.  The change of variables `u = M₃ t` scales all three integrals by `M₃⁻¹`, and the
two exponential sums have the same modulus because they are complex conjugates of each other.
-/

open MeasureTheory Complex Finset
open scoped BigOperators FourierTransform Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Affine

noncomputable section

/-- The trigonometric polynomial `t ↦ Σ_{ℓ ∈ s} H ℓ e^{2πi ℓ t}` of the statement. -/
def Pt (s : Finset ℤ) (H : ℤ → ℝ) (t : ℝ) : ℂ :=
  ∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))

/-- **Conjugation identity.**  Evaluating the trigonometric polynomial at `u/M` gives the complex
conjugate of the `Gsum` of `FarCx_aux` at `u`. -/
lemma Pt_eq_conj_Gsum (s : Finset ℤ) (H : ℤ → ℝ) (M u : ℝ) :
    Pt s H (u / M) = (starRingEnd ℂ) (FarCx.Gsum s H M u) := by
  rw [Pt, FarCx.Gsum, map_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_div]
  push_cast
  ring_nf

/-- The moduli of `Pt s H (u/M₃)` and of `FarCx.Gsum s H M₃ u` agree. -/
lemma Pt_norm_eq_Gsum (s : Finset ℤ) (H : ℤ → ℝ) (M u : ℝ) :
    ‖Pt s H (u / M)‖ = ‖FarCx.Gsum s H M u‖ := by
  rw [Pt_eq_conj_Gsum s H M u, Complex.norm_conj]

/-! ## Scaling of the three sets -/

lemma inv_smul_Ioi_two (c : ℝ) (hc : 0 < c) : Set.Ioi (2 / c) = c⁻¹ • Set.Ioi (2 : ℝ) := by
  ext y
  constructor
  · intro hy
    refine ⟨c * y, ?_, ?_⟩
    · simp only [Set.mem_Ioi]
      have h1 : c * (2 / c) = 2 := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hc.ne']
      have h2 := mul_lt_mul_of_pos_left hy hc
      rw [h1] at h2
      exact h2
    · simp only [smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · rintro ⟨t, ht, rfl⟩
    rw [Set.mem_Ioi] at ht
    show 2 / c < c⁻¹ • t
    have h1 : c⁻¹ * 2 = 2 / c := by rw [div_eq_mul_inv, mul_comm]
    rw [← h1]
    simp only [smul_eq_mul]
    exact mul_lt_mul_of_pos_left ht (inv_pos.mpr hc)

lemma inv_smul_Iio_neg_two (c : ℝ) (hc : 0 < c) :
    Set.Iio (-(2 / c)) = c⁻¹ • Set.Iio (-2 : ℝ) := by
  ext y
  constructor
  · intro hy
    refine ⟨c * y, ?_, ?_⟩
    · rw [Set.mem_Iio]
      have h1 : c * (-(2 / c)) = -2 := by
        rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hc.ne']
      have h2 := mul_lt_mul_of_pos_left hy hc
      rw [h1] at h2
      exact h2
    · simp only [smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · rintro ⟨t, ht, rfl⟩
    rw [Set.mem_Iio] at ht
    show c⁻¹ • t < -(2 / c)
    have h1 : c⁻¹ * (-2) = -(2 / c) := by rw [mul_neg, div_eq_mul_inv, mul_comm]
    rw [← h1]
    simp only [smul_eq_mul]
    exact mul_lt_mul_of_pos_left ht (inv_pos.mpr hc)

lemma inv_smul_Icc_two (c : ℝ) (hc : 0 < c) :
    Set.Icc (-(2 / c)) (2 / c) = c⁻¹ • Set.Icc (-2 : ℝ) 2 := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_Icc] at hy
    refine ⟨c * y, ?_, ?_⟩
    · rw [Set.mem_Icc]
      constructor
      · have h1 : c * (-(2 / c)) = -2 := by
          rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hc.ne']
        have h2 := mul_le_mul_of_nonneg_left hy.1 hc.le
        rw [h1] at h2
        exact h2
      · have h1 : c * (2 / c) = 2 := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hc.ne']
        have h2 := mul_le_mul_of_nonneg_left hy.2 hc.le
        rw [h1] at h2
        exact h2
    · simp only [smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · rintro ⟨t, ht, rfl⟩
    rw [Set.mem_Icc] at ht
    show -(2 / c) ≤ c⁻¹ • t ∧ c⁻¹ • t ≤ 2 / c
    simp only [smul_eq_mul]
    constructor
    · have h1 : c⁻¹ * (-2) = -(2 / c) := by rw [mul_neg, div_eq_mul_inv, mul_comm]
      rw [← h1]
      exact mul_le_mul_of_nonneg_left ht.1 (inv_pos.mpr hc).le
    · have h1 : c⁻¹ * 2 = 2 / c := by rw [div_eq_mul_inv, mul_comm]
      rw [← h1]
      exact mul_le_mul_of_nonneg_left ht.2 (inv_pos.mpr hc).le

/-! ## The change of variables on a half-line -/

/-- Substituting `t = y/c` in an integral over `c⁻¹ • X`. -/
lemma setIntegral_inv_smul {c : ℝ} (hc : 0 < c) (X : Set ℝ) (F : ℝ → ℝ) :
    (∫ t in c⁻¹ • X, F t) = c⁻¹ * ∫ y in X, F (c⁻¹ * y) := by
  have h := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume) F X
    (inv_pos.mpr hc)
  rw [Module.finrank_self, pow_one, inv_inv, smul_eq_mul] at h
  have h2 : c⁻¹ * (c * ∫ t in c⁻¹ • X, F t) = ∫ t in c⁻¹ • X, F t := by
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  calc (∫ t in c⁻¹ • X, F t) = c⁻¹ * (c * ∫ t in c⁻¹ • X, F t) := h2.symm
    _ = c⁻¹ * ∫ y in X, F (c⁻¹ * y) := by rw [← h]; simp only [smul_eq_mul]

/-- Crux inequality with explicit parentheses around each integral on the left-hand side (so the two
half-line integrals are ADDED rather than nested): for a nonnegative finitely-supported sequence
`H : ℤ → ℝ` and `M₃ ≥ 1`, the `‖psi1hat K (M₃ ·)‖²`-weighted `L²`-mass of the trigonometric
polynomial `t ↦ Σ_ℓ H ℓ e^{2πiℓt}` on `|t| > 2/M₃` is at most `C` times its unweighted mass on the
window `|t| ≤ 2/M₃`. -/
theorem far_sampling_crux_fixed {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ M₃ : ℝ, 1 ≤ M₃ → ∀ (s : Finset ℤ) (H : ℤ → ℝ),
      (∀ ℓ, 0 ≤ H ℓ) →
      ((∫ t in Set.Ioi (2 / M₃),
          ‖∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖ ^ 2
            * ‖psi1hat K (M₃ * t)‖ ^ 2)
        + (∫ t in Set.Iio (-(2 / M₃)),
          ‖∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖ ^ 2
            * ‖psi1hat K (M₃ * t)‖ ^ 2))
      ≤ C * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃),
          ‖∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖ ^ 2 := by
  obtain ⟨C, hCpos, hcrux⟩ := FarCx.crux_bound hK
  refine ⟨C, hCpos, ?_⟩
  intro M₃ hM₃ s H hH
  have hMpos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hMne : M₃ ≠ 0 := hMpos.ne'
  change ((∫ t in Set.Ioi (2 / M₃), ‖Pt s H t‖ ^ 2 * ‖psi1hat K (M₃ * t)‖ ^ 2)
        + (∫ t in Set.Iio (-(2 / M₃)), ‖Pt s H t‖ ^ 2 * ‖psi1hat K (M₃ * t)‖ ^ 2))
      ≤ C * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), ‖Pt s H t‖ ^ 2
  -- pointwise comparison of the two exponential sums
  have hpt : ∀ u : ℝ, ‖Pt s H (M₃⁻¹ * u)‖ ^ 2 = ‖FarCx.Gsum s H M₃ u‖ ^ 2 := by
    intro u
    rw [show M₃⁻¹ * u = u / M₃ from by rw [div_eq_mul_inv, mul_comm],
      Pt_norm_eq_Gsum s H M₃ u]
  have hpt2 : ∀ u : ℝ, ‖Pt s H (M₃⁻¹ * u)‖ ^ 2 * ‖psi1hat K (M₃ * (M₃⁻¹ * u))‖ ^ 2
      = ‖FarCx.Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2 := by
    intro u
    rw [show M₃ * (M₃⁻¹ * u) = u from by rw [← mul_assoc, mul_inv_cancel₀ hMne, one_mul],
      hpt u]
  -- the three substitution identities
  have hA : (∫ t in Set.Ioi (2 / M₃), ‖Pt s H t‖ ^ 2 * ‖psi1hat K (M₃ * t)‖ ^ 2)
      = M₃⁻¹ * ∫ u in Set.Ioi 2, ‖FarCx.Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2 := by
    rw [inv_smul_Ioi_two M₃ hMpos,
      setIntegral_inv_smul hMpos (Set.Ioi 2)
        (fun t => ‖Pt s H t‖ ^ 2 * ‖psi1hat K (M₃ * t)‖ ^ 2)]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt2 u)
  have hB : (∫ t in Set.Iio (-(2 / M₃)), ‖Pt s H t‖ ^ 2 * ‖psi1hat K (M₃ * t)‖ ^ 2)
      = M₃⁻¹ * ∫ u in Set.Iio (-2), ‖FarCx.Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2 := by
    rw [inv_smul_Iio_neg_two M₃ hMpos,
      setIntegral_inv_smul hMpos (Set.Iio (-2))
        (fun t => ‖Pt s H t‖ ^ 2 * ‖psi1hat K (M₃ * t)‖ ^ 2)]
    congr 1
    exact setIntegral_congr_fun measurableSet_Iio (fun u _ => hpt2 u)
  have hR : (∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), ‖Pt s H t‖ ^ 2)
      = M₃⁻¹ * ∫ u in Set.Icc (-2) 2, ‖FarCx.Gsum s H M₃ u‖ ^ 2 := by
    rw [inv_smul_Icc_two M₃ hMpos,
      setIntegral_inv_smul hMpos (Set.Icc (-2) 2) (fun t => ‖Pt s H t‖ ^ 2)]
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc (fun u _ => hpt u)
  rw [hA, hB, hR]
  have hcr := hcrux M₃ hM₃ s H hH
  calc M₃⁻¹ * (∫ u in Set.Ioi 2, ‖FarCx.Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2)
        + M₃⁻¹ * ∫ u in Set.Iio (-2), ‖FarCx.Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2
      = M₃⁻¹ * ((∫ u in Set.Ioi 2, ‖FarCx.Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2)
          + ∫ u in Set.Iio (-2), ‖FarCx.Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2) := by ring
    _ ≤ M₃⁻¹ * (C * ∫ u in Set.Icc (-2) 2, ‖FarCx.Gsum s H M₃ u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcr (by positivity)
    _ = C * (M₃⁻¹ * ∫ u in Set.Icc (-2) 2, ‖FarCx.Gsum s H M₃ u‖ ^ 2) := by ring

end

end Work.GM.Affine
