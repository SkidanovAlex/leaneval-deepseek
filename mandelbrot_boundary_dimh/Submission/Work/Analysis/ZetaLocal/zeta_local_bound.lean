import Mathlib

namespace Work.Analysis.ZetaLocal

/-- Local quantitative estimate used in the Shishikura argument: if `u` is a Lipschitz
map on the disk of radius `1/32` (with constants `C`, `‖u‖ ≤ 2`) and `A = 1 + σ u σ`
has real part `≥ 1/2`, then the "change of coordinate" factor
`1 - σ u τ / (1 + τ u τ)` has positive real part, is non-zero, and differs from the
leading term `1 / (1 + σ u σ)` by at most `(C + 5) ‖τ - σ‖`. -/
theorem zeta_local_bound {u : ℂ → ℂ} {σ τ : ℂ} {C : ℝ}
    (hC : 0 ≤ C) (huσ : ‖u σ‖ ≤ 2) (huτ : ‖u τ‖ ≤ 2)
    (hLip : ‖u σ - u τ‖ ≤ C * ‖σ - τ‖)
    (hτσ : ‖τ - σ‖ ≤ 1 / 64) (hCσ : C * ‖σ‖ ≤ 1) (hσ : ‖σ‖ ≤ 1 / 32)
    (hDnorm : 1 / 2 ≤ ‖1 + σ * u σ‖) (hDre : 1 / 2 ≤ (1 + σ * u σ).re)
    (hDim : |(1 + σ * u σ).im| ≤ 1 / 64 + 1 / 32) :
    0 < (1 - σ * u τ / (1 + τ * u τ)).re ∧
    (1 - σ * u τ / (1 + τ * u τ)) ≠ 0 ∧
    ‖(1 - σ * u τ / (1 + τ * u τ)) * (1 + σ * u σ) - 1‖ ≤ (C + 5) * ‖τ - σ‖ := by
  set A : ℂ := 1 + σ * u σ with hA
  set B : ℂ := 1 + τ * u τ with hB
  set E : ℂ := 1 - σ * u τ / B with hE
  -- `B` is within `3/64` of `A`.
  have hBA : ‖B - A‖ ≤ 3 / 64 := by
    have hBA_eq : B - A = (τ - σ) * u τ + σ * (u τ - u σ) := by rw [hA, hB]; ring
    rw [hBA_eq]
    have t1 : ‖(τ - σ) * u τ‖ ≤ 1 / 32 := by
      rw [norm_mul]
      calc ‖τ - σ‖ * ‖u τ‖ ≤ (1 / 64) * 2 := mul_le_mul hτσ huτ (norm_nonneg (u τ)) (by norm_num)
        _ = 1 / 32 := by norm_num
    have h1 : ‖u τ - u σ‖ ≤ C * ‖τ - σ‖ := by
      rw [norm_sub_rev (u τ) (u σ), ← norm_sub_rev σ τ]
      exact hLip
    have t2 : ‖σ * (u τ - u σ)‖ ≤ 1 / 64 := by
      rw [norm_mul]
      calc ‖σ‖ * ‖u τ - u σ‖ ≤ ‖σ‖ * (C * ‖τ - σ‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg σ)
        _ = C * ‖σ‖ * ‖τ - σ‖ := by ring
        _ ≤ 1 * ‖τ - σ‖ := mul_le_mul_of_nonneg_right hCσ (norm_nonneg _)
        _ ≤ 1 / 64 := by rw [one_mul]; exact hτσ
    have htri := norm_add_le ((τ - σ) * u τ) (σ * (u τ - u σ))
    linarith
  -- hence `B` has positive real part, bounded below.
  have hreB : 29 / 64 ≤ B.re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (B - A))).1
    rw [Complex.sub_re] at h
    linarith [h, hBA, hDre]
  have hnormB : 29 / 64 ≤ ‖B‖ := le_trans hreB (Complex.re_le_norm B)
  have hnum : ‖σ * u τ‖ ≤ 1 / 16 := by
    rw [norm_mul]
    calc ‖σ‖ * ‖u τ‖ ≤ (1 / 32) * 2 := mul_le_mul hσ huτ (norm_nonneg (u τ)) (by norm_num)
      _ = 1 / 16 := by norm_num
  have hBpos : 0 < ‖B‖ := by linarith
  -- `E` is close to `1`.
  have hE1 : ‖E - 1‖ ≤ 4 / 29 := by
    have heq : E - 1 = -(σ * u τ / B) := by rw [hE]; ring
    rw [heq, norm_neg, norm_div]
    rw [div_le_iff₀ hBpos]
    have hb2 : (4/29:ℝ) * (29/64) ≤ (4/29) * ‖B‖ := mul_le_mul_of_nonneg_left hnormB (by norm_num)
    linarith [hnum, hb2]
  have hEre : 0 < E.re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (E - 1))).1
    have h1 : (E - 1).re = E.re - (1:ℂ).re := Complex.sub_re E 1
    have hrw : E.re = 1 + (E - 1).re := by rw [h1, Complex.one_re]; ring
    rw [hrw]
    linarith [h, hE1]
  have hEne : E ≠ 0 := by
    intro hE0
    rw [hE0] at hEre
    simp at hEre
  have hBne : B ≠ 0 := norm_pos_iff.mp hBpos
  -- the algebraic identity `E * A - 1 = ((B - σ u τ) * A - B) / B`
  have hF : E * A - 1 = ((B - σ * u τ) * A - B) / B := by
    rw [hE]; field_simp
  have hFeq : (B - σ * u τ) * A - B = σ * (u σ - u τ) + σ * (τ - σ) * u τ * u σ := by
    rw [hA, hB]; ring
  have t1' : ‖σ * (u σ - u τ)‖ ≤ ‖τ - σ‖ := by
    rw [norm_mul]
    calc ‖σ‖ * ‖u σ - u τ‖ ≤ ‖σ‖ * (C * ‖σ - τ‖) := mul_le_mul_of_nonneg_left hLip (norm_nonneg σ)
      _ = C * ‖σ‖ * ‖τ - σ‖ := by rw [norm_sub_rev σ τ]; ring
      _ ≤ 1 * ‖τ - σ‖ := mul_le_mul_of_nonneg_right hCσ (norm_nonneg _)
      _ = ‖τ - σ‖ := one_mul _
  have t2' : ‖σ * (τ - σ) * u τ * u σ‖ ≤ (1/8) * ‖τ - σ‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    have hp : ‖σ‖ * ‖u τ‖ * ‖u σ‖ ≤ 1/8 := by
      have h1 : ‖σ‖ * ‖u τ‖ ≤ 1/16 := by
        calc ‖σ‖ * ‖u τ‖ ≤ (1/32) * 2 := mul_le_mul hσ huτ (norm_nonneg (u τ)) (by norm_num)
          _ = 1/16 := by norm_num
      calc ‖σ‖ * ‖u τ‖ * ‖u σ‖ ≤ (1/16) * 2 := mul_le_mul h1 huσ (norm_nonneg (u σ)) (by norm_num)
        _ = 1/8 := by norm_num
    calc ‖σ‖ * ‖τ - σ‖ * ‖u τ‖ * ‖u σ‖
        = ‖τ - σ‖ * (‖σ‖ * ‖u τ‖ * ‖u σ‖) := by ring
      _ ≤ ‖τ - σ‖ * (1/8) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = (1/8) * ‖τ - σ‖ := by ring
  have hFnorm : ‖(B - σ * u τ) * A - B‖ ≤ (9/8) * ‖τ - σ‖ := by
    rw [hFeq]
    have htri := norm_add_le (σ * (u σ - u τ)) (σ * (τ - σ) * u τ * u σ)
    linarith
  refine ⟨hEre, hEne, ?_⟩
  rw [hF, norm_div]
  have hdiv : ‖(B - σ * u τ) * A - B‖ / ‖B‖ ≤ ((9/8) * ‖τ - σ‖) / (29/64) :=
    div_le_div₀ (by positivity) hFnorm (by norm_num) hnormB
  calc ‖(B - σ * u τ) * A - B‖ / ‖B‖
      ≤ ((9/8) * ‖τ - σ‖) / (29/64) := hdiv
    _ = (72/29) * ‖τ - σ‖ := by ring_nf
    _ ≤ (C + 5) * ‖τ - σ‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end Work.Analysis.ZetaLocal
