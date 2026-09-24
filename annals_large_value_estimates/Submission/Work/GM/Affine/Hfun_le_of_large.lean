import Mathlib
import Submission.Work.GM.Affine.region_II_vocab

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

namespace Work.GM.Affine

/-- Pointwise decay bound on `Fhat f` in the form used below: for every `ξ ≠ 0`,
`‖Fhat f ξ‖ ≤ max (c 3 1 * Λ) 0 * T * (T/|ξ|)^3`. -/
private lemma Fhat_le_of_decay {c : ℕ → ℝ → ℝ} {T Λ : ℝ} (hT : 1 ≤ T) {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) :
    ∀ ξ : ℝ, ξ ≠ 0 → ‖Fhat f ξ‖ ≤ max (c 3 1 * Λ) 0 * T * (T / |ξ|) ^ 3 := by
  intro ξ hξ
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hξabs : 0 < |ξ| := abs_pos.mpr hξ
  have h := hdec 3 1 one_pos ξ hξ
  rw [Real.rpow_one] at h
  have hV : 0 < T * (T / |ξ|) ^ 3 :=
    mul_pos hTpos (pow_pos (div_pos hTpos hξabs) 3)
  calc ‖Fhat f ξ‖ ≤ c 3 1 * T * (T / |ξ|) ^ 3 * Λ := h
    _ = (c 3 1 * Λ) * (T * (T / |ξ|) ^ 3) := by ring
    _ ≤ max (c 3 1 * Λ) 0 * (T * (T / |ξ|) ^ 3) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hV.le
    _ = max (c 3 1 * Λ) 0 * T * (T / |ξ|) ^ 3 := by ring

theorem Hfun_le_of_large {c : ℕ → ℝ → ℝ} {T Λ : ℝ} (hT : 1 ≤ T)
    {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) (hM₃ : 1 ≤ M₃) {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (ℓ : ℤ) (hℓ : 4 ≤ |ℓ|) (τ : ℝ) (hτ : τ ∈ Set.Icc (-2:ℝ) 2) :
    ‖Hfun f M₂ M₃ ℓ τ‖ ≤
      (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (8 * max (c 3 1 * Λ) 0 * T ^ 4) / (((|ℓ| : ℤ)) : ℝ) ^ 3 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hAeq0 : ((|ℓ| : ℤ) : ℝ) = |(ℓ : ℝ)| := Int.cast_abs
  have hAge40 : (4:ℝ) ≤ ((|ℓ| : ℤ) : ℝ) := by exact_mod_cast hℓ
  let D : ℝ := max (c 3 1 * Λ) 0
  let A : ℝ := ((|ℓ| : ℤ) : ℝ)
  have hDnn : 0 ≤ D := le_max_right _ _
  have hcD : c 3 1 * Λ ≤ D := le_max_left _ _
  have hAeq : A = |(ℓ : ℝ)| := hAeq0
  have hAge4 : (4:ℝ) ≤ A := hAge40
  have hApos : 0 < A := by linarith
  have hpoint := Fhat_le_of_decay hT hdec
  have hτabs : |τ| ≤ 2 := abs_le.mpr (Set.mem_Icc.mp hτ)
  have hτM : |τ / M₃| ≤ 2 := by
    rw [abs_div, abs_of_pos hM₃pos, div_le_iff₀ hM₃pos]
    nlinarith [hτabs, hM₃]
  have hy_abs : A / 2 ≤ |(ℓ : ℝ) + τ / M₃| := by
    have h1 : |(ℓ : ℝ)| ≤ |(ℓ : ℝ) + τ / M₃| + |τ / M₃| := by
      have h := abs_add_le ((ℓ : ℝ) + τ / M₃) (-(τ / M₃))
      rw [show (ℓ : ℝ) + τ / M₃ + -(τ / M₃) = (ℓ : ℝ) from by ring, abs_neg] at h
      exact h
    have h2 : A ≤ |(ℓ : ℝ) + τ / M₃| + 2 := by rw [hAeq]; linarith
    linarith [hAge4, h2]
  have hyabs_pos : 0 < |(ℓ : ℝ) + τ / M₃| := lt_of_lt_of_le (by linarith : 0 < A / 2) hy_abs
  have hy0 : |(ℓ : ℝ) + τ / M₃| ≠ 0 := ne_of_gt hyabs_pos
  have hyne : (ℓ : ℝ) + τ / M₃ ≠ 0 := abs_pos.mp hyabs_pos
  have hterm : ∀ m ∈ R2 M₂,
      (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ≤ 8 * D * T ^ 4 / A ^ 3 := by
    intro m hm
    have hm1 : (1:ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have hm1R : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    have hmpos : 0 < (m:ℝ) := lt_of_lt_of_le zero_lt_one hm1R
    have hm0 : (m:ℝ) ≠ 0 := ne_of_gt hmpos
    have hmyne : (m:ℝ) * ((ℓ : ℝ) + τ / M₃) ≠ 0 := mul_ne_zero hm0 hyne
    have hb := hpoint ((m : ℝ) * ((ℓ : ℝ) + τ / M₃)) hmyne
    have hmm2 : (1:ℝ) ≤ (m:ℝ)^2 := by nlinarith [hm1R, sq_nonneg ((m:ℝ) - 1)]
    have hkey : A^3 ≤ 8 * ((m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3) := by
      have h1 : (A/2)^3 ≤ |(ℓ : ℝ) + τ / M₃|^3 :=
        pow_le_pow_left₀ (by linarith : 0 ≤ A/2) hy_abs 3
      have h3 : |(ℓ : ℝ) + τ / M₃|^3 ≤ (m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3 :=
        le_mul_of_one_le_left (pow_nonneg (abs_nonneg _) 3) hmm2
      calc A^3 = 8 * (A/2)^3 := by ring
        _ ≤ 8 * |(ℓ : ℝ) + τ / M₃|^3 := by linarith
        _ ≤ 8 * ((m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3) := by linarith
    have hdt : 0 ≤ D * T^4 := mul_nonneg hDnn (pow_nonneg hTpos.le 4)
    have hA3pos : 0 < A^3 := pow_pos hApos 3
    have hden : 0 < (m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3 :=
      mul_pos (pow_pos hmpos 2) (pow_pos hyabs_pos 3)
    have heq : (m:ℝ) * (D * T * (T / |(m:ℝ) * ((ℓ : ℝ) + τ / M₃)|)^3)
        = D * T^4 / ((m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3) := by
      rw [abs_mul, abs_of_pos hmpos]
      field_simp
    have hle : D * T^4 / ((m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3) ≤ 8 * D * T^4 / A^3 := by
      rw [div_le_div_iff₀ hden hA3pos]
      calc D * T^4 * A^3 ≤ D * T^4 * (8 * ((m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3)) :=
            mul_le_mul_of_nonneg_left hkey hdt
        _ = 8 * D * T^4 * ((m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3) := by ring
    calc (m:ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖
        ≤ (m:ℝ) * (D * T * (T / |(m:ℝ) * ((ℓ : ℝ) + τ / M₃)|)^3) :=
            mul_le_mul_of_nonneg_left hb hmpos.le
      _ = D * T^4 / ((m:ℝ)^2 * |(ℓ : ℝ) + τ / M₃|^3) := heq
      _ ≤ 8 * D * T^4 / A^3 := hle
  have hsum1 : ‖Hfun f M₂ M₃ ℓ τ‖ ≤
      ∑ m ∈ R2 M₂, (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ := by
    have h1 : Hfun f M₂ M₃ ℓ τ
        = ∑ m ∈ R2 M₂, ((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃)) := rfl
    rw [h1]
    calc ‖∑ m ∈ R2 M₂, ((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖
        ≤ ∑ m ∈ R2 M₂, ‖((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ :=
            norm_sum_le _ _
      _ = ∑ m ∈ R2 M₂, (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          have hm1 : (1:ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
          have hm1R : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
          rw [norm_mul, show ‖((m : ℝ) : ℂ)‖ = |(m:ℝ)| from by simp,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ))]
  have hsum2 : ∑ m ∈ R2 M₂, (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖
      ≤ (R2 M₂).card * (8 * D * T ^ 4 / A ^ 3) := by
    calc ∑ m ∈ R2 M₂, (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖
        ≤ ∑ m ∈ R2 M₂, (8 * D * T ^ 4 / A ^ 3) := Finset.sum_le_sum hterm
      _ = (R2 M₂).card * (8 * D * T ^ 4 / A ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((R2 M₂).card : ℝ) ≤ ∑ m ∈ R2 M₂, (m : ℝ) := by
    have h1 : ((R2 M₂).card : ℝ) = ∑ m ∈ R2 M₂, (1:ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1]
    exact Finset.sum_le_sum (fun m hm => by
      have hm1 : (1:ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      exact_mod_cast hm1)
  have hc0 : 0 ≤ 8 * D * T ^ 4 / A ^ 3 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hDnn) (pow_nonneg hTpos.le 4)) (pow_nonneg hApos.le 3)
  have hsum3 : (R2 M₂).card * (8 * D * T ^ 4 / A ^ 3) ≤
      (∑ m ∈ R2 M₂, (m : ℝ)) * (8 * D * T ^ 4 / A ^ 3) :=
    mul_le_mul_of_nonneg_right hcard hc0
  have hfinal : ‖Hfun f M₂ M₃ ℓ τ‖ ≤ (∑ m ∈ R2 M₂, (m : ℝ)) * (8 * D * T ^ 4 / A ^ 3) :=
    le_trans hsum1 (le_trans hsum2 hsum3)
  have hconv : (∑ m ∈ R2 M₂, (m : ℝ)) * (8 * D * T ^ 4 / A ^ 3)
      = (∑ m ∈ R2 M₂, (m : ℝ)) * (8 * max (c 3 1 * Λ) 0 * T ^ 4) / (((|ℓ| : ℤ)) : ℝ) ^ 3 := by
    rw [show D = max (c 3 1 * Λ) 0 from rfl, show A = ((|ℓ| : ℤ) : ℝ) from rfl]
    ring
  exact hconv ▸ hfinal

end Work.GM.Affine
