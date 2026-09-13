import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Sigma2

/-- `(a - b)^2 ≤ 2 a^2 + 2 b^2`. -/
lemma sq_sub_sq_le_two (a b : ℝ) : (a - b)^2 ≤ 2*a^2 + 2*b^2 := by
  nlinarith [sq_nonneg (a + b)]

/-- If `|x| ≤ 3` then `x^2 ≤ 9`. -/
lemma sq_le_nine_of_abs_le_three {x : ℝ} (h : |x| ≤ 3) : x^2 ≤ 9 := by
  have h' : |x|^2 ≤ (3:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg x) h 2
  rw [sq_abs] at h'
  norm_num at h'
  exact h'

/-- If `|u| ≤ Γ` then `u^2 ≤ Γ^2`. -/
lemma sq_le_sq_of_abs_le {u Γ : ℝ} (h : |u| ≤ Γ) : u^2 ≤ Γ^2 := by
  have h' : |u|^2 ≤ Γ^2 := pow_le_pow_left₀ (abs_nonneg u) h 2
  simpa [sq_abs] using h'

open scoped BigOperators in
theorem degenerate_case_bound_pos {S rho b α β Γ : ℝ} {lam xc u D1b : Fin 4 → ℝ}
    (hb : 0 < b) (hβ : 0 < β) (hrho : 0 < rho) (hrho9 : rho < 9) (hS : 0 < S) (hΓ : 4 ≤ Γ)
    (hα : 0 ≤ α) (hα2 : α ^ 2 ≤ β / 200) (hβ2 : β * Γ ^ 2 ≤ 1 / 100)
    (hxc : ∀ i : Fin 4, |xc i| ≤ 3) (hu : ∀ i : Fin 4, |u i| ≤ Γ)
    (hfs3 : (∑ i : Fin 4, (S - lam i)) = 3 * S)
    (hfsnn : ∀ i : Fin 4, 0 ≤ S - lam i)
    (hC1 : ((1 - 1 / Real.sqrt 2) / 16) * S ^ 3 ≤ ∑ i : Fin 4, (S - lam i) * (lam i) ^ 2)
    (hmax1 : ∀ i : Fin 4, D1b i / b = 4 * xc i / rho - α * xc i * lam i - β * u i * lam i)
    (hmaxP : -12 * S / rho - 8 * (∑ i : Fin 4, (S - lam i) * (xc i) ^ 2) / rho ^ 2 + 2 * α
        + β * (∑ i : Fin 4, (S - lam i) * (lam i) ^ 2)
        - (1 / b ^ 2) * (∑ i : Fin 4, (S - lam i) * (D1b i) ^ 2) ≤ 0) :
    rho ^ 2 * S ^ 2 ≤ 3240 * 16 / (1 - 1 / Real.sqrt 2) / β := by
  classical
  set A : ℝ := ∑ i : Fin 4, (S - lam i) * (xc i)^2 with hA
  set T : ℝ := ∑ i : Fin 4, (S - lam i) * (lam i)^2 with hT
  set D : ℝ := ∑ i : Fin 4, (S - lam i) * (D1b i)^2 with hD
  set W : ℝ := ∑ i : Fin 4, (S - lam i) * (α * xc i + β * u i)^2 * (lam i)^2 with hW
  set c0 : ℝ := 1 - 1 / Real.sqrt 2 with hc0def
  -- positivity
  have hρ2 : (0:ℝ) < rho^2 := pow_pos hrho 2
  have hbne : b ≠ 0 := ne_of_gt hb
  have hc0pos : 0 < c0 := by
    rw [hc0def]
    have hlt : (1:ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
    have hpos : (0:ℝ) < Real.sqrt 2 := lt_trans zero_lt_one hlt
    have : (1:ℝ)/Real.sqrt 2 < 1 := by
      rw [div_lt_iff₀ hpos]; simpa using hlt
    linarith
  -- (1) pointwise bound on (α xc + β u)^2
  have hw_bound : ∀ i : Fin 4, (α * xc i + β * u i)^2 ≤ (11/100) * β := by
    intro i
    have hxi : (xc i)^2 ≤ 9 := sq_le_nine_of_abs_le_three (hxc i)
    have hui : (u i)^2 ≤ Γ^2 := sq_le_sq_of_abs_le (hu i)
    have hat : (α * xc i + β * u i)^2 ≤ 2*(α * xc i)^2 + 2*(β * u i)^2 := by
      nlinarith [sq_nonneg (α * xc i - β * u i)]
    have h1 : (α * xc i)^2 ≤ 9 * (β/200) := by
      rw [show (α * xc i)^2 = α^2 * (xc i)^2 by ring]
      calc α^2 * (xc i)^2 ≤ α^2 * 9 := mul_le_mul_of_nonneg_left hxi (sq_nonneg α)
        _ ≤ (β/200) * 9 := mul_le_mul_of_nonneg_right hα2 (by norm_num)
        _ = 9 * (β/200) := by ring
    have h2 : (β * u i)^2 ≤ β * (1/100) := by
      rw [show (β * u i)^2 = β^2 * (u i)^2 by ring]
      calc β^2 * (u i)^2 ≤ β^2 * Γ^2 := mul_le_mul_of_nonneg_left hui (sq_nonneg β)
        _ = β * (β * Γ^2) := by ring
        _ ≤ β * (1/100) := mul_le_mul_of_nonneg_left hβ2 (le_of_lt hβ)
    nlinarith [hat, h1, h2]
  -- (2) W ≤ (11/100) β T
  have hWle : W ≤ (11/100) * β * T := by
    rw [hW, hT]
    calc ∑ i : Fin 4, (S - lam i) * (α * xc i + β * u i)^2 * (lam i)^2
        ≤ ∑ i : Fin 4, (S - lam i) * ((11/100)*β) * (lam i)^2 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hw_bound i) (hfsnn i)) (sq_nonneg (lam i))
      _ = (11/100) * β * ∑ i : Fin 4, (S - lam i) * (lam i)^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
  -- (3) A ≤ 27 S
  have hAle : A ≤ 27 * S := by
    rw [hA]
    calc ∑ i : Fin 4, (S - lam i) * (xc i)^2
        ≤ ∑ i : Fin 4, (S - lam i) * 9 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (sq_le_nine_of_abs_le_three (hxc i)) (hfsnn i)
      _ = (∑ i : Fin 4, (S - lam i)) * 9 := by rw [Finset.sum_mul]
      _ = 3 * S * 9 := by rw [hfs3]
      _ = 27 * S := by ring
  -- (4) expand (1/b^2) D
  have hDexpand : (1/b^2) * D
      = ∑ i : Fin 4, (S - lam i) * (4 * xc i / rho - (α * xc i + β * u i) * lam i)^2 := by
    rw [hD, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hpt : (1/b^2) * ((S - lam i) * (D1b i)^2)
        = (S - lam i) * (4 * xc i / rho - (α * xc i + β * u i) * lam i)^2 := by
      have hb1 : D1b i / b = 4 * xc i / rho - (α * xc i + β * u i) * lam i := by
        rw [hmax1 i]; ring
      rw [← hb1, div_pow]
      ring
    exact hpt
  -- (5) (1/b^2) D ≤ 32 A/rho^2 + 2 W
  have hDle : (1/b^2) * D ≤ 32*A/rho^2 + 2*W := by
    rw [hDexpand, hA, hW]
    calc ∑ i : Fin 4, (S - lam i) * (4 * xc i / rho - (α * xc i + β * u i) * lam i)^2
        ≤ ∑ i : Fin 4, (S - lam i) *
            (2*(4 * xc i / rho)^2 + 2*((α * xc i + β * u i) * lam i)^2) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (sq_sub_sq_le_two (4 * xc i / rho) ((α * xc i + β * u i) * lam i)) (hfsnn i)
      _ = (∑ i : Fin 4, (S - lam i) * (2*(4 * xc i / rho)^2))
          + (∑ i : Fin 4, (S - lam i) * (2*((α * xc i + β * u i) * lam i)^2)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = 32*A/rho^2 + 2*W := by
          congr 1
          · rw [show 32*A/rho^2 = (32/rho^2)*A by ring, hA, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          · rw [hW, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
  -- (6) combine
  have hbetaT : β*T ≤ (1/b^2)*D + 12*S/rho + 8*A/rho^2 - 2*α := by
    ring_nf at hmaxP ⊢
    linarith [hmaxP]
  have hW2 : 2*W ≤ (11/50)*β*T := by linarith [hWle]
  have hA2 : 40*A/rho^2 ≤ 1080*S/rho^2 := by
    have h40 : 40*A ≤ 1080*S := by linarith [hAle]
    have hr2 : 0 ≤ (rho^2)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_right h40 hr2
    simpa [div_eq_mul_inv] using this
  have hboundT : (39/50)*β*T ≤ 1080*S/rho^2 + 12*S/rho := by
    ring_nf at hbetaT hDle hW2 hA2 ⊢
    linarith [hbetaT, hDle, hW2, hA2, hα]
  -- (7) multiply by rho^2 and bound rho < 9
  have hkey1 : (39/50)*β*T*rho^2 ≤ 1188*S := by
    have hm := mul_le_mul_of_nonneg_right hboundT hρ2.le
    have hsimp : (1080*S/rho^2 + 12*S/rho)*rho^2 = 1080*S + 12*S*rho := by
      field_simp
    rw [hsimp] at hm
    have hro : 12*S*rho ≤ 108*S := by nlinarith [hrho9, hS]
    linarith [hm, hro]
  -- (8) use T ≥ (c0/16) S^3
  have hTlow : (c0/16) * S^3 ≤ T := hC1
  -- final algebra
  have hc0ne : c0 ≠ 0 := ne_of_gt hc0pos
  have h5 : 39 * β * rho^2 * c0 * S^2 ≤ 950400 := by
    have hnn : 0 ≤ (39/50)*β*rho^2 := by positivity
    have h1 : (39/50)*β*rho^2*((c0/16)*S^3) ≤ (39/50)*β*rho^2*T :=
      mul_le_mul_of_nonneg_left hTlow hnn
    have h2 : (39/50)*β*rho^2*T ≤ 1188*S := by linarith [hkey1]
    have h3 : (39/50)*β*rho^2*((c0/16)*S^3) ≤ 1188*S := le_trans h1 h2
    have h4 : 39*β*rho^2*c0*S^3 ≤ 950400*S := by
      have hmul := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 800)
      ring_nf at hmul ⊢
      linarith [hmul]
    have hfac : 39*β*rho^2*c0*S^3 = (39*β*rho^2*c0*S^2)*S := by ring
    rw [hfac] at h4
    exact (mul_le_mul_iff_of_pos_right hS).mp h4
  have hfinal : β*rho^2*c0*S^2 ≤ 3240*16 := by linarith [h5]
  rw [le_div_iff₀ hβ, le_div_iff₀ hc0pos]
  ring_nf at hfinal ⊢
  linarith [hfinal]

end Commons.Analysis.Sigma2