import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N7

/-- The `δ`-term bound for the per-term estimate: for `L ≥ 3`, `0 ≤ t ≤ L + 2`,
`0 ≤ δ ≤ cζ L^{-6/7}`, one has `t * δ ≤ 2 cζ L^{1/7}`. -/
theorem vk_delta_term_le (cζ : ℝ) (hcζ : 0 < cζ) :
    ∀ (L t δ : ℝ), 3 ≤ L → 0 ≤ t → t ≤ L + 2 → 0 ≤ δ →
      δ ≤ cζ * L ^ (-(6 / 7 : ℝ)) →
      t * δ ≤ 2 * cζ * L ^ ((1 / 7 : ℝ)) := by
  intro L t δ hL ht ht2 hδ hδ2
  have hLpos : (0:ℝ) < L := by linarith
  have hrpow : L * L ^ (-(6 / 7 : ℝ)) = L ^ (1 / 7 : ℝ) := by
    have hsum : (1:ℝ) + (-(6/7:ℝ)) = (1/7:ℝ) := by norm_num
    calc L * L ^ (-(6/7:ℝ)) = L^(1:ℝ) * L^(-(6/7:ℝ) : ℝ) := by rw [Real.rpow_one]
         _ = L ^ ((1:ℝ) + (-(6/7:ℝ))) := by rw [Real.rpow_add hLpos]
         _ = L ^ (1/7:ℝ) := by rw [hsum]
  have h1 : t * δ ≤ (L + 2) * (cζ * L ^ (-(6/7:ℝ))) := by
    calc t * δ ≤ t * (cζ * L ^ (-(6/7:ℝ))) := by
              apply mul_le_mul_of_nonneg_left hδ2 ht
         _ ≤ (L + 2) * (cζ * L ^ (-(6/7:ℝ))) := by
              exact mul_le_mul_of_nonneg_right ht2 (by positivity)
  calc t * δ ≤ (L + 2) * (cζ * L ^ (-(6/7:ℝ))) := h1
    _ ≤ 2 * cζ * L ^ (1/7:ℝ) := by
          have hL2 : L + 2 ≤ 2 * L := by linarith
          calc (L + 2) * (cζ * L ^ (-(6/7:ℝ)))
              = cζ * ((L + 2) * L ^ (-(6/7:ℝ))) := by ring
            _ ≤ cζ * ((2 * L) * L ^ (-(6/7:ℝ))) := by
                  apply mul_le_mul_of_nonneg_left _ (le_of_lt hcζ)
                  exact mul_le_mul_of_nonneg_right hL2 (by positivity)
            _ = 2 * cζ * L ^ (1/7:ℝ) := by rw [mul_assoc, hrpow]; ring

/-- The main-term bound for the per-term estimate: for `c₀ > 0`, `L ≥ 3`, `0 ≤ t`,
`(L/c₀)^{6/7} ≤ t ≤ L + 2`, one has
`c₀^{-17/7}/5 · L^{3/7} ≤ t · (c₀ (t/L)² / log(L/t + 2))`. -/
theorem vk_main_term_ge (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ (L t : ℝ), 3 ≤ L → 0 ≤ t →
      (L / c₀) ^ (6 / 7 : ℝ) ≤ t → t ≤ L + 2 →
      c₀ ^ (-(17 / 7) : ℝ) / 5 * L ^ ((3 / 7 : ℝ)) ≤
        t * (c₀ * ((t / L) ^ 2) / Real.log (L / t + 2)) := by
  intro L t hL ht hBt htL
  have hLpos : (0:ℝ) < L := by linarith
  have hcd : 0 < L / c₀ := div_pos hLpos hc₀
  have hBpos : 0 < (L/c₀)^(6/7:ℝ) := Real.rpow_pos_of_pos hcd _
  have htpos : 0 < t := lt_of_lt_of_le hBpos hBt
  set A := c₀^(6/7:ℝ) * L^(1/7:ℝ) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hLtpos : 0 < L/t := div_pos hLpos htpos
  have hDpos : 0 < Real.log (L/t+2) := Real.log_pos (by linarith)
  have hdiv_eq : L / (L/c₀)^(6/7:ℝ) = A := by
    rw [hA]
    rw [Real.div_rpow (le_of_lt hLpos) (le_of_lt hc₀), div_div_eq_mul_div]
    rw [show L * c₀^(6/7:ℝ) / L^(6/7:ℝ) = (L / L^(6/7:ℝ)) * c₀^(6/7:ℝ) by ring]
    rw [show L / L^(6/7:ℝ) = L^(1/7:ℝ) by
          rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hLpos _))]
          rw [← Real.rpow_add hLpos]
          rw [show (1:ℝ)/7 + 6/7 = 1 by norm_num, Real.rpow_one]]
    ring
  have hdiv : L / t ≤ A := by
    rw [← hdiv_eq]
    exact div_le_div_of_nonneg_left (le_of_lt hLpos) hBpos hBt
  have hAge : (3:ℝ)/5 ≤ A := by
    have h1 : L / (L+2) ≤ L/t := div_le_div_of_nonneg_left (le_of_lt hLpos) (by linarith) htL
    have h2 : (3:ℝ)/5 ≤ L/(L+2) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < L+2)]
      linarith
    linarith
  have hDle : Real.log (L/t+2) ≤ 5 * A := by
    have h1 : L/t + 2 ≤ A + 2 := by linarith
    have h2 : Real.log (L/t+2) ≤ Real.log (A+2) := Real.log_le_log (by linarith) h1
    have h3 : Real.log (A+2) ≤ A + 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < A+2 by linarith)
      linarith
    have h4 : A + 1 ≤ 5 * A := by linarith
    linarith
  have hDiv : c₀ * ((t/L)^2) / (5*A) ≤ c₀ * ((t/L)^2) / Real.log (L/t+2) :=
    div_le_div_of_nonneg_left (by positivity) hDpos hDle
  have hstep1 : t * (c₀ * ((t/L)^2) / (5*A)) ≤
                t * (c₀ * ((t/L)^2) / Real.log (L/t+2)) :=
    mul_le_mul_of_nonneg_left hDiv (le_of_lt htpos)
  have heq1 : t * (c₀ * ((t/L)^2) / (5*A)) = c₀ * t^3 / (5*L^2*A) := by
    field_simp
  have hii : c₀^(-(17/7):ℝ) * L^(3/7:ℝ) * (L^2 * (c₀^(6/7:ℝ)*L^(1/7:ℝ))) =
      c₀^(-(11/7):ℝ) * L^(18/7:ℝ) := by
    have hLcomb : L^(3/7:ℝ) * L^2 * L^(1/7:ℝ) = L^(18/7:ℝ) := by
      rw [← Real.rpow_natCast L 2]; push_cast
      rw [← Real.rpow_add hLpos (3/7:ℝ) (2:ℝ)]
      rw [← Real.rpow_add hLpos ((3/7:ℝ)+2) (1/7:ℝ)]
      rw [show ((3/7:ℝ)+2)+(1/7:ℝ) = 18/7 by norm_num]
    calc c₀^(-(17/7):ℝ) * L^(3/7:ℝ) * (L^2 * (c₀^(6/7:ℝ)*L^(1/7:ℝ)))
        = (c₀^(-(17/7):ℝ) * c₀^(6/7:ℝ)) * (L^(3/7:ℝ) * L^2 * L^(1/7:ℝ)) := by ring
      _ = c₀^((-(17/7):ℝ) + 6/7) * (L^(3/7:ℝ) * L^2 * L^(1/7:ℝ)) := by
            rw [← Real.rpow_add hc₀]
      _ = c₀^((-(17/7):ℝ) + 6/7) * L^(18/7:ℝ) := by rw [hLcomb]
      _ = c₀^(-(11/7):ℝ) * L^(18/7:ℝ) := by
            rw [show (-(17/7):ℝ)+6/7 = -(11/7) by norm_num]
  have hic : c₀ * (L/c₀)^(18/7:ℝ) = c₀^(-(11/7):ℝ) * L^(18/7:ℝ) := by
    have hchain : c₀ * c₀^(-(18/7):ℝ) = c₀^(-(11/7):ℝ) := by
      nth_rewrite 1 [← Real.rpow_one c₀]
      rw [← Real.rpow_add hc₀ (1:ℝ) (-(18/7:ℝ))]
      norm_num
    have h : (L/c₀)^(18/7:ℝ) = L^(18/7:ℝ) * c₀^(-(18/7):ℝ) := by
      rw [Real.div_rpow (le_of_lt hLpos) (le_of_lt hc₀), Real.rpow_neg (le_of_lt hc₀),
        div_eq_mul_inv]
    calc c₀ * (L/c₀)^(18/7:ℝ)
        = c₀ * (L^(18/7:ℝ) * c₀^(-(18/7):ℝ)) := by rw [h]
      _ = (c₀ * c₀^(-(18/7):ℝ)) * L^(18/7:ℝ) := by ring
      _ = c₀^(-(11/7):ℝ) * L^(18/7:ℝ) := by rw [hchain]
  have ht3 : (L/c₀)^(18/7:ℝ) ≤ t^3 := by
    have h1 : ((L/c₀)^(6/7:ℝ))^3 ≤ t^3 := pow_le_pow_left₀ (le_of_lt hBpos) hBt 3
    have h2 : ((L/c₀)^(6/7:ℝ))^3 = (L/c₀)^(18/7:ℝ) := by
      rw [← Real.rpow_natCast ((L/c₀)^(6/7:ℝ)) 3]; push_cast
      rw [← Real.rpow_mul (le_of_lt hcd) (6/7:ℝ) 3]
      rw [show (6/7:ℝ)*3 = 18/7 by norm_num]
    rwa [h2] at h1
  have hfinal : c₀^(-(17/7):ℝ)/5 * L^(3/7:ℝ) ≤ c₀*t^3/(5*L^2*A) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 5*L^2*A)]
    have hLHS : c₀^(-(17/7):ℝ)/5 * L^(3/7:ℝ) * (5*L^2*A) = c₀*(L/c₀)^(18/7:ℝ) := by
      rw [hA]
      rw [show c₀^(-(17/7):ℝ)/5 * L^(3/7:ℝ) * (5*L^2*(c₀^(6/7:ℝ)*L^(1/7:ℝ)))
            = c₀^(-(17/7):ℝ) * L^(3/7:ℝ) * (L^2 * (c₀^(6/7:ℝ)*L^(1/7:ℝ))) by ring]
      rw [hii, ← hic]
    rw [hLHS]
    exact mul_le_mul_of_nonneg_left ht3 (le_of_lt hc₀)
  calc c₀^(-(17/7):ℝ)/5 * L^(3/7:ℝ)
      ≤ c₀*t^3/(5*L^2*A) := hfinal
    _ = t * (c₀ * ((t/L)^2) / (5*A)) := heq1.symm
    _ ≤ t * (c₀ * ((t/L)^2) / Real.log (L/t+2)) := hstep1

/-- A single term of the dyadic `V_K` sum with `t = j·log 2`: for `L ≥ 3`,
`0 ≤ δ ≤ cζ L^{-6/7}`, `(L/c₀)^{6/7} ≤ t` and `t ≤ L + 2`, the term
`2^{j(δ - c₀ (t/L)²/log(L/t+2))}` is at most `exp(2 cζ L^{1/7} - (c₀^{-17/7}/5) L^{3/7})`. -/
theorem vk_per_term_bound (c₀ cζ : ℝ) (hc₀ : 0 < c₀) (hcζ : 0 < cζ) :
    ∀ (L δ : ℝ) (j : ℕ),
      3 ≤ L → 0 ≤ δ → δ ≤ cζ * L ^ (-(6 / 7 : ℝ)) →
      (L / c₀) ^ (6 / 7 : ℝ) ≤ (j : ℝ) * Real.log 2 →
      (j : ℝ) * Real.log 2 ≤ L + 2 →
      (2 : ℝ) ^ ((j : ℝ) * (δ - c₀ * (((j : ℝ) * Real.log 2) / L) ^ 2 /
            Real.log (L / ((j : ℝ) * Real.log 2) + 2))) ≤
        Real.exp (2 * cζ * L ^ (1 / 7 : ℝ) - c₀ ^ (-(17 / 7) : ℝ) / 5 * L ^ (3 / 7 : ℝ)) := by
  intro L δ j hL hδ0 hδle htlo hthi
  set t : ℝ := (j:ℝ) * Real.log 2 with ht
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht0 : 0 ≤ t := by
    rw [ht]; exact mul_nonneg (Nat.cast_nonneg j) (le_of_lt hlog2pos)
  have hdelta := vk_delta_term_le cζ hcζ L t δ hL ht0 hthi hδ0 hδle
  have hmain := vk_main_term_ge c₀ hc₀ L t hL ht0 htlo hthi
  have hconv : (2:ℝ) ^ ((j:ℝ) * (δ - c₀ * ((t / L) ^ 2) / Real.log (L / t + 2)))
      = Real.exp (t * (δ - c₀ * ((t / L) ^ 2) / Real.log (L / t + 2))) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    rw [ht]; ring
  rw [hconv]
  rw [Real.exp_le_exp]
  have hsplit : t * (δ - c₀ * ((t / L) ^ 2) / Real.log (L / t + 2))
      = t * δ - t * (c₀ * ((t / L) ^ 2) / Real.log (L / t + 2)) := by ring
  rw [hsplit]
  exact sub_le_sub hdelta hmain

end Work.BMF.N7
