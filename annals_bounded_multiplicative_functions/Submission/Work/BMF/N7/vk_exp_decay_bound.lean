import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N7

/-- Elementary estimate: for `a, c > 0` and `t ≥ 0` one has
`c * t - a * t ^ 3 ≤ c * √c / √a`.

Indeed, if `t ≤ √(c/a)` then `c t - a t³ ≤ c t ≤ c √(c/a) = c √c / √a`, while if
`t ≥ √(c/a)` then `a t² ≥ c`, hence `a t³ ≥ c t` and the left-hand side is `≤ 0`. -/
lemma cubic_le (a c t : ℝ) (ha : 0 < a) (hc : 0 < c) (ht : 0 ≤ t) :
    c * t - a * t ^ 3 ≤ c * Real.sqrt c / Real.sqrt a := by
  rcases le_total t (Real.sqrt (c / a)) with h | h
  · have h1 : c * t - a * t ^ 3 ≤ c * t := by
      have : 0 ≤ a * t ^ 3 := mul_nonneg ha.le (pow_nonneg ht 3)
      linarith
    have h2 : c * t ≤ c * Real.sqrt (c / a) := mul_le_mul_of_nonneg_left h hc.le
    have h3 : Real.sqrt (c / a) = Real.sqrt c / Real.sqrt a := Real.sqrt_div hc.le a
    calc c * t - a * t ^ 3 ≤ c * t := h1
      _ ≤ c * Real.sqrt (c / a) := h2
      _ = c * (Real.sqrt c / Real.sqrt a) := by rw [h3]
      _ = c * Real.sqrt c / Real.sqrt a := by ring
  · have hs2 : Real.sqrt (c / a) ^ 2 = c / a := Real.sq_sqrt (div_nonneg hc.le ha.le)
    have hsq : c / a ≤ t ^ 2 := by
      nlinarith [Real.sqrt_nonneg (c / a), ht, h, hs2]
    have hca : c ≤ a * t ^ 2 := by
      have hh : a * (c / a) ≤ a * t ^ 2 := mul_le_mul_of_nonneg_left hsq ha.le
      have hc' : a * (c / a) = c := by field_simp
      linarith
    have hct : c * t ≤ a * t ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_right hca ht
      have h2 : a * t ^ 2 * t = a * t ^ 3 := by ring
      linarith
    have hM : 0 ≤ c * Real.sqrt c / Real.sqrt a :=
      div_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg c)) (Real.sqrt_nonneg a)
    linarith

/-- `2(L+2)·exp(b L^{1/7} - a L^{3/7})` is `O(L^{6/7})` on `L ≥ 3`, for `a, b > 0`.

Explicit witness: `A = exp(log 6 + (b+1)·√(b+1)/√a)`.  Writing `t = L^{1/7}`, for
`L ≥ 3` one has `L + 2 ≤ 3 L` and `L = t · L^{6/7}`, so it suffices to bound
`6 t · exp(b t - a t³) = exp(log 6 + log t + b t - a t³)`.  Since `log t ≤ t` and
`(b+1) t - a t³ ≤ (b+1)√(b+1)/√a` (`cubic_le`), that factor is `≤ A`. -/
theorem vk_exp_decay_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 3 ≤ L →
      2 * (L + 2) * Real.exp (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ)) ≤
        A * L ^ (6 / 7 : ℝ) := by
  refine ⟨Real.exp (Real.log 6 + (b + 1) * Real.sqrt (b + 1) / Real.sqrt a),
    Real.exp_pos _, ?_⟩
  intro L hL
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have htpos : 0 < L ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have ht0 : 0 ≤ L ^ (1 / 7 : ℝ) := htpos.le
  have hpow3 : L ^ (3 / 7 : ℝ) = (L ^ (1 / 7 : ℝ)) ^ 3 := by
    have h1 : (3 / 7 : ℝ) = (1 / 7 : ℝ) * 3 := by norm_num
    rw [h1, Real.rpow_mul hL0]
    norm_num
  have hLid : L = L ^ (1 / 7 : ℝ) * L ^ (6 / 7 : ℝ) := by
    rw [← Real.rpow_add hLpos (1 / 7 : ℝ) (6 / 7 : ℝ)]
    rw [show (1 / 7 : ℝ) + 6 / 7 = 1 by norm_num, Real.rpow_one]
  have h6t : Real.exp (Real.log (6 * L ^ (1 / 7 : ℝ))) = 6 * L ^ (1 / 7 : ℝ) :=
    Real.exp_log (mul_pos (by norm_num) htpos)
  have hmain : 6 * L ^ (1 / 7 : ℝ) * Real.exp (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ)) ≤
      Real.exp (Real.log 6 + (b + 1) * Real.sqrt (b + 1) / Real.sqrt a) := by
    have hsplit : 6 * L ^ (1 / 7 : ℝ) * Real.exp (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ))
        = Real.exp (Real.log (6 * L ^ (1 / 7 : ℝ)) +
            (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ))) := by
      rw [Real.exp_add, h6t]
    rw [hsplit]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (ne_of_gt htpos), hpow3]
    have hlogt : Real.log (L ^ (1 / 7 : ℝ)) ≤ L ^ (1 / 7 : ℝ) := by
      have := Real.log_le_sub_one_of_pos htpos; linarith
    have hcub := cubic_le a (b + 1) (L ^ (1 / 7 : ℝ)) ha (by linarith) ht0
    linarith
  have hstep1 : 2 * (L + 2) * Real.exp (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ)) ≤
      6 * L * Real.exp (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    linarith
  have hstep2 : 6 * L * Real.exp (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ)) ≤
      Real.exp (Real.log 6 + (b + 1) * Real.sqrt (b + 1) / Real.sqrt a) *
        L ^ (6 / 7 : ℝ) := by
    have htmp : 6 * L * Real.exp (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ))
        = (6 * L ^ (1 / 7 : ℝ) * Real.exp (b * L ^ (1 / 7 : ℝ) - a * L ^ (3 / 7 : ℝ))) *
            L ^ (6 / 7 : ℝ) := by
      nth_rewrite 1 [hLid]
      ring
    rw [htmp]
    exact mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hL0 _)
  linarith

end Work.BMF.N7
