import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace Commons.Analysis.Real

open Filter

/-- For every `c > 0`, `k : ℕ` and `ε > 0`, for all sufficiently large natural `n`,
we have `n ^ k * exp (-(c * n)) ≤ ε`. -/
lemma exists_nat_pow_mul_exp_neg_le (k : ℕ) {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) ^ k * Real.exp (-(c * (n : ℝ))) ≤ ε := by
  have hlo : (fun x : ℝ => x ^ k) =o[Filter.atTop] (fun x : ℝ => Real.exp (c * x)) :=
    isLittleO_pow_exp_pos_mul_atTop k hc
  have hev : ∀ᶠ x : ℝ in Filter.atTop, x ^ k * Real.exp (-(c * x)) ≤ ε := by
    filter_upwards [hlo.bound hε, Filter.eventually_ge_atTop (0 : ℝ)] with x hx hx0
    rw [Real.norm_of_nonneg (pow_nonneg hx0 k),
      Real.norm_of_nonneg (Real.exp_pos (c * x)).le] at hx
    have h2 := mul_le_mul_of_nonneg_right hx (Real.exp_pos (-(c * x))).le
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h2
    exact h2
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  obtain ⟨N, hN⟩ := exists_nat_ge a
  exact ⟨N, fun n hn => ha (n : ℝ) (le_trans hN (by exact_mod_cast hn))⟩

/-- For every `c > 0`, for all sufficiently large natural `n`, `(log n)^2 ≤ c * n`. -/
lemma exists_nat_log_sq_le_mul {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log (n : ℝ)) ^ 2 ≤ c * (n : ℝ) := by
  have hlo : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[Filter.atTop]
      (fun x : ℝ => x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (2 : ℝ) one_pos
  have hev : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ 2 ≤ c * x := by
    filter_upwards [hlo.bound hc, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 ≤ x := le_trans zero_le_one hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog (2 : ℝ)), Real.rpow_two,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0 (1 : ℝ)), Real.rpow_one] at hx
    exact hx
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  obtain ⟨N, hN⟩ := exists_nat_ge a
  exact ⟨N, fun n hn => ha (n : ℝ) (le_trans hN (by exact_mod_cast hn))⟩

theorem reservoir_union_bound (c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ V : ℝ, 0 ≤ V → V ≤ (n : ℝ) ^ Real.log n → (2 * (n : ℝ) + 4 * (n : ℝ) * V) * Real.exp (-(c1 * (n : ℝ))) + 2 * ((4 : ℝ) ^ n) * Real.exp (-(c2 * (n : ℝ) ^ 2)) < 1 := by
  have hc1h : 0 < c1 / 2 := by linarith
  have hc2h : 0 < c2 / 2 := by linarith
  have e1 : ∀ᶠ n : ℕ in Filter.atTop, (Real.log (n : ℝ)) ^ 2 ≤ (c1 / 2) * (n : ℝ) :=
    Filter.eventually_atTop.mpr (exists_nat_log_sq_le_mul hc1h)
  have e2 : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * Real.exp (-((c1 / 2) * (n : ℝ))) ≤ 1 / 24 := by
    have h := exists_nat_pow_mul_exp_neg_le 1 hc1h (ε := 1 / 24) (by norm_num)
    filter_upwards [Filter.eventually_atTop.mpr h] with n hn
    simpa using hn
  have e3 : ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-((c2 / 2) * (n : ℝ))) ≤ 1 / 8 := by
    have h := exists_nat_pow_mul_exp_neg_le 0 hc2h (ε := 1 / 8) (by norm_num)
    filter_upwards [Filter.eventually_atTop.mpr h] with n hn
    simpa using hn
  have e4 : ∀ᶠ n : ℕ in Filter.atTop, Real.log 4 ≤ (c2 / 2) * (n : ℝ) := by
    obtain ⟨M, hM⟩ := exists_nat_ge (Real.log 4 / (c2 / 2))
    apply Filter.eventually_atTop.mpr
    refine ⟨M, fun n hn => ?_⟩
    have h : Real.log 4 / (c2 / 2) ≤ (n : ℝ) := le_trans hM (by exact_mod_cast hn)
    have h' : (Real.log 4 / (c2 / 2)) * (c2 / 2) ≤ (n : ℝ) * (c2 / 2) :=
      mul_le_mul_of_nonneg_right h hc2h.le
    rw [div_mul_cancel₀ (Real.log 4) (ne_of_gt hc2h)] at h'
    linarith [h']
  have eall : ∀ᶠ n : ℕ in Filter.atTop,
      (Real.log (n : ℝ)) ^ 2 ≤ (c1 / 2) * (n : ℝ) ∧
      (n : ℝ) * Real.exp (-((c1 / 2) * (n : ℝ))) ≤ 1 / 24 ∧
      Real.exp (-((c2 / 2) * (n : ℝ))) ≤ 1 / 8 ∧
      Real.log 4 ≤ (c2 / 2) * (n : ℝ) ∧ 2 ≤ n := by
    filter_upwards [e1, e2, e3, e4, Filter.eventually_ge_atTop 2] with n h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp eall
  refine ⟨N, fun n hn V hV0 hVn => ?_⟩
  obtain ⟨hlogn, hexp1, hexp2, hlog4, hn2⟩ := hN n hn
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hVexp : V ≤ Real.exp ((Real.log (n : ℝ)) ^ 2) := by
    calc V ≤ (n : ℝ) ^ Real.log (n : ℝ) := hVn
      _ = Real.exp ((Real.log (n : ℝ)) ^ 2) := by
            rw [Real.rpow_def_of_pos hnpos]
            congr 1
            ring
  have hVbound : V * Real.exp (-(c1 * (n : ℝ))) ≤ Real.exp (-((c1 / 2) * (n : ℝ))) := by
    have h1 : V * Real.exp (-(c1 * (n : ℝ)))
        ≤ Real.exp ((Real.log (n : ℝ)) ^ 2) * Real.exp (-(c1 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hVexp (Real.exp_pos _).le
    have h2 : Real.exp ((Real.log (n : ℝ)) ^ 2) * Real.exp (-(c1 * (n : ℝ)))
        = Real.exp ((Real.log (n : ℝ)) ^ 2 - c1 * (n : ℝ)) := by
      rw [← Real.exp_add]
      apply congrArg Real.exp
      ring
    rw [h2] at h1
    have h3 : (Real.log (n : ℝ)) ^ 2 - c1 * (n : ℝ) ≤ -((c1 / 2) * (n : ℝ)) := by
      linarith [hlogn]
    exact h1.trans (Real.exp_le_exp.mpr h3)
  have hbound1 : (2 * (n : ℝ) + 4 * (n : ℝ) * V) * Real.exp (-(c1 * (n : ℝ))) ≤ 1 / 4 := by
    have h2n : 2 * (n : ℝ) * Real.exp (-(c1 * (n : ℝ)))
        ≤ 2 * (n : ℝ) * Real.exp (-((c1 / 2) * (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        nlinarith [hnn, hc1]
      · exact mul_nonneg (by norm_num) hnn
    have h4n : 4 * (n : ℝ) * (V * Real.exp (-(c1 * (n : ℝ))))
        ≤ 4 * (n : ℝ) * Real.exp (-((c1 / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hVbound (mul_nonneg (by norm_num) hnn)
    have hsplit : (2 * (n : ℝ) + 4 * (n : ℝ) * V) * Real.exp (-(c1 * (n : ℝ)))
        = 2 * (n : ℝ) * Real.exp (-(c1 * (n : ℝ)))
          + 4 * (n : ℝ) * (V * Real.exp (-(c1 * (n : ℝ)))) := by ring
    rw [hsplit]
    calc 2 * (n : ℝ) * Real.exp (-(c1 * (n : ℝ)))
            + 4 * (n : ℝ) * (V * Real.exp (-(c1 * (n : ℝ))))
        ≤ 2 * (n : ℝ) * Real.exp (-((c1 / 2) * (n : ℝ)))
            + 4 * (n : ℝ) * Real.exp (-((c1 / 2) * (n : ℝ))) := add_le_add h2n h4n
      _ = 6 * ((n : ℝ) * Real.exp (-((c1 / 2) * (n : ℝ)))) := by ring
      _ ≤ 6 * (1 / 24) := mul_le_mul_of_nonneg_left hexp1 (by norm_num)
      _ = 1 / 4 := by norm_num
  have h4eq : (4 : ℝ) ^ n = Real.exp (Real.log 4 * (n : ℝ)) := by
    rw [show (4 : ℝ) ^ n = (4 : ℝ) ^ ((n : ℝ)) from (Real.rpow_natCast (4 : ℝ) n).symm,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hbound2 : 2 * ((4 : ℝ) ^ n) * Real.exp (-(c2 * (n : ℝ) ^ 2)) ≤ 1 / 4 := by
    have hexp_le : Real.exp (Real.log 4 * (n : ℝ)) * Real.exp (-(c2 * (n : ℝ) ^ 2)) ≤ 1 / 8 := by
      have harg : Real.log 4 * (n : ℝ) - c2 * (n : ℝ) ^ 2 ≤ -((c2 / 2) * (n : ℝ)) := by
        have hmul : Real.log 4 * (n : ℝ) ≤ (c2 / 2) * (n : ℝ) ^ 2 := by
          have h := mul_le_mul_of_nonneg_right hlog4 hnn
          calc Real.log 4 * (n : ℝ) ≤ ((c2 / 2) * (n : ℝ)) * (n : ℝ) := h
            _ = (c2 / 2) * (n : ℝ) ^ 2 := by ring
        have h1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
        have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
          calc (n : ℝ) = (n : ℝ) * 1 := by ring
            _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left h1 hnn
            _ = (n : ℝ) ^ 2 := by ring
        have hmul2 : (c2 / 2) * (n : ℝ) ≤ (c2 / 2) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hc2h.le
        linarith [hmul, hmul2]
      calc Real.exp (Real.log 4 * (n : ℝ)) * Real.exp (-(c2 * (n : ℝ) ^ 2))
          = Real.exp (Real.log 4 * (n : ℝ) - c2 * (n : ℝ) ^ 2) := by
            rw [← Real.exp_add]
            apply congrArg Real.exp
            ring
        _ ≤ Real.exp (-((c2 / 2) * (n : ℝ))) := Real.exp_le_exp.mpr harg
        _ ≤ 1 / 8 := hexp2
    rw [h4eq]
    calc 2 * Real.exp (Real.log 4 * (n : ℝ)) * Real.exp (-(c2 * (n : ℝ) ^ 2))
        = 2 * (Real.exp (Real.log 4 * (n : ℝ)) * Real.exp (-(c2 * (n : ℝ) ^ 2))) := by ring
      _ ≤ 2 * (1 / 8) := mul_le_mul_of_nonneg_left hexp_le (by norm_num)
      _ = 1 / 4 := by norm_num
  linarith

end Commons.Analysis.Real