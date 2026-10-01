import Mathlib

namespace Work.LinnikAreas.Density4

/-- Per-term inequality behind the telescoping bound: for `x ≥ 1`,
`x^{-3/2} ≤ 4 (x^{-1/2} - (x+1)^{-1/2})`.
Writing `u = √x`, `v = √(x+1)`, the claim is `1/(xu) ≤ 4(1/u - 1/v)`, which after
clearing the positive denominator `xuv` is equivalent to `4xu ≤ (4x-1)v`; that in
turn follows on squaring from `16x³ ≤ (4x-1)²(x+1)`, i.e. `8x² - 7x + 1 ≥ 0`. -/
private lemma rpow_neg_three_halves_term_le (x : ℝ) (hx : 1 ≤ x) :
    x ^ (-(3/2:ℝ)) ≤ 4 * (x ^ (-(1/2:ℝ)) - (x+1) ^ (-(1/2:ℝ))) := by
  have hx0 : 0 < x := by linarith
  have hx10 : 0 < x + 1 := by linarith
  set u := Real.sqrt x with hu
  set v := Real.sqrt (x+1) with hv
  have hu0 : 0 < u := by rw [hu]; exact Real.sqrt_pos.mpr hx0
  have hv0 : 0 < v := by rw [hv]; exact Real.sqrt_pos.mpr hx10
  have hu2 : u^2 = x := by rw [hu]; exact Real.sq_sqrt hx0.le
  have hv2 : v^2 = x + 1 := by rw [hv]; exact Real.sq_sqrt hx10.le
  have h4xu : 4*x*u ≤ (4*x-1)*v := by
    have hsq : (4*x*u)^2 ≤ ((4*x-1)*v)^2 := by
      have h1 : (4*x*u)^2 = 16*x^3 := by nlinarith [hu2]
      have h2 : ((4*x-1)*v)^2 = (4*x-1)^2*(x+1) := by nlinarith [hv2]
      rw [h1, h2]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ x-1 by linarith) (show (0:ℝ) ≤ 8*x+1 by linarith)]
    have hL : 0 ≤ 4*x*u := by positivity
    have hR : 0 ≤ (4*x-1)*v := mul_nonneg (by linarith) hv0.le
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hL, abs_of_nonneg hR] at this
  have hkey : (x*u)⁻¹ ≤ 4*(u⁻¹ - v⁻¹) := by
    rw [inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < x*u)]
    rw [inv_sub_inv (ne_of_gt hu0) (ne_of_gt hv0)]
    have hsimp : 4 * ((v - u) / (u * v)) * (x * u) = 4*x*(v-u)/v := by field_simp
    rw [hsimp, le_div_iff₀ hv0]
    nlinarith [h4xu]
  have e1 : x ^ (-(3/2:ℝ)) = (x*u)⁻¹ := by
    rw [show (-(3/2:ℝ)) = -1 + -(1/2:ℝ) by norm_num, Real.rpow_add hx0, Real.rpow_neg_one]
    rw [Real.rpow_neg hx0.le, Real.rpow_div_two_eq_sqrt 1 hx0.le, Real.rpow_one, ← hu, mul_inv_rev]
    ring
  have e2 : x ^ (-(1/2:ℝ)) = u⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_div_two_eq_sqrt 1 hx0.le, Real.rpow_one, ← hu]
  have e3 : (x+1) ^ (-(1/2:ℝ)) = v⁻¹ := by
    rw [Real.rpow_neg hx10.le, Real.rpow_div_two_eq_sqrt 1 hx10.le, Real.rpow_one, ← hv]
  rw [e1, e2, e3]
  exact hkey

/-- The same per-term inequality written with square roots and division. -/
private lemma rpow_neg_three_halves_term_le' (a : ℕ) (ha : 1 ≤ a) :
    (a:ℝ) ^ (-(3/2:ℝ)) ≤ 4 * (1/√(a:ℝ) - 1/√((a:ℝ)+1)) := by
  have hx : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hx0 : (0:ℝ) < (a:ℝ) := by linarith
  have hx10 : (0:ℝ) < (a:ℝ) + 1 := by linarith
  have h := rpow_neg_three_halves_term_le (a:ℝ) hx
  have h1 : (a:ℝ)^(-(1/2:ℝ)) = 1/√(a:ℝ) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_div_two_eq_sqrt 1 hx0.le, Real.rpow_one, one_div]
  have h2 : ((a:ℝ)+1)^(-(1/2:ℝ)) = 1/√((a:ℝ)+1) := by
    rw [Real.rpow_neg hx10.le, Real.rpow_div_two_eq_sqrt 1 hx10.le, Real.rpow_one, one_div]
  rw [h1, h2] at h
  exact h

/-- The partial sums of `n^{-3/2}` are bounded by `4` uniformly in `N`.  Proof: for every `a ≥ 1` one has `a^{-3/2} ≤ 4(1/√a - 1/√(a+1))` (equivalently `3a-1 ≥ √(a(a+1))`, i.e. `8a²-7a+1 ≥ 0`, true for `a ≥ 1`), and `∑_{a=1}^N (1/√a - 1/√(a+1)) = 1 - 1/√(N+1) ≤ 1` telescopes (`Finset.sum_Ico_sub`). -/
theorem rpow_neg_three_halves_sum_le_four (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, (a : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 4 := by
  -- Rewrite `Icc 1 N` as the half-open interval `Ico 1 (N+1)` so that the
  -- telescoping lemma `Finset.sum_Ico_sub` applies.
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  -- Telescoping sum `∑_{a=1}^N (1/√a - 1/√(a+1)) = 1 - 1/√(N+1)`.
  have htelesc : ∑ a ∈ Finset.Ico 1 (N + 1), (1/√(a:ℝ) - 1/√((a:ℝ)+1))
      = 1 - 1/√((N:ℝ)+1) := by
    have h := Finset.sum_Ico_sub (fun k : ℕ => -(1/√(k:ℝ))) (show 1 ≤ N + 1 by omega)
    have h' : ∑ a ∈ Finset.Ico 1 (N + 1), (1/√(a:ℝ) - 1/√((a:ℝ)+1))
        = ∑ a ∈ Finset.Ico 1 (N + 1), (-(1/√(((a+1:ℕ):ℝ))) - (-(1/√(a:ℝ)))) := by
      apply Finset.sum_congr rfl
      intro a ha
      push_cast
      ring
    rw [h', h]
    push_cast
    rw [Real.sqrt_one]
    ring
  rw [hIcc]
  calc ∑ a ∈ Finset.Ico 1 (N + 1), (a:ℝ) ^ (-(3/2:ℝ))
      ≤ ∑ a ∈ Finset.Ico 1 (N + 1), 4 * (1/√(a:ℝ) - 1/√((a:ℝ)+1)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact rpow_neg_three_halves_term_le' a (Finset.mem_Ico.mp ha).1
    _ = 4 * ∑ a ∈ Finset.Ico 1 (N + 1), (1/√(a:ℝ) - 1/√((a:ℝ)+1)) := by
        rw [Finset.mul_sum]
    _ = 4 * (1 - 1/√((N:ℝ)+1)) := by rw [htelesc]
    _ ≤ 4 := by
        have h : (0:ℝ) ≤ 1/√((N:ℝ)+1) := by positivity
        linarith

end Work.LinnikAreas.Density4
