import Mathlib
import Submission.Work.Fx.LogTwoDefs

/-!
# The analytic bound for `logU`

`logU p` is within one unit in the last place of `2^p log 2`:
`Real.log 2 = Σ_{m≥1} 1/(m 2^m)` (Mercator series at `x = 1/2`, with the remainder bound
`Real.abs_log_sub_add_sum_range_le`), and `logS p (logM p + 1)` is the same sum truncated at
`logM p` terms with every summand rounded down, so the total accumulated error is at most
`logM p + 1 ≤ 2 ^ logG p`; the final nearest-integer rounding loses another `1/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Fx

open HvdH

/-- `⌊a/b⌋` bounds in `ℝ`. -/
theorem natDiv_bounds (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) ∧ (a : ℝ) / (b : ℝ) < ((a / b : ℕ) : ℝ) + 1 := by
  constructor
  · exact Nat.cast_div_le
  · have h1 : a < (a / b) * b + b := by
      have h2 : (a / b) * b + a % b = a := Nat.div_add_mod' a b
      have h3 := Nat.mod_lt a hb
      omega
    have h4 : (a : ℝ) < ((a / b : ℕ) : ℝ) * b + b := by exact_mod_cast h1
    rw [div_lt_iff₀ (by exact_mod_cast hb : (0 : ℝ) < (b : ℝ))]
    linarith [h4]

theorem two_p_le (p : ℕ) : 2 * p + 22 ≤ 2 ^ (p + 5) := by
  induction p with
  | zero => norm_num
  | succ k ih =>
    have h3 : 2 * k + 24 ≤ 2 * (2 * k + 22) := by omega
    have h4 : 2 * (2 * k + 22) ≤ 2 * 2 ^ (k + 5) := Nat.mul_le_mul_left 2 ih
    have h5 : 2 * 2 ^ (k + 5) = 2 ^ (k + 6) := by rw [← pow_succ']
    calc 2 * (k + 1) + 22 = 2 * k + 24 := by ring
      _ ≤ 2 * (2 * k + 22) := h3
      _ ≤ 2 * 2 ^ (k + 5) := h4
      _ = 2 ^ (k + 1 + 5) := by rw [h5]

/-- `N`-th partial sum of the Mercator series at `1/2`. -/
noncomputable def mercSum (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1))

/-- The same sum scaled by `2^logM p`. -/
noncomputable def truncSum (p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (logM p), (2 : ℝ) ^ logM p / (((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1))

/-- The integer truncated sum, as a real number. -/
noncomputable def intSum (p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (logM p), ((logA p (j + 1) : ℕ) : ℝ)

/-- Remainder of the Mercator series at `x = 1/2`: `|Σ_{m≤N} 1/(m 2^m) - log 2| ≤ 2^{-N}`. -/
theorem mercator_err (N : ℕ) : |mercSum N - Real.log 2| ≤ (1 / 2 : ℝ) ^ N := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 2 : ℝ)) (by norm_num) N
  have hlog : Real.log (1 - (1 / 2 : ℝ)) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have habs : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  have hgeo : (1 / 2 : ℝ) ^ (N + 1) / (1 - 1 / 2) = (1 / 2 : ℝ) ^ N := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, pow_succ, mul_div_assoc,
      div_self (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_one]
  rw [hlog, habs] at h
  rw [hgeo] at h
  have h1 : (∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) = mercSum N := by
    rw [mercSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, one_pow, one_div]
    push_cast
    field_simp
  rw [h1, ← sub_eq_add_neg] at h
  exact h

/-- Every summand `logA p m` is the floor of `2^logP p/(m 2^m)`. -/
theorem logA_bounds (p m : ℕ) (hm : 1 ≤ m) :
    ((logA p m : ℕ) : ℝ) ≤ (2 : ℝ) ^ logP p / ((m : ℝ) * 2 ^ m) ∧
      (2 : ℝ) ^ logP p / ((m : ℝ) * 2 ^ m) < ((logA p m : ℕ) : ℝ) + 1 := by
  have hA : ((logA p m : ℕ) : ℝ) = ((2 ^ logP p / (2 ^ m * m) : ℕ) : ℝ) := by
    rw [show logA p m = 2 ^ logP p / (2 ^ m * m) from by
      simp only [logA, logD]; rw [Nat.div_div_eq_div_mul]]
  rw [hA]
  have h := natDiv_bounds (2 ^ logP p) (2 ^ m * m) (by positivity)
  constructor
  · calc ((2 ^ logP p / (2 ^ m * m) : ℕ) : ℝ)
        ≤ ((2 ^ logP p : ℕ) : ℝ) / ((2 ^ m * m : ℕ) : ℝ) := h.1
      _ = (2 : ℝ) ^ logP p / ((m : ℝ) * 2 ^ m) := by push_cast; ring
  · calc (2 : ℝ) ^ logP p / ((m : ℝ) * 2 ^ m)
        = ((2 ^ logP p : ℕ) : ℝ) / ((2 ^ m * m : ℕ) : ℝ) := by push_cast; ring
      _ < ((2 ^ logP p / (2 ^ m * m) : ℕ) : ℝ) + 1 := h.2

/-- `intSum` is the truncated sum. -/
theorem logS_eq_intSum (p : ℕ) : (logS p (logM p + 1) : ℝ) = intSum p := by
  have hzero : logA p (logM p + 1) = 0 := by
    have h1 : 2 ^ logP p / 2 ^ (logM p + 1) = 0 := by
      apply Nat.div_eq_of_lt
      rw [logP_eq_logM]
      exact Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self _)
    simp only [logA, logD, h1, Nat.zero_div]
  rw [logS_succ, hzero, add_zero]
  rw [intSum, logS, Nat.cast_sum]

/-- `truncSum` is the scaled Mercator sum. -/
theorem truncSum_eq (p : ℕ) : truncSum p = (2 : ℝ) ^ logM p * mercSum (logM p) := by
  rw [truncSum, mercSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Error of the truncated sum. -/
theorem logS_err (p : ℕ) :
    |(2 : ℝ) ^ logP p * Real.log 2 - (logS p (logM p + 1) : ℝ)| ≤ logM p + 1 := by
  have hR : (2 : ℝ) ^ logP p = 2 ^ logM p := by rw [logP_eq_logM]
  have hterm : ∀ j ∈ Finset.range (logM p),
      ((logA p (j + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ logM p / (((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1)) ∧
      (2 : ℝ) ^ logM p / (((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1))
        < ((logA p (j + 1) : ℕ) : ℝ) + 1 := by
    intro j _
    have h := logA_bounds p (j + 1) (by omega)
    rw [hR] at h
    exact h
  have hsum1 : intSum p ≤ truncSum p := by
    rw [intSum, truncSum]
    exact Finset.sum_le_sum (fun j hj => (hterm j hj).1)
  have hsum2 : truncSum p ≤ intSum p + logM p := by
    rw [intSum, truncSum]
    calc (∑ j ∈ Finset.range (logM p),
            (2 : ℝ) ^ logM p / (((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1)))
        ≤ ∑ j ∈ Finset.range (logM p), (((logA p (j + 1) : ℕ) : ℝ) + 1) :=
          Finset.sum_le_sum (fun j hj => le_of_lt (hterm j hj).2)
      _ = (∑ j ∈ Finset.range (logM p), ((logA p (j + 1) : ℕ) : ℝ)) + logM p := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hmerc := mercator_err (logM p)
  have hmerc' : mercSum (logM p) - Real.log 2 ≤ (1 / 2 : ℝ) ^ logM p := (abs_le.mp hmerc).2
  have hmerc'' : -((1 / 2 : ℝ) ^ logM p) ≤ mercSum (logM p) - Real.log 2 := (abs_le.mp hmerc).1
  have hpow : (2 : ℝ) ^ logM p * (1 / 2 : ℝ) ^ logM p = 1 := by
    rw [one_div, inv_pow]
    field_simp
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ logM p := by positivity
  rw [logS_eq_intSum]
  rw [truncSum_eq] at hsum1 hsum2
  have hSN : (2 : ℝ) ^ logM p * Real.log 2 - intSum p
      ≤ (2 : ℝ) ^ logM p * (1 / 2 : ℝ) ^ logM p + logM p := by
    nlinarith [hsum1, hsum2, hmerc', hpow, hpowpos, mul_nonneg (le_of_lt hpowpos) (le_of_lt hpowpos)]
  have hSN2 : -((2 : ℝ) ^ logM p * (1 / 2 : ℝ) ^ logM p) ≤
      (2 : ℝ) ^ logM p * Real.log 2 - intSum p := by
    nlinarith [hsum1, hmerc'', hpow, mul_le_mul_of_nonneg_left hmerc'' (le_of_lt hpowpos)]
  rw [hpow] at hSN hSN2
  rw [hR, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- `logU p` is within one unit in the last place of `2^p log 2`. -/
theorem logMainBoundAux (p : ℕ) (hp : 100 ≤ p) : |(logU p : ℝ) - 2 ^ p * Real.log 2| ≤ 1 := by
  set G : ℕ := logG p with hG
  set S : ℝ := (logS p (logM p + 1) : ℝ) with hS
  have hE' : |(2 : ℝ) ^ logP p * Real.log 2 - S| ≤ logM p + 1 := by
    have h := logS_err p
    rw [← hS] at h
    exact h
  have hGN : logM p + 1 ≤ 2 ^ G := by
    have h1 : 2 * p + 22 ≤ 2 ^ (p + 5) := two_p_le p
    have h2 : 2 ^ (p + 5) ≤ 2 ^ G := by
      rw [hG, logG]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [logM] at h1 ⊢
    omega
  have hRG : (2 : ℝ) ^ logP p = 2 ^ (G + 1) * 2 ^ p := by
    rw [hG, logP_eq, pow_add, pow_add]
    ring
  have hdiv := natDiv_bounds (logS p (logM p + 1) + 2 ^ logG p) (2 ^ (logG p + 1)) (by positivity)
  have hnum : (((logS p (logM p + 1) + 2 ^ logG p : ℕ)) : ℝ) = S + (2 : ℝ) ^ G := by
    rw [hS, hG]; push_cast; ring
  have hden : (((2 ^ (logG p + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (G + 1) := by
    rw [hG]; push_cast; ring
  rw [hnum, hden] at hdiv
  have hx : (S + (2 : ℝ) ^ G) / 2 ^ (G + 1) = S / 2 ^ (G + 1) + 1 / 2 := by
    rw [add_div]
    congr 1
    rw [pow_succ]
    have h1 : (2 : ℝ) ^ G ≠ 0 := by positivity
    field_simp
  have hx1 : S / 2 ^ (G + 1) - 2 ^ p * Real.log 2
      = -(((2 : ℝ) ^ logP p * Real.log 2 - S) / 2 ^ (G + 1)) := by
    rw [hRG]
    have h1 : (2 : ℝ) ^ (G + 1) ≠ 0 := by positivity
    field_simp
    ring
  have habs1 : |S / 2 ^ (G + 1) - 2 ^ p * Real.log 2| ≤ 1 / 2 := by
    rw [hx1, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (G + 1))]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (G + 1))]
    have h2 : (((logM p + 1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ G := by exact_mod_cast hGN
    have h2' : ((logM p : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ G := by
      have h := h2
      push_cast at h
      exact h
    have h3 : (1 / 2 : ℝ) * 2 ^ (G + 1) = (2 : ℝ) ^ G := by
      rw [pow_succ]; ring
    linarith [hE', h2', h3]
  have hU1 : ((logU p : ℕ) : ℝ) ≤ S / 2 ^ (G + 1) + 1 / 2 := by
    rw [← hx]
    exact hdiv.1
  have hU2 : S / 2 ^ (G + 1) + 1 / 2 < ((logU p : ℕ) : ℝ) + 1 := by
    rw [← hx]
    exact hdiv.2
  rw [abs_le] at habs1 ⊢
  constructor <;> linarith [habs1.1, habs1.2, hU1, hU2]

end Work.Fx
