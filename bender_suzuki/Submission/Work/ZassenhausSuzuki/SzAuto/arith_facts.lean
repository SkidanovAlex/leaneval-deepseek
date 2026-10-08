import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SzAuto

/-- A Bernoulli-type strict inequality: for `2 ≤ A` and `2 ≤ q`,
`q * (A - 1) < A ^ q - 1`.  Obtained by bounding `q ≤ A ^ (q - 1)`
(using `q - 1 < 2 ^ (q - 1)`) and subtracting. -/
lemma geom_ineq (A q : ℕ) (hA : 2 ≤ A) (hq : 2 ≤ q) :
    q * (A - 1) < A ^ q - 1 := by
  have hq1 : 1 ≤ q := by omega
  have hle : q ≤ A ^ (q - 1) := by
    have h1 : q - 1 < 2 ^ (q - 1) := Nat.lt_pow_self (by norm_num : (1:ℕ) < 2) (n := q - 1)
    have h2 : 2 ^ (q - 1) ≤ A ^ (q - 1) := Nat.pow_le_pow_left hA (q - 1)
    omega
  have hstep2 : A ^ (q - 1) * (A - 1) = A ^ q - A ^ (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_succ, Nat.sub_add_cancel hq1]
  calc q * (A - 1) ≤ A ^ (q - 1) * (A - 1) := Nat.mul_le_mul_right _ hle
    _ = A ^ q - A ^ (q - 1) := hstep2
    _ < A ^ q - 1 :=
        Nat.sub_lt_sub_left (Nat.one_lt_pow (n := q) (by omega) (by omega))
          (Nat.one_lt_pow (n := q - 1) (by omega) (by omega))

theorem arith_facts (n s : ℕ) (hs : 0 < s) (hsn : s < n) :
    0 < (n / n.gcd s) * (2 ^ (n.gcd s) - 1) ∧
    (n / n.gcd s) * (2 ^ (n.gcd s) - 1) < 2 ^ n - 1 ∧
    n ∣ s * ((n / n.gcd s) * (2 ^ (n.gcd s) - 1)) := by
  set d := n.gcd s with hd
  have hdvdn : d ∣ n := Nat.gcd_dvd_left n s
  have hdvds : d ∣ s := Nat.gcd_dvd_right n s
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right n hs
  have hdle : d ≤ s := Nat.gcd_le_right n hs
  have hdlt : d < n := lt_of_le_of_lt hdle hsn
  have hnpos : 0 < n := lt_trans hs hsn
  have hn_eq : n = d * (n / d) := (Nat.mul_div_cancel' hdvdn).symm
  have hne0 : n / d ≠ 0 := by
    intro hc; rw [hn_eq, hc, mul_zero] at hnpos
    exact Nat.lt_irrefl 0 hnpos
  have hne1 : n / d ≠ 1 := by
    intro hc; rw [hn_eq, hc, mul_one] at hdlt
    exact Nat.lt_irrefl d hdlt
  have hq2 : 2 ≤ n / d := (Nat.two_le_iff _).mpr ⟨hne0, hne1⟩
  have hqdpos : 0 < n / d := by omega
  have hA : 2 ≤ 2 ^ d := by
    have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 1 ≤ d by omega)
    simpa using this
  have hpow1 : 0 < 2 ^ d - 1 := by omega
  refine ⟨Nat.mul_pos hqdpos hpow1, ?_, ?_⟩
  · have h := geom_ineq (2 ^ d) (n / d) hA hq2
    have hpow : (2 ^ d) ^ (n / d) = 2 ^ n := by
      rw [← pow_mul, Nat.mul_div_cancel' hdvdn]
    rwa [hpow] at h
  · have h := mul_dvd_mul hdvds (dvd_mul_right (n/d) (2^d - 1))
    rwa [Nat.mul_div_cancel' hdvdn] at h

end Work.ZassenhausSuzuki.SzAuto
