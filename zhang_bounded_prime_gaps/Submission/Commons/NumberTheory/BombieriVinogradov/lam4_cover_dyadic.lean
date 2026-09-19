import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Submission.Commons.NumberTheory.BombieriVinogradov.lam4_block_real_bound

namespace Commons.NumberTheory.BombieriVinogradov

/-- Lower dyadic bound: for `1 ≤ T < m`, the largest dyadic index compatible with `m`
satisfies `T · 2^j < m` where `j = log₂ ((m-1)/T)`. -/
lemma lam4_dyadic_lower (T m : ℕ) (hT : 1 ≤ T) (hm : T < m) :
    T * 2 ^ (Nat.log 2 ((m - 1) / T)) < m := by
  have hne : (m - 1) / T ≠ 0 := by
    have : 0 < (m - 1) / T := Nat.div_pos (by omega) (by omega)
    omega
  have hle : 2 ^ (Nat.log 2 ((m - 1) / T)) ≤ (m - 1) / T := Nat.pow_log_le_self 2 hne
  have h1 : T * 2 ^ (Nat.log 2 ((m - 1) / T)) ≤ T * ((m - 1) / T) :=
    Nat.mul_le_mul_left T hle
  have h2 : T * ((m - 1) / T) ≤ m - 1 := Nat.mul_div_le (m - 1) T
  omega

/-- Upper dyadic bound: for `1 ≤ T < m`, with `j = log₂ ((m-1)/T)` we have
`m ≤ 2 · (T · 2^j)`. -/
lemma lam4_dyadic_upper (T m : ℕ) (hT : 1 ≤ T) (_hm : T < m) :
    m ≤ 2 * (T * 2 ^ (Nat.log 2 ((m - 1) / T))) := by
  have hlt : m - 1 < T * ((m - 1) / T + 1) := Nat.lt_mul_div_succ (m - 1) (by omega)
  have hle1 : m ≤ T * ((m - 1) / T + 1) := by omega
  have hlt2 : (m - 1) / T < 2 ^ (Nat.log 2 ((m - 1) / T) + 1) := by
    have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) ((m - 1) / T)
    simpa [Nat.succ_eq_add_one] using this
  have hle2 : T * ((m - 1) / T + 1) ≤ T * 2 ^ (Nat.log 2 ((m - 1) / T) + 1) :=
    Nat.mul_le_mul_left T (by omega)
  have heq : T * 2 ^ (Nat.log 2 ((m - 1) / T) + 1) = 2 * (T * 2 ^ (Nat.log 2 ((m - 1) / T))) := by
    rw [pow_succ]; ring
  calc m ≤ T * ((m - 1) / T + 1) := hle1
    _ ≤ T * 2 ^ (Nat.log 2 ((m - 1) / T) + 1) := hle2
    _ = 2 * (T * 2 ^ (Nat.log 2 ((m - 1) / T))) := heq

/-- The dyadic index `j = log₂ ((m-1)/T)` is bounded by `log₂ (x/(T·T))` whenever
`1 ≤ T < m`, `m ≤ x` and `T < n/m`. -/
lemma lam4_dyadic_le_log (T x n m : ℕ) (hT : 1 ≤ T) (hn : n ≤ x)
    (hm : T < m) (hdiv : T < n / m) :
    Nat.log 2 ((m - 1) / T) ≤ Nat.log 2 (x / (T * T)) := by
  have hmpos : 0 < m := by omega
  have hlt0 : T * m < n - (m - 1) := (Nat.lt_div_iff_mul_lt hmpos).mp hdiv
  have hlt : T * m < n := lt_of_lt_of_le hlt0 (Nat.sub_le n (m - 1))
  have hltx : T * m < x := lt_of_lt_of_le hlt hn
  have hlow : T * 2 ^ (Nat.log 2 ((m - 1) / T)) < m := lam4_dyadic_lower T m hT hm
  have h1 : T * (T * 2 ^ (Nat.log 2 ((m - 1) / T))) < T * m :=
    (Nat.mul_lt_mul_left (show 0 < T by omega)).mpr hlow
  have h2 : T * (T * 2 ^ (Nat.log 2 ((m - 1) / T))) < x := lt_trans h1 hltx
  have h3 : 2 ^ (Nat.log 2 ((m - 1) / T)) * (T * T) ≤ x := by
    have he : 2 ^ (Nat.log 2 ((m - 1) / T)) * (T * T)
        = T * (T * 2 ^ (Nat.log 2 ((m - 1) / T))) := by ring
    rw [he]; exact le_of_lt h2
  have h4 : 2 ^ (Nat.log 2 ((m - 1) / T)) ≤ x / (T * T) :=
    (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mpr h3
  calc Nat.log 2 ((m - 1) / T)
      = Nat.log 2 (2 ^ (Nat.log 2 ((m - 1) / T))) :=
        (Nat.log_pow (show 1 < 2 by norm_num) _).symm
    _ ≤ Nat.log 2 (x / (T * T)) := Nat.log_mono_right h4

lemma lam4_cover_dyadic (T x n : ℕ) (hT : 1 ≤ T) (hn : n ≤ x) :
    (∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
        ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
          (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)))
      = ∑ j ∈ Finset.range (Nat.log 2 (x / (T * T)) + 1),
          ∑ m ∈ n.divisors.filter (fun m => T * 2 ^ j < m ∧ m ≤ 2 * (T * 2 ^ j) ∧ T < n / m),
            ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
              (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) := by
  have hkey : n.divisors.filter (fun m => T < m ∧ T < n / m)
      = (Finset.range (Nat.log 2 (x / (T * T)) + 1)).biUnion
          (fun j => n.divisors.filter
            (fun m => T * 2 ^ j < m ∧ m ≤ 2 * (T * 2 ^ j) ∧ T < n / m)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨hmdvd, hmT, hdiv⟩
      refine ⟨Nat.log 2 ((m - 1) / T),
        Nat.lt_succ_of_le (lam4_dyadic_le_log T x n m hT hn hmT hdiv),
        hmdvd, lam4_dyadic_lower T m hT hmT, lam4_dyadic_upper T m hT hmT, hdiv⟩
    · rintro ⟨j, _hjlt, hmdvd, hltj, _hlej, hdiv⟩
      refine ⟨hmdvd, ?_, hdiv⟩
      have h1 : T ≤ T * 2 ^ j := by
        calc T = T * 1 := (mul_one T).symm
          _ ≤ T * 2 ^ j := Nat.mul_le_mul_left T Nat.one_le_two_pow
      omega
  have hdisj : (Finset.range (Nat.log 2 (x / (T * T)) + 1) : Set ℕ).PairwiseDisjoint
      (fun j => n.divisors.filter
        (fun m => T * 2 ^ j < m ∧ m ≤ 2 * (T * 2 ^ j) ∧ T < n / m)) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro m hmi hmj
    rw [Finset.mem_filter] at hmi hmj
    obtain ⟨-, hi1, hi2, -⟩ := hmi
    obtain ⟨-, hj1, hj2, -⟩ := hmj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hEq : 2 * (T * 2 ^ i) = T * 2 ^ (i + 1) := by rw [pow_succ]; ring
      have hp : T * 2 ^ (i + 1) ≤ T * 2 ^ j :=
        Nat.mul_le_mul_left T (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [hEq] at hi2
      omega
    · have hEq : 2 * (T * 2 ^ j) = T * 2 ^ (j + 1) := by rw [pow_succ]; ring
      have hp : T * 2 ^ (j + 1) ≤ T * 2 ^ i :=
        Nat.mul_le_mul_left T (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [hEq] at hj2
      omega
  rw [hkey, Finset.sum_biUnion hdisj]

end Commons.NumberTheory.BombieriVinogradov