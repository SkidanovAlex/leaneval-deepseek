import Mathlib
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le
import Submission.Commons.NumberTheory.Harmonic.harm_ge_log_add_half
import Submission.Commons.NumberTheory.Totient.sum_mu_sq_ge_log_alt

/-!
# `∑_{r ≤ z} μ(r)²/φ(r) ≥ log z + 1`

Supporting estimate for the Duffin-Schaeffer project.
-/

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.Totient

noncomputable section

/-- Local value of `c` at `p ^ k`. -/
def cc (p k : ℕ) : ℝ :=
  if k = 1 then (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
  else if k = 2 then -((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) else 0

/-- `cfun n = ∏_{p | n} cc p (v_p n)`. -/
@[simp] lemma cc_one (p : ℕ) : cc p 1 = (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by simp [cc]

@[simp] lemma cc_two (p : ℕ) : cc p 2 = -((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by simp [cc]

def cfun (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, cc p (n.factorization p)

/-- The arithmetic function `c`. -/
def c : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else cfun n, by simp⟩

@[simp] lemma c_apply (n : ℕ) : c n = if n = 0 then 0 else cfun n := rfl

lemma cfun_one : cfun 1 = 1 := by
  simp only [cfun, Nat.primeFactors_one, Finset.prod_empty]

lemma cfun_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) :
    cfun (m * n) = cfun m * cfun n := by
  have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
    Nat.primeFactors_mul hm hn
  have hdisj : Disjoint m.primeFactors n.primeFactors := by
    rw [Finset.disjoint_left]
    intro p hpm hpn
    have hdm : p ∣ m := (Nat.mem_primeFactors.mp hpm).2.1
    have hdn : p ∣ n := (Nat.mem_primeFactors.mp hpn).2.1
    have hp1 : p ∣ 1 := by
      have hg : p ∣ m.gcd n := Nat.dvd_gcd hdm hdn
      rwa [h.gcd_eq_one] at hg
    exact (Nat.mem_primeFactors.mp hpm).1.not_dvd_one hp1
  have hfac : ∀ p, (m * n).factorization p
      = m.factorization p + n.factorization p := by
    intro p
    have := congrArg (fun (f : ℕ →₀ ℕ) => f p) (Nat.factorization_mul hm hn)
    rwa [Finsupp.add_apply] at this
  have hfact : ∀ p ∈ m.primeFactors, (m * n).factorization p = m.factorization p := by
    intro p hpm
    have hpm' : p ∉ n.primeFactors := fun hc => Finset.disjoint_left.mp hdisj hpm hc
    have hpndvd : ¬ p ∣ n := by
      intro hd
      exact hpm' (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hpm).1, hd, hn⟩)
    rw [hfac p, Nat.factorization_eq_zero_of_not_dvd hpndvd, add_zero]
  have hfact2 : ∀ p ∈ n.primeFactors, (m * n).factorization p = n.factorization p := by
    intro p hpn
    have hpn' : p ∉ m.primeFactors := fun hc => Finset.disjoint_left.mp hdisj hc hpn
    have hpndvd : ¬ p ∣ m := by
      intro hd
      exact hpn' (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hpn).1, hd, hm⟩)
    rw [hfac p, Nat.factorization_eq_zero_of_not_dvd hpndvd, zero_add]
  unfold cfun
  rw [hpf, Finset.prod_union hdisj]
  congr 1
  · exact Finset.prod_congr rfl (fun p hp => by rw [hfact p hp])
  · exact Finset.prod_congr rfl (fun p hp => by rw [hfact2 p hp])

lemma c_isMultiplicative : c.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [c_apply, if_neg (one_ne_zero), cfun_one]
  · intro m n hm hn h
    rw [c_apply, c_apply, c_apply, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn)]
    exact cfun_mul hm hn h

/-- The arithmetic function `n ↦ 1/n`. -/
def z1 : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ)⁻¹, by simp⟩

@[simp] lemma z1_apply (n : ℕ) : z1 n = if n = 0 then 0 else (n : ℝ)⁻¹ := rfl

lemma z1_isMultiplicative : z1.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [z1_apply, if_neg (one_ne_zero)]; simp
  · intro m n hm hn _
    rw [z1_apply, z1_apply, z1_apply, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
      Nat.cast_mul, mul_inv]

/-- `g n = μ(n)²/φ(n)`. -/
def g : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ),
    by simp⟩

@[simp] lemma g_apply (n : ℕ) :
    g n = if n = 0 then 0 else ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ) :=
  rfl

lemma g_isMultiplicative : g.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [g_apply, if_neg (one_ne_zero)]; norm_num
  · intro m n hm hn h
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    have hmu : ArithmeticFunction.moebius (m * n) =
        ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
    have htot : Nat.totient (m * n) = Nat.totient m * Nat.totient n := Nat.totient_mul h
    have htot0 : (Nat.totient m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)).ne'
    have htot0' : (Nat.totient n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    rw [g_apply, g_apply, g_apply, if_neg hm, if_neg hn, if_neg hmn, hmu, htot]
    push_cast
    field_simp


/-- `c'(n) = c(n)·n`. -/
def c' : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else cfun n * n, by simp⟩

@[simp] lemma c'_apply (n : ℕ) : c' n = if n = 0 then 0 else cfun n * n := rfl

lemma cfun_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) : cfun (p ^ k) = cc p k := by
  have hk0 : k ≠ 0 := by omega
  unfold cfun
  rw [Nat.primeFactors_pow p hk0, hp.primeFactors, Finset.prod_singleton]
  congr 1
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self, mul_one]

lemma c_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) : c (p ^ k) = cc p k := by
  rw [c_apply, if_neg (pow_ne_zero k hp.ne_zero), cfun_prime_pow hp hk]

lemma c'_isMultiplicative : c'.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [c'_apply, if_neg (one_ne_zero)]; simp [cfun_one]
  · intro m n hm hn h
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    rw [c'_apply, c'_apply, c'_apply, if_neg hm, if_neg hn, if_neg hmn,
      cfun_mul hm hn h]
    push_cast; ring

/-- `h₂(n) = n·μ(n)²/φ(n)`. -/
def h2 : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) * ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
      / (Nat.totient n : ℝ), by simp⟩

@[simp] lemma h2_apply (n : ℕ) : h2 n = if n = 0 then 0 else (n : ℝ) *
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ) := rfl

lemma h2_isMultiplicative : h2.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [h2_apply, if_neg (one_ne_zero)]; norm_num
  · intro m n hm hn h
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    have hmu : ArithmeticFunction.moebius (m * n) =
        ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
    have htot : Nat.totient (m * n) = Nat.totient m * Nat.totient n := Nat.totient_mul h
    rw [h2_apply, h2_apply, h2_apply, if_neg hm, if_neg hn, if_neg hmn, hmu, htot]
    push_cast
    field_simp

lemma c'_prime_pow (p j : ℕ) (hp : p.Prime) :
    c' (p ^ j) = if j = 0 then 1 else cc p j * (p : ℝ) ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, c'_apply, if_neg (one_ne_zero)]; simp [cfun_one]
  · rw [c'_apply, if_neg (pow_ne_zero j hp.ne_zero), cfun_prime_pow hp hj,
      if_neg (by omega : j ≠ 0), Nat.cast_pow]

lemma cc_eq_zero_of_three_le {p j : ℕ} (hj : 3 ≤ j) : cc p j = 0 := by
  simp only [cc, show j ≠ 1 by omega, show j ≠ 2 by omega, if_false]

lemma c'_prime_pow_eq_zero (p j : ℕ) (hp : p.Prime) (hj : 3 ≤ j) : c' (p ^ j) = 0 := by
  rw [c'_prime_pow p j hp, if_neg (by omega), cc_eq_zero_of_three_le hj, zero_mul]

lemma sum_c'_range_three {p : ℕ} (hp : p.Prime) : ∀ m : ℕ,
    ∑ j ∈ Finset.range (m + 3), c' (p ^ j)
      = 1 + cc p 1 * (p:ℝ) + cc p 2 * (p:ℝ)^2 := by
  intro m
  induction m with
  | zero =>
    rw [show (0:ℕ)+3 = 3 by norm_num, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    rw [c'_prime_pow p 0 hp, c'_prime_pow p 1 hp, c'_prime_pow p 2 hp]
    simp
  | succ m ih =>
    rw [show (m+1)+3 = (m+3)+1 by omega, Finset.sum_range_succ, ih,
      c'_prime_pow_eq_zero p (m+3) hp (by omega), add_zero]

/-- The key identity `c' * ζ = h₂`, i.e. `∑_{d | n} c(d) d = n μ(n)²/φ(n)`. -/
lemma c'_mul_zeta_eq_h2 : c' * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = h2 := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (c'_isMultiplicative.mul (ArithmeticFunction.IsMultiplicative.natCast
      ArithmeticFunction.isMultiplicative_zeta)) _ h2_isMultiplicative).mpr ?_
  intro p k hp
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm1 : (p:ℝ) - 1 ≠ 0 := by
    have : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
    linarith
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.divisors_prime_pow hp k, Finset.sum_map]
  change (∑ j ∈ Finset.range (k + 1), c' (p ^ j)) = h2 (p ^ k)
  rcases k with _ | _ | k
  · rw [show (0:ℕ)+1 = 1 by norm_num, Finset.sum_range_one]
    rw [c'_prime_pow p 0 hp, h2_apply, if_neg (pow_ne_zero 0 hp.ne_zero)]
    simp
  · rw [show (1:ℕ)+1 = 2 by norm_num, Finset.sum_range_succ, Finset.sum_range_one,
      c'_prime_pow p 0 hp, c'_prime_pow p 1 hp, h2_apply,
      if_neg (pow_ne_zero 1 hp.ne_zero)]
    rw [if_pos rfl, if_neg (by norm_num : (1:ℕ) ≠ 0)]
    simp only [Nat.zero_add, pow_one, pow_zero, Nat.cast_one, mul_one, ↓reduceIte, cc_one]
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le,
      ArithmeticFunction.moebius_apply_prime hp]
    norm_num
    field_simp
    ring
  · rw [show (Nat.succ (Nat.succ k))+1 = k+3 by omega, sum_c'_range_three hp k]
    rw [h2_apply, if_neg (pow_ne_zero (k+2) hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega),
      if_neg (by omega : k+2 ≠ 1)]
    rw [Nat.totient_prime_pow hp (by omega)]
    simp only [Int.cast_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, zero_div]
    rw [cc_one, cc_two]
    field_simp
    ring

open Commons.NumberTheory.DivisorSum in
/-- The exact identity `G(R) = ∑_{d ≤ R} c(d) H_{⌊R/d⌋}`. -/
theorem sum_mu_sq_eq (R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ))
      = ∑ d ∈ Finset.Icc 1 R, cfun d * (harmonic (R / d) : ℝ) := by
  -- rewrite the summand as `g n`
  have hg : ∀ n ∈ Finset.Icc 1 R,
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ) = g n := by
    intro n hn
    rw [g_apply, if_neg (by have := (Finset.mem_Icc.mp hn).1; omega)]
  rw [Finset.sum_congr rfl hg]
  -- rewrite `g n = (1/n) * ∑_{d | n} c d * d`
  have hgn : ∀ n ∈ Finset.Icc 1 R, g n = (n:ℝ)⁻¹ * ∑ d ∈ n.divisors, cfun d * (d:ℝ) := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hφ : (Nat.totient n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)).ne'
    have hh2 : h2 n = ∑ d ∈ n.divisors, cfun d * (d:ℝ) := by
      rw [← c'_mul_zeta_eq_h2, ArithmeticFunction.coe_mul_zeta_apply]
      apply Finset.sum_congr rfl
      intro d hd
      rw [c'_apply, if_neg (by have := Nat.pos_of_mem_divisors hd; omega)]
    have key : (n:ℝ)⁻¹ * ∑ d ∈ n.divisors, cfun d * (d:ℝ)
        = ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ) := by
      rw [← hh2, h2_apply, if_neg hn0]
      field_simp
    rw [g_apply, if_neg hn0, key]
  rw [Finset.sum_congr rfl hgn]
  -- reindex the double sum
  have hdiv : ∀ n ∈ Finset.Icc 1 R,
      n.divisors = (Finset.Icc 1 R).filter (fun d => d ∣ n) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnR : n ≤ R := (Finset.mem_Icc.mp hn).2
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdv, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdv (by omega),
        le_trans (Nat.le_of_dvd (by omega) hdv) hnR⟩, hdv⟩
    · rintro ⟨⟨hd1, _⟩, hdv⟩
      exact ⟨hdv, by omega⟩
  have hstep : (∑ n ∈ Finset.Icc 1 R,
        (n:ℝ)⁻¹ * ∑ d ∈ n.divisors, cfun d * (d:ℝ))
      = ∑ d ∈ Finset.Icc 1 R,
          cfun d * (d:ℝ) * ∑ n ∈ (Finset.Icc 1 R).filter (fun n => d ∣ n), (n:ℝ)⁻¹ := by
    calc (∑ n ∈ Finset.Icc 1 R, (n:ℝ)⁻¹ * ∑ d ∈ n.divisors, cfun d * (d:ℝ))
        = ∑ n ∈ Finset.Icc 1 R,
            ∑ d ∈ Finset.Icc 1 R,
              (if d ∣ n then cfun d * (d:ℝ) * (n:ℝ)⁻¹ else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hdiv n hn, Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases h : d ∣ n <;> simp [h, mul_assoc, mul_comm, mul_left_comm]
      _ = ∑ d ∈ Finset.Icc 1 R,
            ∑ n ∈ Finset.Icc 1 R,
              (if d ∣ n then cfun d * (d:ℝ) * (n:ℝ)⁻¹ else 0) := Finset.sum_comm
      _ = ∑ d ∈ Finset.Icc 1 R,
            cfun d * (d:ℝ) * ∑ n ∈ (Finset.Icc 1 R).filter (fun n => d ∣ n), (n:ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          by_cases h : d ∣ n <;> simp [h]
  rw [hstep]
  -- evaluate the inner sum
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  rw [show (∑ n ∈ (Finset.Icc 1 R).filter (fun n => d ∣ n), (n:ℝ)⁻¹)
        = (1/(d:ℝ)) * ∑ k ∈ Finset.Icc 1 (R / d), (1:ℝ)/(k:ℝ) by
      simpa only [one_div] using sum_Icc_filter_dvd_inv R d hd1]
  rw [harmonic_cast_eq_sum]
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp

/-- For `1 ≤ z ≤ 5` the excess `G(z) - H_z` is at least `1/2 - 1/(2z)` (a purely rational
statement). -/
lemma E_small (z : ℕ) (h1 : 1 ≤ z) (h5 : z ≤ 5) :
    (1:ℝ)/2 - 1/(2*(z:ℝ)) ≤
      (∑ r ∈ Finset.Icc 1 z,
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ))
        - (harmonic z : ℝ) := by
  have hm4 : ArithmeticFunction.moebius 4 = 0 := by
    rw [show (4:ℕ) = 2^2 by norm_num,
      ArithmeticFunction.moebius_apply_prime_pow (p:=2) (k:=2) (by norm_num) (by norm_num)]
    norm_num
  interval_cases z <;>
    norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ,
      show Nat.totient 2 = 1 by decide, show Nat.totient 3 = 2 by decide,
      show Nat.totient 4 = 2 by decide, show Nat.totient 5 = 4 by decide,
      ArithmeticFunction.moebius_apply_one, hm4,
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
      harmonic]

theorem sum_mu_sq_div_totient_ge_log_add_one (z : ℕ) (hz : 1 ≤ z) :
    Real.log (z : ℝ) + 1 ≤ ∑ r ∈ Finset.Icc 1 z,
      ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) :=
  Commons.NumberTheory.Totient.sum_mu_sq_ge_log_alt z hz



end

end Commons.NumberTheory.Totient
