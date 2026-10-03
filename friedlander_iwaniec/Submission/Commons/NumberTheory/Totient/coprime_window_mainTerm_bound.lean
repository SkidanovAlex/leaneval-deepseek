import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Finset Nat
open scoped Nat
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta
open ArithmeticFunction

namespace Commons.NumberTheory.Totient

/-!
# The Möbius main-term bound for the initial coprime window

`|#{c ∈ [1,C] : (c,m)=1} − C·φ(m)/m| ≤ τ(m)` (reals), for `m ≥ 1`.

The proof uses the exact identities
`#{c ≤ C : (c,m)=1} = Σ_{d | m} μ(d)·⌊C/d⌋` and `φ(m)/m = Σ_{d | m} μ(d)/d`,
so the discrepancy is `Σ_{d | m} μ(d)·(⌊C/d⌋ − C/d)`, whose absolute value is
bounded termwise by `|μ(d)| · 1 ≤ 1`; there are at most `τ(m) = d(m)` terms.
-/

/-- `Σ_{d | n} μ(d)` is the indicator of `n = 1` (as an integer). -/
lemma sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, μ d) = if n = 1 then (1 : ℤ) else 0 := by
  rw [← coe_mul_zeta_apply (f := μ) (x := n)]
  rw [moebius_mul_coe_zeta, one_apply]

/-- The number of multiples of `d` in `[1,C]` is exactly `C / d`. -/
lemma card_multiples_Icc_one (d C : ℕ) :
    ((Finset.Icc 1 C).filter (fun x : ℕ => d ∣ x)).card = C / d := by
  induction C with
  | zero => simp
  | succ C ih =>
      have hins : Finset.Icc 1 (C + 1) = insert (C + 1) (Finset.Icc 1 C) := by
        ext x; simp only [mem_insert, mem_Icc]; omega
      rw [hins]
      by_cases h : d ∣ C + 1
      · rw [Finset.filter_insert, if_pos h]
        rw [Finset.card_insert_of_notMem]
        · rw [Nat.succ_div, if_pos h]
          omega
        · simp
      · rw [Finset.filter_insert, if_neg h]
        rw [Nat.succ_div, if_neg h]
        exact ih

/-- For `m ≥ 1`, the divisors of `gcd c m` are exactly the divisors `d` of `m` with
`d ∣ c`. -/
lemma divisors_gcd_eq_filter (c m : ℕ) (hm : 1 ≤ m) :
    (Nat.gcd c m).divisors = (m.divisors).filter (fun d : ℕ => d ∣ c) := by
  ext d
  rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨hdg, hgne⟩
    constructor
    · constructor
      · exact dvd_trans hdg (Nat.gcd_dvd_right c m)
      · exact ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
    · exact dvd_trans hdg (Nat.gcd_dvd_left c m)
  · rintro ⟨⟨hdr, hrne⟩, hdx⟩
    constructor
    · exact Nat.dvd_gcd hdx hdr
    · have hg : 0 < Nat.gcd c m := Nat.gcd_pos_of_pos_right c (lt_of_lt_of_le Nat.zero_lt_one hm)
      exact ne_of_gt hg

/-- For every `c`, the Möbius sum over the divisors of `gcd c m` is the indicator of
`Nat.Coprime c m`. -/
lemma sum_moebius_gcd_coprime (c m : ℕ) :
    (∑ d ∈ (Nat.gcd c m).divisors, μ d) = if Nat.Coprime c m then (1 : ℤ) else 0 := by
  rw [sum_moebius_divisors (Nat.gcd c m)]

/-- For every `c`, the Möbius sum over the divisors of `gcd c m` equals the indicator
of `Nat.Coprime c m`, as reals. -/
lemma sum_moebius_gcd_coprime_real (c m : ℕ) :
    (if Nat.Coprime c m then (1 : ℝ) else 0) =
      ∑ d ∈ (Nat.gcd c m).divisors, ((μ d : ℤ) : ℝ) := by
  exact_mod_cast (sum_moebius_gcd_coprime c m).symm

/-- For `m ≥ 1`, the real coprime count in `[1,C]` equals
`Σ_{d | m} μ(d) · (C / d)`. -/
lemma coprime_count_moebius_real (C m : ℕ) (hm : 1 ≤ m) :
    (((Finset.Icc 1 C).filter (fun c : ℕ => Nat.Coprime c m)).card : ℝ) =
      ∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) * ((C / d : ℕ) : ℝ) := by
  classical
  rw [← Finset.sum_boole (fun c : ℕ => Nat.Coprime c m) (Finset.Icc 1 C)]
  calc
    (∑ c ∈ (Finset.Icc 1 C), (if Nat.Coprime c m then (1 : ℝ) else 0))
        = ∑ c ∈ (Finset.Icc 1 C), (∑ d ∈ (Nat.gcd c m).divisors, ((μ d : ℤ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            exact sum_moebius_gcd_coprime_real c m
    _ = ∑ c ∈ (Finset.Icc 1 C), (∑ d ∈ m.divisors, if d ∣ c then ((μ d : ℤ) : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            rw [divisors_gcd_eq_filter c m hm]
            rw [Finset.sum_filter]
    _ = ∑ d ∈ m.divisors, (∑ c ∈ (Finset.Icc 1 C), if d ∣ c then ((μ d : ℤ) : ℝ) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) * ((C / d : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            calc
              (∑ c ∈ (Finset.Icc 1 C), if d ∣ c then ((μ d : ℤ) : ℝ) else 0)
                  = ∑ c ∈ (Finset.Icc 1 C),
                      ((μ d : ℤ) : ℝ) * (if d ∣ c then (1 : ℝ) else 0) := by
                      refine Finset.sum_congr rfl ?_
                      intro c hc
                      by_cases h : d ∣ c <;> simp [h]
              _ = ((μ d : ℤ) : ℝ) * (∑ c ∈ (Finset.Icc 1 C), (if d ∣ c then (1 : ℝ) else 0)) := by
                      rw [Finset.mul_sum]
              _ = ((μ d : ℤ) : ℝ) * ((C / d : ℕ) : ℝ) := by
                      congr 1
                      rw [Finset.sum_boole (fun c : ℕ => d ∣ c)]
                      rw [card_multiples_Icc_one d C]


/-- Möbius inversion of `Nat.sum_totient`: `φ(n) = ∑_{a·b=n} μ(a)·b` as rationals. -/
lemma sum_antidiag_moebius_snd_eq_totient (m : ℕ) (hm : 0 < m) :
    (∑ x ∈ m.divisorsAntidiagonal, (((μ x.1 : ℤ) : ℚ) * (x.2 : ℚ))) = (Nat.totient m : ℚ) := by
  have hprem : ∀ n : ℕ, 0 < n → (∑ i ∈ n.divisors, ((Nat.totient i : ℕ) : ℚ)) = (n : ℚ) := by
    intro n hn
    exact_mod_cast (Nat.sum_totient n)
  have hres := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℚ)
    (f := fun i => ((Nat.totient i : ℕ) : ℚ)) (g := fun i => (i : ℚ))).mp hprem
  exact hres m hm

/-- Changing variables `(a,b) ↦ (a, n/a)` turns the antidiagonal sum into a divisor sum. -/
lemma sum_antidiag_eq_sum_div_moebius (m : ℕ) :
    (∑ x ∈ m.divisorsAntidiagonal, (((μ x.1 : ℤ) : ℚ) * (x.2 : ℚ))) =
      ∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) * ((m / d : ℕ) : ℚ)) := by
  rw [← Nat.map_div_right_divisors]
  rw [Finset.sum_map]
  rfl

/-- `∑_{d | m} μ(d)·(m/d) = φ(m)` for `m ≥ 1`. -/
lemma sum_moebius_mul_natDiv_eq_totient (m : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) * ((m / d : ℕ) : ℚ))) = (Nat.totient m : ℚ) := by
  rw [← sum_antidiag_eq_sum_div_moebius m]
  exact sum_antidiag_moebius_snd_eq_totient m (lt_of_lt_of_le zero_lt_one hm)

/-- For `d ∣ m`, `m · μ(d)/d = μ(d) · (m/d)` in `ℚ`. -/
lemma moebius_ratio_mul (m d : ℕ) (hm : 0 < m) (hd : d ∣ m) :
    (m : ℚ) * (((μ d : ℤ) : ℚ) / (d : ℚ)) = ((μ d : ℤ) : ℚ) * ((m / d : ℕ) : ℚ) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hm
  have hd0q : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  have hdc : ((d : ℚ) * ((m / d : ℕ) : ℚ)) = (m : ℚ) := by
    have hm' : d * (m / d) = m := Nat.mul_div_cancel' hd
    exact_mod_cast hm'
  have hcancel : ((d : ℚ) * ((m / d : ℕ) : ℚ)) * (d : ℚ)⁻¹ = ((m / d : ℕ) : ℚ) := by
    calc
      ((d : ℚ) * ((m / d : ℕ) : ℚ)) * (d : ℚ)⁻¹
          = (d : ℚ) * (d : ℚ)⁻¹ * ((m / d : ℕ) : ℚ) := by ring
      _ = (1 : ℚ) * ((m / d : ℕ) : ℚ) := by rw [mul_inv_cancel₀ hd0q]
      _ = ((m / d : ℕ) : ℚ) := by rw [one_mul]
  calc
    (m : ℚ) * (((μ d : ℤ) : ℚ) / (d : ℚ))
        = ((μ d : ℤ) : ℚ) * ((m : ℚ) * (d : ℚ)⁻¹) := by
          rw [div_eq_mul_inv]
          ring
    _ = ((μ d : ℤ) : ℚ) * (((d : ℚ) * ((m / d : ℕ) : ℚ)) * (d : ℚ)⁻¹) := by rw [hdc]
    _ = ((μ d : ℤ) : ℚ) * ((m / d : ℕ) : ℚ) := by rw [hcancel]

/-- `∑_{d | m} μ(d)/d = φ(m)/m` for `m ≥ 1`, as rationals. -/
lemma sum_moebius_div_eq_phi_ratio (m : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) / (d : ℚ))) = ((Nat.totient m : ℚ) / (m : ℚ)) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hconv : (∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) * ((m / d : ℕ) : ℚ))) =
      (Nat.totient m : ℚ) := sum_moebius_mul_natDiv_eq_totient m hm
  have hmq0 : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
  have hleft : (m : ℚ) * (∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) / (d : ℚ))) =
      (Nat.totient m : ℚ) := by
    calc
      (m : ℚ) * (∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) / (d : ℚ)))
          = ∑ d ∈ m.divisors, (m : ℚ) * (((μ d : ℤ) : ℚ) / (d : ℚ)) := by
              rw [Finset.mul_sum]
      _ = ∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) * ((m / d : ℕ) : ℚ)) :=
              Finset.sum_congr rfl (fun d hd =>
                moebius_ratio_mul m d hmpos (Nat.dvd_of_mem_divisors hd))
      _ = (Nat.totient m : ℚ) := hconv
  have hright : (m : ℚ) * ((Nat.totient m : ℚ) / (m : ℚ)) = (Nat.totient m : ℚ) := by
    calc
      (m : ℚ) * ((Nat.totient m : ℚ) / (m : ℚ)) = (m : ℚ) * ((Nat.totient m : ℚ) * (m : ℚ)⁻¹) := by
        rw [div_eq_mul_inv]
      _ = (Nat.totient m : ℚ) * ((m : ℚ) * (m : ℚ)⁻¹) := by ring
      _ = (Nat.totient m : ℚ) := by rw [mul_inv_cancel₀ hmq0, mul_one]
  have hmul : (m : ℚ) * (∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) / (d : ℚ))) =
      (m : ℚ) * ((Nat.totient m : ℚ) / (m : ℚ)) := by
    rw [hleft, hright]
  exact mul_left_cancel₀ hmq0 hmul

/-- `Σ_{d | m} μ(d)/d = φ(m)/m` for `m ≥ 1`, as reals. -/
lemma sum_moebius_div_eq_phi_ratio_real (m : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) / (d : ℝ)) = ((Nat.totient m : ℝ) / (m : ℝ)) := by
  have hq := sum_moebius_div_eq_phi_ratio m hm
  have hqr := congrArg (fun q : ℚ => (q : ℝ)) hq
  have hsum : (∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) / (d : ℝ)) =
      (((∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) / (d : ℚ))) : ℚ) : ℝ) := by
    rw [show (((∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) / (d : ℚ))) : ℚ) : ℝ)
        = ∑ d ∈ m.divisors, (((((μ d : ℤ) : ℚ) / (d : ℚ)) : ℚ) : ℝ) by simp]
    refine Finset.sum_congr rfl ?_
    intro d hd
    norm_num [Rat.cast_div]
  calc
    (∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) / (d : ℝ))
        = (((∑ d ∈ m.divisors, (((μ d : ℤ) : ℚ) / (d : ℚ))) : ℚ) : ℝ) := hsum
    _ = ((Nat.totient m : ℝ) / (m : ℝ)) := by
          rw [hqr]
          norm_num [Rat.cast_div]

/-- `|μ(d)| ≤ 1` as reals. -/
lemma abs_moebius_real_le_one (d : ℕ) : |((μ d : ℤ) : ℝ)| ≤ 1 := by
  have hz : |μ d| ≤ 1 := abs_moebius_le_one (n := d)
  exact_mod_cast hz

/-- The fractional part of `C / d` is within `1` of the natural division `C / d`. -/
lemma floor_div_sub_le_one (C d : ℕ) (hd : 1 ≤ d) :
    |(((C / d : ℕ) : ℝ) - (C : ℝ) / (d : ℝ))| ≤ 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  let q : ℕ := C / d
  have hq1 : (q : ℝ) ≤ (C : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]
    have hnat : q * d ≤ C := Nat.div_mul_le_self C d
    exact_mod_cast hnat
  have hq2 : (C : ℝ) / (d : ℝ) < (q : ℝ) + 1 := by
    rw [div_lt_iff₀ hdR]
    have hnat : C < d * (q + 1) := Nat.lt_mul_div_succ C hd
    have hcast : (C : ℝ) < (d : ℝ) * (((q + 1 : ℕ) : ℝ)) := by exact_mod_cast hnat
    have hcast' : (C : ℝ) < ((q : ℝ) + 1) * (d : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hcast
    exact hcast'
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **Main-term bound for the initial coprime window.**  For `m ≥ 1` and every natural
`C`, the number of `c ∈ [1,C]` coprime to `m` differs from `C·φ(m)/m` by at most the
number of divisors of `m`, as reals. -/
theorem coprime_window_mainTerm_bound (C m : ℕ) (hm : 1 ≤ m) :
    |((((Finset.Icc 1 C).filter (fun c : ℕ => Nat.Coprime c m)).card : ℝ) -
        (C : ℝ) * (Nat.totient m : ℝ) / (m : ℝ))| ≤ (m.divisors.card : ℝ) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 C).filter (fun c : ℕ => Nat.Coprime c m)
  change |(S.card : ℝ) - (C : ℝ) * (Nat.totient m : ℝ) / (m : ℝ)| ≤ (m.divisors.card : ℝ)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hm))
  have hdiv : ∀ d ∈ m.divisors, (d : ℝ) ≠ 0 := by
    intro d hd
    have hpos : 0 < d := Nat.pos_of_mem_divisors hd
    exact_mod_cast (ne_of_gt hpos)
  have hcnt_real : (S.card : ℝ) =
      ∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) * ((C / d : ℕ) : ℝ) := by
    simpa [S] using coprime_count_moebius_real C m hm
  have hmain : (C : ℝ) * (Nat.totient m : ℝ) / (m : ℝ) =
      ∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) * ((C : ℝ) / (d : ℝ)) := by
    have hr := sum_moebius_div_eq_phi_ratio_real m hm
    calc
      (C : ℝ) * (Nat.totient m : ℝ) / (m : ℝ)
          = (C : ℝ) * ((Nat.totient m : ℝ) / (m : ℝ)) := by
              field_simp [hm0]
      _ = (C : ℝ) * (∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) / (d : ℝ)) := by rw [hr]
      _ = ∑ d ∈ m.divisors, (C : ℝ) * (((μ d : ℤ) : ℝ) / (d : ℝ)) := by
              rw [Finset.mul_sum]
      _ = ∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) * ((C : ℝ) / (d : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro d hd
              field_simp [hdiv d hd]
  have hdiff : (S.card : ℝ) - (C : ℝ) * (Nat.totient m : ℝ) / (m : ℝ) =
      ∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) *
        (((C / d : ℕ) : ℝ) - (C : ℝ) / (d : ℝ)) := by
    rw [hcnt_real, hmain, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro d hd
    ring
  calc
    |(S.card : ℝ) - (C : ℝ) * (Nat.totient m : ℝ) / (m : ℝ)|
        = |∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ) *
            (((C / d : ℕ) : ℝ) - (C : ℝ) / (d : ℝ))| := by
              rw [hdiff]
    _ ≤ ∑ d ∈ m.divisors, |((μ d : ℤ) : ℝ) *
            (((C / d : ℕ) : ℝ) - (C : ℝ) / (d : ℝ))| := by
              exact Finset.abs_sum_le_sum_abs (fun d : ℕ =>
                ((μ d : ℤ) : ℝ) * (((C / d : ℕ) : ℝ) - (C : ℝ) / (d : ℝ))) m.divisors
    _ ≤ ∑ d ∈ m.divisors, |(((C / d : ℕ) : ℝ) - (C : ℝ) / (d : ℝ))| := by
              refine Finset.sum_le_sum ?_
              intro d hd
              have hμ : |((μ d : ℤ) : ℝ)| ≤ 1 := abs_moebius_real_le_one d
              let e : ℝ := (((C / d : ℕ) : ℝ) - (C : ℝ) / (d : ℝ))
              calc
                |((μ d : ℤ) : ℝ) * e| ≤ 1 * |e| := by
                      rw [abs_mul]
                      exact mul_le_mul hμ le_rfl (abs_nonneg e) (by norm_num)
                _ = |e| := by simp
    _ ≤ ∑ d ∈ m.divisors, (1 : ℝ) := by
              refine Finset.sum_le_sum ?_
              intro d hd
              simpa using (floor_div_sub_le_one C d (Nat.pos_of_mem_divisors hd))
    _ = (m.divisors.card : ℝ) := by
              simp

end Commons.NumberTheory.Totient