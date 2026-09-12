/-
Elementary identities for the Kronecker-symbol-style function `ksym`
(defined in KR.lean): numerator reduction modulo the denominator,
multiplicativity in the numerator, and the square symbol law.

Main theorems:
  * `ksym_numred`:     ksym c m = ksym c' m whenever m | c - c',
        m ≢ 2 (mod 4) and c, c' coprime to m;
  * `ksym_mul_left`:   ksym (x*y) m = ksym x m * ksym y m;
  * `ksym_sq_coprime`: gcd(s, m) = 1 -> ksym (s^2) m = 1.
-/
import Submission.Apollo.KR
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Apollo

lemma ksym_one (c : ℤ) : ksym c 1 = 1 := by
  have hodd : Odd (1 : ℕ) := by norm_num
  rw [ksym_odd c hodd]
  simp

/-- the Kronecker symbol at 2 is multiplicative in the numerator. -/
lemma kronTwo_mul (x y : ℤ) : kronTwo (x * y) = kronTwo x * kronTwo y := by
  unfold kronTwo
  by_cases h : x * y % 2 = 0
  · have hxory : x % 2 = 0 ∨ y % 2 = 0 := by
      have hd : (2 : ℤ) ∣ x * y := Int.dvd_iff_emod_eq_zero.mpr h
      rcases (Int.prime_two.dvd_mul).1 hd with hdx | hdy
      · left; exact Int.dvd_iff_emod_eq_zero.mp hdx
      · right; exact Int.dvd_iff_emod_eq_zero.mp hdy
    rcases hxory with hx | hy
    · simp [h, hx]
    · simp [h, hy]
  · have hx : x % 2 ≠ 0 := by
      intro hx
      have hd : (2 : ℤ) ∣ x := Int.dvd_iff_emod_eq_zero.mpr hx
      exact h (Int.dvd_iff_emod_eq_zero.mp (dvd_mul_of_dvd_left hd y))
    have hy : y % 2 ≠ 0 := by
      intro hy
      have hd : (2 : ℤ) ∣ y := Int.dvd_iff_emod_eq_zero.mpr hy
      exact h (Int.dvd_iff_emod_eq_zero.mp (dvd_mul_of_dvd_right hd x))
    have hx2 : x % 2 = 1 := by omega
    have hy2 : y % 2 = 1 := by omega
    have hmod : (x * y) % 8 = (x % 8 * (y % 8)) % 8 := by
      rw [Int.mul_emod, Int.mul_emod]
    have hx8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
    have hy8 : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by omega
    rcases hx8 with hx1 | hx1 | hx1 | hx1
    all_goals rcases hy8 with hy1 | hy1 | hy1 | hy1
    all_goals
      simp [h, hx2, hy2, hmod, hx1, hy1] <;> norm_num

/-- odd denominators: the symbol depends only on the numerator modulo m. -/
lemma numred_odd (c c' : ℤ) (m : ℕ) (hodd : Odd m) (hdiv : (m : ℤ) ∣ c - c') :
    ksym c m = ksym c' m := by
  rw [ksym_odd c hodd, ksym_odd c' hodd]
  have hmod : c % (m : ℤ) = c' % (m : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    rcases hdiv with ⟨t, ht⟩
    rw [ht]
    exact Int.mul_emod_right (m : ℤ) t
  rw [jacobiSym.mod_left c m, jacobiSym.mod_left c' m, hmod]

/-- the numerator is odd when it is coprime to an even denominator. -/
lemma odd_of_coprime_even {c : ℤ} {m : ℕ} (hm : Even m) (hg : c.gcd m = 1) : c % 2 = 1 := by
  by_contra h
  have hc0 : c % 2 = 0 := by omega
  have hd2c : (2 : ℤ) ∣ c := Int.dvd_iff_emod_eq_zero.mpr hc0
  rcases hd2c with ⟨a, ha⟩
  have hna : (2 : ℕ) ∣ c.natAbs := by
    rw [ha]
    rw [Int.natAbs_mul]
    norm_num
  have hnm : (2 : ℕ) ∣ m := by
    rcases hm with ⟨k, hk⟩
    rw [hk]
    exact ⟨k, by omega⟩
  have hdiv2 : (2 : ℕ) ∣ Nat.gcd c.natAbs m := Nat.dvd_gcd hna hnm
  have hg1 : Nat.gcd c.natAbs m = 1 := by
    simpa [Int.gcd_eq_natAbs] using hg
  have h2 : (2 : ℕ) ∣ 1 := by rwa [hg1] at hdiv2
  norm_num at h2

/-- ksym c (4k) = ksym c k for odd c: the two 2-factors cancel. -/
lemma ksym_4k (c : ℤ) (k : ℕ) (hcodd : c % 2 = 1) : ksym c (4 * k) = ksym c k := by
  by_cases hk : k = 0
  · subst k; simp [ksym]
  · have h2k0 : 2 * k ≠ 0 := by omega
    have h1 := ksym_even_mul c (b := 2 * k) h2k0
    have h2 := ksym_even_mul c (b := k) hk
    have hk2 : kronTwo c * kronTwo c = 1 := by
      rcases kronTwo_eq_one_or_neg_one hcodd with h1 | h1 <;> rw [h1] <;> norm_num
    calc
      ksym c (4 * k) = ksym c (2 * (2 * k)) := by ring_nf
      _ = ksym c (2 * k) * kronTwo c := h1
      _ = (ksym c k * kronTwo c) * kronTwo c := by rw [h2]
      _ = ksym c k * (kronTwo c * kronTwo c) := by ring
      _ = ksym c k := by rw [hk2, mul_one]

/-- two odd integers equal modulo 8 have equal kronTwo. -/
lemma kronTwo_eq_of_mod8 {c c' : ℤ} (hc : c % 8 = c' % 8) (ho : c % 2 = 1) :
    kronTwo c = kronTwo c' := by
  unfold kronTwo
  have ho' : c' % 2 = 1 := by omega
  rw [ho, ho']
  by_cases h1 : c % 8 = 1 ∨ c % 8 = 7 <;> by_cases h2 : c' % 8 = 1 ∨ c' % 8 = 7 <;>
    simp [h1, h2, hc]

/-- an even natural m satisfies m = 2 * (m/2). -/
lemma two_mul_div_two (m : ℕ) (hm : Even m) : m = 2 * (m / 2) := by
  rcases hm with ⟨k, hk⟩
  rw [hk]
  have hd : (k + k) / 2 = k := by omega
  omega

/-- pulling one factor of 2 out of an even denominator (m ≠ 0). -/
lemma ksym_double (c : ℤ) {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) :
    ksym c m = ksym c (m / 2) * kronTwo c := by
  have hmm : m = 2 * (m / 2) := two_mul_div_two m hm
  have hpos : m / 2 ≠ 0 := by
    intro hz
    rw [hmm, hz, mul_zero] at hm0
    exact hm0 rfl
  have h1 : ksym c (2 * (m / 2)) = ksym c (m / 2) * kronTwo c := ksym_even_mul c hpos
  have hrew : ksym c m = ksym c (2 * (m / 2)) := congrArg (fun t => ksym c t) hmm
  exact hrew.trans h1

/-- c.gcd k = 1 follows from c.gcd m = 1 when k | m. -/
lemma gcd_dvd_of_dvd (c : ℤ) (m k : ℕ) (hkd : k ∣ m) (hg : c.gcd m = 1) : c.gcd k = 1 := by
  have hg12 : c.gcd k ∣ c.gcd m := by
    rw [Int.gcd_eq_natAbs, Int.gcd_eq_natAbs]
    simp
    exact Nat.dvd_gcd (Nat.gcd_dvd_left c.natAbs k)
      (dvd_trans (Nat.gcd_dvd_right c.natAbs k) hkd)
  have hdiv1 : c.gcd k ∣ 1 := by rwa [hg] at hg12
  exact Nat.dvd_one.mp hdiv1


/-- multiplicativity of ksym in the numerator (odd denominators, via the Jacobi
symbol). -/
theorem ksym_mul_left_odd (x y : ℤ) (m : ℕ) (hodd : Odd m) :
    ksym (x * y) m = ksym x m * ksym y m := by
  rw [ksym_odd (x * y) hodd, ksym_odd x hodd, ksym_odd y hodd]
  exact jacobiSym.mul_left x y m


/-- the Kronecker symbol at 2 of an odd square is 1. -/
lemma kronTwo_sq {s : ℤ} (hs : s % 2 = 1) : kronTwo (s ^ 2) = 1 := by
  rw [pow_two, kronTwo_mul]
  rcases kronTwo_eq_one_or_neg_one hs with h1 | h1 <;> rw [h1] <;> norm_num

/-- multiplicativity of ksym in the numerator, for all denominators. -/
theorem ksym_mul_left (x y : ℤ) (m : ℕ) : ksym (x * y) m = ksym x m * ksym y m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp [ksym]
    | succ n =>
        by_cases he : Even (n + 1)
        · have hpos : 0 < n + 1 := by omega
          have hlt : (n + 1) / 2 < n + 1 := Nat.div_lt_self hpos (by norm_num : 1 < 2)
          have hhalf := ih ((n + 1) / 2) hlt
          simp [ksym, he, hhalf, kronTwo_mul]
          ring
        · have hodd : Odd (n + 1) := Nat.not_even_iff_odd.mp he
          rw [ksym_odd (x * y) hodd, ksym_odd x hodd, ksym_odd y hodd]
          exact jacobiSym.mul_left x y (n + 1)

/-- a square numerator coprime to the denominator gives symbol 1. -/
theorem ksym_sq_coprime (s : ℤ) (m : ℕ) (h : s.gcd m = 1) : ksym (s ^ 2) m = 1 := by
  rw [pow_two, ksym_mul_left]
  rcases ksym_eq_one_or_neg_one h with h1 | h1 <;> rw [h1] <;> norm_num

/-- numerator reduction modulo the denominator.  The hypothesis `m ≢ 2 (mod 4)`
(i.e. m odd or divisible by 4) is the exact condition under which the
Kronecker symbol is periodic in the numerator with period m. -/
theorem ksym_numred (c c' : ℤ) (m : ℕ) (hm : ¬ Even m ∨ 4 ∣ m)
    (hc : c.gcd m = 1) (hc' : c'.gcd m = 1) (hdiv : (m : ℤ) ∣ c - c') :
    ksym c m = ksym c' m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm0 : m = 0
    · subst m
      simp [ksym]
    · by_cases hodd : Odd m
      · exact numred_odd c c' m hodd hdiv
      · have hev : Even m := Nat.not_odd_iff_even.mp hodd
        have h4 : 4 ∣ m := by
          rcases hm with hne | h4
          · exact False.elim (hne hev)
          · exact h4
        rcases h4 with ⟨k, hk⟩
        by_cases hk0 : k = 0
        · subst k
          rw [hk]
          simp [ksym]
        · have hcodd : c % 2 = 1 := odd_of_coprime_even (m := m) hev hc
          have hc'odd : c' % 2 = 1 := odd_of_coprime_even (m := m) hev hc'
          have hckm : ksym c m = ksym c k := by
            rw [hk]
            exact ksym_4k c k hcodd
          have hc'km : ksym c' m = ksym c' k := by
            rw [hk]
            exact ksym_4k c' k hc'odd
          have hck : c.gcd k = 1 := gcd_dvd_of_dvd c m k (by rw [hk]; use 4; omega) hc
          have hc'k : c'.gcd k = 1 := gcd_dvd_of_dvd c' m k (by rw [hk]; use 4; omega) hc'
          have hdivk : (k : ℤ) ∣ c - c' := by
            rw [hk] at hdiv
            rcases hdiv with ⟨t, ht⟩
            refine ⟨(4 : ℤ) * t, ?_⟩
            rw [ht]
            norm_num
            ring
          have hlt : k < m := by rw [hk]; omega
          have hmain : ksym c k = ksym c' k := by
            by_cases hkodd : Odd k
            · exact ih k hlt (Or.inl (Nat.not_even_iff_odd.mpr hkodd)) hck hc'k hdivk
            · have hkev : Even k := Nat.not_odd_iff_even.mp hkodd
              by_cases hk4 : 4 ∣ k
              · exact ih k hlt (Or.inr hk4) hck hc'k hdivk
              · -- k ≡ 2 mod 4: strip one factor of 2, numred_odd + kronTwo
                rcases hkev with ⟨j, hkj⟩
                have hk2 : k = 2 * j := by omega
                have hoddj : Odd j := by
                  by_contra hje
                  have hjev : Even j := Nat.not_odd_iff_even.mp hje
                  rcases hjev with ⟨i, hji⟩
                  apply hk4
                  rw [hk2, hji]
                  refine ⟨i, ?_⟩
                  omega
                have hj0 : j ≠ 0 := by
                  intro hj0
                  apply hk0
                  rw [hk2]
                  omega
                have hstrip : ksym c k = ksym c j * kronTwo c := by
                  calc
                    ksym c k = ksym c (2 * j) := by rw [hk2]
                    _ = ksym c j * kronTwo c := ksym_even_mul c (b := j) hj0
                have hstrip' : ksym c' k = ksym c' j * kronTwo c' := by
                  calc
                    ksym c' k = ksym c' (2 * j) := by rw [hk2]
                    _ = ksym c' j * kronTwo c' := ksym_even_mul c' (b := j) hj0
                have hdivj : (j : ℤ) ∣ c - c' := by
                  rcases hdivk with ⟨t, ht⟩
                  refine ⟨(2 : ℤ) * t, ?_⟩
                  rw [ht]
                  rw [hk2]
                  norm_num
                  ring
                have hnumj : ksym c j = ksym c' j := numred_odd c c' j hoddj hdivj
                -- kronTwo c = kronTwo c' from c ≡ c' mod 8 (8 | m since k = 2j):
                have hc8 : c % 8 = c' % 8 := by
                  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
                  have hd8 : (8 : ℤ) ∣ c - c' := by
                    rw [hk] at hdiv
                    rcases hdiv with ⟨t, ht⟩
                    refine ⟨(j : ℤ) * t, ?_⟩
                    rw [ht]
                    rw [hk2]
                    norm_num
                    ring
                  rcases hd8 with ⟨u, hu⟩
                  rw [hu]
                  exact Int.mul_emod_right (8 : ℤ) u
                have hkt : kronTwo c = kronTwo c' := kronTwo_eq_of_mod8 hc8 hcodd
                calc
                  ksym c k = ksym c j * kronTwo c := hstrip
                  _ = ksym c' j * kronTwo c' := by rw [hnumj, hkt]
                  _ = ksym c' k := by rw [hstrip']
          exact hckm.trans (hmain.trans hc'km.symm)

/-- ksym of an odd numerator at denominator 8 equals kronTwo. -/
lemma ksym_8_odd (c : ℤ) (hc : c % 2 = 1) : ksym c 8 = kronTwo c := by
  calc
    ksym c 8 = ksym c 4 * kronTwo c := by
      rw [show (8 : ℕ) = 2 * 4 by norm_num]
      exact ksym_even_mul c (by norm_num : (4 : ℕ) ≠ 0)
    _ = (ksym c 2 * kronTwo c) * kronTwo c := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num]
      rw [ksym_even_mul c (by norm_num : (2 : ℕ) ≠ 0)]
    _ = ((ksym c 1 * kronTwo c) * kronTwo c) * kronTwo c := by
      rw [show (2 : ℕ) = 2 * 1 by norm_num]
      rw [ksym_even_mul c (by norm_num : (1 : ℕ) ≠ 0)]
    _ = kronTwo c := by
      rw [ksym_one c, one_mul]
      rcases kronTwo_eq_one_or_neg_one hc with h1 | h1 <;> rw [h1] <;> norm_num

end Apollo

