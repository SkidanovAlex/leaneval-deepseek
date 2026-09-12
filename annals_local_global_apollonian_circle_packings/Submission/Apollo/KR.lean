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
/-
Kronecker symbol library for the χ₂ theory.
The Kronecker symbol (a | b) for a : ℤ, b : ℕ is defined recursively:
  (a | 0) = 1   (convention, never needed)
  (a | b) = jacobiSym a b            if b is odd
  (a | 2b) = (a | b) * (a | 2)       where (a | 2) is the supplementary law
This agrees with the classical Kronecker symbol for positive denominators.

The final definition `pairChi x y` is the χ₂ value attached to a circle of
curvature x with a coprime co-occurring circle of curvature y; the key lemma
`pairChi_square` says that square curvatures force χ₂ = 1.
-/
set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Apollo

/-- The value of the Kronecker symbol (a | 2): 0 if a is even, and for odd a
it is 1 iff a ≡ ±1 mod 8, −1 otherwise. -/
def kronTwo (a : ℤ) : ℤ :=
  if a % 2 = 0 then 0 else if a % 8 = 1 ∨ a % 8 = 7 then 1 else -1

/-- The Kronecker symbol (a | b) for positive denominator b. -/
def ksym : ℤ → ℕ → ℤ
| a, 0 => 1
| a, b + 1 => if Even (b + 1) then ksym a ((b + 1) / 2) * kronTwo a else jacobiSym a (b + 1)
termination_by _a b => b
decreasing_by
  simp_wf
  omega

lemma kronTwo_eq_zero_iff (a : ℤ) : kronTwo a = 0 ↔ a % 2 = 0 := by
  unfold kronTwo
  by_cases h : a % 2 = 0
  · simp [h]
  · by_cases h2 : a % 8 = 1 ∨ a % 8 = 7 <;> simp [h, h2]

lemma kronTwo_eq_one_or_neg_one {a : ℤ} (ha : a % 2 = 1) : kronTwo a = 1 ∨ kronTwo a = -1 := by
  unfold kronTwo
  rw [ha]
  by_cases h : a % 8 = 1 ∨ a % 8 = 7 <;> simp [h]

/-- Odd denominators: the Kronecker symbol is the Jacobi symbol. -/
lemma ksym_odd (a : ℤ) {b : ℕ} (hb : Odd b) : ksym a b = jacobiSym a b := by
  cases b with
  | zero => exfalso; exact (Nat.not_even_iff_odd.mpr hb) (by simp)
  | succ b =>
      have hne : ¬ Even (b + 1) := by
        exact Nat.not_even_iff_odd.mpr hb
      simp [ksym, hne]

/-- Even denominators: (a | 2b) = (a | b)(a | 2) for b ≥ 1. -/
lemma ksym_even_mul (a : ℤ) {b : ℕ} (hb : b ≠ 0) : ksym a (2 * b) = ksym a b * kronTwo a := by
  have hn : 2 * b = (2 * b - 1) + 1 := by omega
  have he : Even (2 * b - 1 + 1) := by
    rw [hn]
    exact ⟨b, by omega⟩
  have hdiv : (2 * b - 1 + 1) / 2 = b := by
    rw [show 2 * b - 1 + 1 = 2 * b by omega]
    exact Nat.mul_div_right b (by norm_num : 0 < 2)
  rw [hn]
  simp only [ksym]
  rw [if_pos he, hdiv]

-- an integer coprime to 2 is odd
lemma emod_two_eq_one_of_gcd_two (a : ℤ) (h : a.gcd 2 = 1) : a % 2 = 1 := by
  have hne : a % 2 ≠ 0 := by
    intro hz
    have hd : (2 : ℤ) ∣ a := (Int.dvd_iff_emod_eq_zero (a := 2) (b := a)).2 hz
    rcases hd with ⟨t, ht⟩
    have hnat : a.natAbs = 2 * t.natAbs := by
      rw [ht]
      simp [Int.natAbs_mul]
    rw [Int.gcd_def, hnat] at h
    have htwoabs : Int.natAbs 2 = 2 := by norm_num
    rw [htwoabs] at h
    have hg' : Nat.gcd (2 * t.natAbs) 2 = 2 * Nat.gcd t.natAbs 1 := by
      rw [show (2 : ℕ) = 2 * 1 by norm_num, Nat.gcd_mul_left]
    rw [hg'] at h
    omega
  rcases Int.emod_two_eq_zero_or_one a with h0 | h1
  · exact False.elim (hne h0)
  · exact h1

/-- Coprime arguments give value ±1. -/
lemma ksym_eq_one_or_neg_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : ksym a b = 1 ∨ ksym a b = -1 := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    cases b with
    | zero => simp [ksym]
    | succ b =>
        by_cases he : Even (b + 1)
        · rcases he with ⟨c, hc⟩
          have hcpos : c ≠ 0 := by
            intro hc0; omega
          have hbform : b + 1 = 2 * c := by omega
          have hclt : c < b + 1 := by omega
          have hgcdc : a.gcd c = 1 := by
            apply Int.gcd_eq_one_of_gcd_mul_right_eq_one_left (m := c) (n := 2)
            simpa [hbform, mul_comm] using h
          have hgcd2 : a.gcd 2 = 1 := by
            apply Int.gcd_eq_one_of_gcd_mul_right_eq_one_right (m := c) (n := 2)
            simpa [hbform, mul_comm] using h
          have hodd : a % 2 = 1 := emod_two_eq_one_of_gcd_two a hgcd2
          rw [hbform, ksym_even_mul a hcpos]
          rcases ih c hclt hgcdc with hc1 | hc1
          · rcases kronTwo_eq_one_or_neg_one hodd with ht1 | ht1
            · left; rw [hc1, ht1]; norm_num
            · right; rw [hc1, ht1]; norm_num
          · rcases kronTwo_eq_one_or_neg_one hodd with ht1 | ht1
            · right; rw [hc1, ht1]; norm_num
            · left; rw [hc1, ht1]; norm_num
        · have hodd : Odd (b + 1) := Nat.not_even_iff_odd.mp he
          have hg : a.gcd (b + 1) = 1 := by
            simpa [Nat.cast_add] using h
          rcases jacobiSym.eq_one_or_neg_one hg with h1 | h1
          · left; rw [ksym_odd a hodd, h1]
          · right; rw [ksym_odd a hodd, h1]

/-- Squares give value 1: (w | q²) = 1 whenever w is coprime to q. -/
lemma ksym_square_right {w : ℤ} {q : ℕ} (h : w.gcd q = 1) : ksym w (q ^ 2) = 1 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq : q = 0
    · subst q; simp [ksym]
    · by_cases he : Even q
      · rcases he with ⟨c, hc⟩
        have hcpos : c ≠ 0 := by
          intro hc0; omega
        have hqform : q = 2 * c := by omega
        have hclt : c < q := by
          rw [hqform]
          omega
        have hgcdc : w.gcd c = 1 := by
          apply Int.gcd_eq_one_of_gcd_mul_right_eq_one_left (m := c) (n := 2)
          simpa [hqform, mul_comm] using h
        have hgcd2 : w.gcd 2 = 1 := by
          apply Int.gcd_eq_one_of_gcd_mul_right_eq_one_right (m := c) (n := 2)
          simpa [hqform, mul_comm] using h
        have hodd : w % 2 = 1 := emod_two_eq_one_of_gcd_two w hgcd2
        have hc2_1 : ksym w (c ^ 2) = 1 := ih c hclt hgcdc
        have htwo : (kronTwo w) ^ 2 = 1 := by
          rcases kronTwo_eq_one_or_neg_one hodd with ht | ht <;> rw [ht] <;> norm_num
        calc
          ksym w (q ^ 2) = ksym w ((2 * c) ^ 2) := by rw [hqform]
          _ = ksym w (4 * c ^ 2) := by ring_nf
          _ = ksym w (2 * (2 * c ^ 2)) := by ring_nf
          _ = ksym w (2 * c ^ 2) * kronTwo w := by
                apply ksym_even_mul
                exact mul_ne_zero (by norm_num : (2 : ℕ) ≠ 0) (pow_ne_zero 2 hcpos)
          _ = ksym w (c ^ 2) * kronTwo w * kronTwo w := by
                rw [ksym_even_mul w (b := c ^ 2) (pow_ne_zero 2 hcpos)]
          _ = 1 := by
                rw [hc2_1, one_mul, ← pow_two, htwo]
      · have hodd : Odd q := Nat.not_even_iff_odd.mp he
        have hodd2 : Odd (q ^ 2) := Odd.pow hodd
        calc
          ksym w (q ^ 2) = jacobiSym w (q ^ 2) := ksym_odd w hodd2
          _ = jacobiSym w q ^ 2 := by rw [← jacobiSym.pow_right w q 2]
          _ = 1 := by
            rcases jacobiSym.eq_one_or_neg_one (by simpa using h) with h1 | h1 <;> rw [h1] <;> norm_num

/-- The χ₂ value attached to a circle of curvature `x` with a coprime
co-occurring circle of curvature `y`, i.e. the Kronecker symbol (y | |x|). -/
def pairChi (x y : ℤ) : ℤ := ksym y x.natAbs

/-- Coprime pairs give value ±1. -/
lemma pairChi_eq_one_or_neg_one {x y : ℤ} (h : y.gcd x = 1) : pairChi x y = 1 ∨ pairChi x y = -1 := by
  unfold pairChi
  apply ksym_eq_one_or_neg_one
  rw [Int.gcd_eq_natAbs] at h ⊢
  rw [Int.natAbs_natCast]
  exact h

/-- A square curvature paired with a coprime value gives χ₂ = 1. -/
lemma pairChi_square {n y : ℤ} (h : y.gcd n = 1) : pairChi (n ^ 2) y = 1 := by
  unfold pairChi
  have hnat : (n ^ 2).natAbs = n.natAbs ^ 2 := by
    rw [Int.natAbs_pow]
  rw [hnat]
  apply ksym_square_right
  rw [Int.gcd_eq_natAbs] at h ⊢
  rw [Int.natAbs_natCast]
  exact h

-- sanity tests
example : pairChi 5 8 = -1 := by native_decide   -- (8 | 5) = -1
example : pairChi 8 5 = -1 := by native_decide   -- (5 | 8) = -1 (even denominator Kronecker)
example : pairChi (-3) 5 = -1 := by native_decide
example : pairChi 5 (-3) = -1 := by native_decide
example (n : ℤ) (h : (5 : ℤ).gcd n = 1) : pairChi (n ^ 2) 5 = 1 := pairChi_square h

end Apollo
