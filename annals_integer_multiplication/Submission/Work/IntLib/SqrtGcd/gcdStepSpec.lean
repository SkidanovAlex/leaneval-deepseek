import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdDefs
import Submission.Work.IntLib.SqrtGcd.oddPartLemmas

/-!
# One binary-gcd step

`Work.IntLib.SG.gcdStep u v` replaces, for two *odd, distinct* numbers `u` and `v`, the larger of
the two by the odd part of the difference.  `gcdStepSpec` records the three facts the binary gcd
loop of the integer library is analysed with:

* the gcd of the pair is unchanged;
* both components remain odd;
* the sum of the binary lengths (`Nat.size`) strictly decreases (so the loop terminates and its
  iteration count is controlled by the input size).

The two mathematical ingredients are `oddPartGcd` (removing the 2-part of a number does not
change its gcd with an odd number) and `oddPartSizeLt` (the odd part of a positive even number is
strictly shorter in binary).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

/-- Removing the factors of `2` from `u` does not change `gcd u v` when `v` is odd. -/
theorem oddPartGcd (u v : ℕ) (hv : v % 2 = 1) : Nat.gcd (oddPart u) v = Nat.gcd u v := by
  induction u using Nat.strong_induction_on with
  | _ n ih =>
    rw [oddPart.eq_def]
    by_cases h : n % 2 = 0 ∧ 0 < n
    · rw [if_pos h]
      have hlt : n / 2 < n := Nat.div_lt_self h.2 (by norm_num)
      rw [ih (n / 2) hlt]
      conv_rhs => rw [← Nat.two_mul_div_two_of_even (Nat.even_iff.mpr h.1)]
      exact (Nat.Coprime.gcd_mul_left_cancel (n / 2)
        (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hv))).symm
    · rw [if_neg h]

/-- A positive number of at most half the size of `m` has strictly smaller binary length. -/
theorem size_lt_of_le_half {a m : ℕ} (h : a ≤ m / 2) (ha : 0 < a) : a.size < m.size := by
  rw [Nat.lt_size]
  have h1 : 0 < a.size := by rwa [Nat.size_pos]
  have h2 : 2 ^ (a.size - 1) ≤ a := by
    rw [← Nat.lt_size]; omega
  have h3 : 2 ^ a.size = 2 * 2 ^ (a.size - 1) := by
    conv_lhs => rw [show a.size = (a.size - 1) + 1 from by omega]
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [h3]
  have h4 : 2 * a ≤ m := by
    have := Nat.le_div_iff_mul_le (k := 2) (by norm_num) |>.mp h
    omega
  exact le_trans (Nat.mul_le_mul_left 2 h2) h4

/-- The odd part of a positive even number has strictly smaller binary length. -/
theorem oddPartSizeLt (n : ℕ) (hpos : 0 < n) (heven : n % 2 = 0) :
    (oddPart n).size < n.size :=
  size_lt_of_le_half (oddPart_le_half n heven hpos)
    (by have := oddPart_odd n (by omega); omega)

end SG
end Work.IntLib

namespace Work.IntLib.SqrtGcd

theorem gcdStepSpec : ∀ u v : ℕ, u % 2 = 1 → v % 2 = 1 → u ≠ v →
    (Nat.gcd (Work.IntLib.SG.gcdStep u v).1 (Work.IntLib.SG.gcdStep u v).2 = Nat.gcd u v ∧
      (Work.IntLib.SG.gcdStep u v).1 % 2 = 1 ∧ (Work.IntLib.SG.gcdStep u v).2 % 2 = 1 ∧
      (Work.IntLib.SG.gcdStep u v).1.size + (Work.IntLib.SG.gcdStep u v).2.size
        < u.size + v.size) := by
  intro u v hu hv huv
  have hnu : ¬ Even u := by rw [Nat.even_iff]; omega
  have hnv : ¬ Even v := by rw [Nat.even_iff]; omega
  rcases le_total v u with hvu | huvle
  · -- the larger entry is `u`; it is replaced by `oddPart (u - v)`
    have heven : (u - v) % 2 = 0 :=
      Nat.even_iff.mp ((Nat.even_sub hvu).mpr ⟨fun h => (hnu h).elim, fun h => (hnv h).elim⟩)
    have hpos : 0 < u - v := by omega
    have hstep1 : (Work.IntLib.SG.gcdStep u v).1 = Work.IntLib.SG.oddPart (u - v) := by
      rw [Work.IntLib.SG.gcdStep, if_pos hvu]
    have hstep2 : (Work.IntLib.SG.gcdStep u v).2 = v := by
      rw [Work.IntLib.SG.gcdStep, if_pos hvu]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc Nat.gcd (Work.IntLib.SG.gcdStep u v).1 (Work.IntLib.SG.gcdStep u v).2
          = Nat.gcd (Work.IntLib.SG.oddPart (u - v)) v := by rw [hstep1, hstep2]
        _ = Nat.gcd (u - v) v := Work.IntLib.SG.oddPartGcd (u - v) v hv
        _ = Nat.gcd u v := Nat.gcd_sub_self_left hvu
    · rw [hstep1]; exact Work.IntLib.SG.oddPart_odd (u - v) (by omega)
    · rw [hstep2]; exact hv
    · rw [hstep1, hstep2]
      have h1 : (Work.IntLib.SG.oddPart (u - v)).size < u.size := by
        have h0 := Work.IntLib.SG.oddPartSizeLt (u - v) hpos heven
        have h2 : (u - v).size ≤ u.size := Nat.size_le_size (Nat.sub_le u v)
        omega
      omega
  · -- the larger entry is `v`; it is replaced by `oddPart (v - u)`
    have hlt : ¬ v ≤ u := by omega
    have heven : (v - u) % 2 = 0 :=
      Nat.even_iff.mp ((Nat.even_sub huvle).mpr ⟨fun h => (hnv h).elim, fun h => (hnu h).elim⟩)
    have hpos : 0 < v - u := by omega
    have hstep1 : (Work.IntLib.SG.gcdStep u v).1 = u := by
      rw [Work.IntLib.SG.gcdStep, if_neg hlt]
    have hstep2 : (Work.IntLib.SG.gcdStep u v).2 = Work.IntLib.SG.oddPart (v - u) := by
      rw [Work.IntLib.SG.gcdStep, if_neg hlt]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc Nat.gcd (Work.IntLib.SG.gcdStep u v).1 (Work.IntLib.SG.gcdStep u v).2
          = Nat.gcd u (Work.IntLib.SG.oddPart (v - u)) := by rw [hstep1, hstep2]
        _ = Nat.gcd (Work.IntLib.SG.oddPart (v - u)) u := Nat.gcd_comm _ _
        _ = Nat.gcd (v - u) u := Work.IntLib.SG.oddPartGcd (v - u) u hu
        _ = Nat.gcd u (v - u) := Nat.gcd_comm _ _
        _ = Nat.gcd u v := Nat.gcd_sub_self_right huvle
    · rw [hstep1]; exact hu
    · rw [hstep2]; exact Work.IntLib.SG.oddPart_odd (v - u) (by omega)
    · rw [hstep1, hstep2]
      have h1 : (Work.IntLib.SG.oddPart (v - u)).size < v.size := by
        have h0 := Work.IntLib.SG.oddPartSizeLt (v - u) hpos heven
        have h2 : (v - u).size ≤ v.size := Nat.size_le_size (Nat.sub_le v u)
        omega
      omega

end Work.IntLib.SqrtGcd
