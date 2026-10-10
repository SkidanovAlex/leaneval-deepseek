import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Commons.NumberTheory.JacobiSymbol

/-- `χ₈'` at a natural number, in terms of its residue mod 8. -/
lemma chi8'_nat_eq {n : ℕ} (hn : n % 2 = 1) :
    ZMod.χ₈' (n : ZMod 8) = (if n % 8 = 1 ∨ n % 8 = 3 then (1 : ℤ) else -1) := by
  rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_neg (by omega)]

/-- `χ₈` at a natural number, in terms of its residue mod 8. -/
lemma chi8_nat_eq {n : ℕ} (hn : n % 2 = 1) :
    ZMod.χ₈ (n : ZMod 8) = (if n % 8 = 1 ∨ n % 8 = 7 then (1 : ℤ) else -1) := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]

lemma mod_eq_neg_two_add (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) % ((N + 2 : ℕ) : ℤ) = (-2) % ((N + 2 : ℕ) : ℤ) := by
  have hcast : ((N + 2 : ℕ) : ℤ) = (N : ℤ) + 2 := by push_cast; ring
  rw [hcast]
  have h1 : (N : ℤ) % ((N : ℤ) + 2) = N :=
    Int.emod_eq_of_lt (by omega) (by omega)
  have he : (-2 : ℤ) = (N : ℤ) + ((N : ℤ) + 2) * (-1) := by ring
  conv_rhs => rw [he]
  rw [Int.add_mul_emod_self_left, h1]

lemma mod_eq_two_add (N : ℕ) (hN : 2 ≤ N) :
    (-(N : ℤ)) % ((N + 2 : ℕ) : ℤ) = 2 % ((N + 2 : ℕ) : ℤ) := by
  have hcast : ((N + 2 : ℕ) : ℤ) = (N : ℤ) + 2 := by push_cast; ring
  rw [hcast]
  have h2 : (2 : ℤ) % ((N : ℤ) + 2) = 2 := Int.emod_eq_of_lt (by norm_num) (by omega)
  have he : (-(N : ℤ)) = 2 + ((N : ℤ) + 2) * (-1) := by ring
  conv_lhs => rw [he]
  rw [Int.add_mul_emod_self_left, h2]

lemma mod_eq_two_sub (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) % ((N - 2 : ℕ) : ℤ) = 2 % ((N - 2 : ℕ) : ℤ) := by
  have hcast : ((N - 2 : ℕ) : ℤ) = (N : ℤ) - 2 := by
    rw [Nat.cast_sub hN]; norm_num
  have he : (N : ℤ) = 2 + ((N : ℤ) - 2) * 1 := by ring
  conv_lhs => rw [he]
  rw [hcast, Int.add_mul_emod_self_left]

lemma mod_eq_neg_two_sub (N : ℕ) (hN : 2 ≤ N) :
    (-(N : ℤ)) % ((N - 2 : ℕ) : ℤ) = (-2) % ((N - 2 : ℕ) : ℤ) := by
  have hcast : ((N - 2 : ℕ) : ℤ) = (N : ℤ) - 2 := by
    rw [Nat.cast_sub hN]; norm_num
  have he : (-(N : ℤ)) = (-2) + ((N : ℤ) - 2) * (-1) := by ring
  conv_lhs => rw [he]
  rw [hcast, Int.add_mul_emod_self_left]

theorem modEight_of_selfRelation {D : ℤ} (hodd : Odd D) (hN : 3 ≤ D.natAbs)
    (h : jacobiSym D (D.natAbs + 2) =
      (if 0 < D then (1 : ℤ) else -1) * jacobiSym D (D.natAbs - 2)) :
    (D % 8 = 1 ∨ D % 8 = 5) ∧ (jacobiSym D (D.natAbs + 2) = 1 ↔ D % 8 = 1) := by
  set N : ℕ := D.natAbs with hNdef
  have hN3 : 3 ≤ N := hN
  have hNodd : Odd N := by rw [hNdef]; exact hodd.natAbs
  have hN2 : N % 2 = 1 := Nat.odd_iff.mp hNodd
  have hoddNp2 : Odd (N + 2) := Nat.odd_iff.mpr (by omega)
  have hoddNm2 : Odd (N - 2) := Nat.odd_iff.mpr (by omega)
  have h2N : 2 ≤ N := by omega
  have hN8 : N % 8 = 1 ∨ N % 8 = 3 ∨ N % 8 = 5 ∨ N % 8 = 7 := by omega
  have hsign : D = (N : ℤ) ∨ D = -(N : ℤ) := by
    rcases lt_trichotomy D 0 with hneg | h0 | hpos
    · right
      have h1 : ((-D).natAbs : ℤ) = -D := Int.natAbs_of_nonneg (by omega)
      have h2 : (-D).natAbs = D.natAbs := Int.natAbs_neg D
      rw [h2] at h1
      have hNd : (D.natAbs : ℤ) = (N : ℤ) := by rw [← hNdef]
      omega
    · exfalso
      rw [h0] at hNdef
      simp at hNdef
      omega
    · left
      have h1 : (D.natAbs : ℤ) = D := Int.natAbs_of_nonneg (le_of_lt hpos)
      have hNd : (D.natAbs : ℤ) = (N : ℤ) := by rw [← hNdef]
      omega
  rcases hsign with hDpos | hDneg
  · have hDgt : 0 < D := by rw [hDpos]; exact_mod_cast (by omega : 0 < N)
    have hif : (if 0 < D then (1 : ℤ) else -1) = 1 := if_pos hDgt
    have hplus : jacobiSym D (N + 2) = ZMod.χ₈' ((N + 2 : ℕ) : ZMod 8) := by
      rw [hDpos]
      exact (jacobiSym.mod_left' (b := N + 2) (mod_eq_neg_two_add N h2N)).trans
        (jacobiSym.at_neg_two hoddNp2)
    have hminus : jacobiSym D (N - 2) = ZMod.χ₈ ((N - 2 : ℕ) : ZMod 8) := by
      rw [hDpos]
      exact (jacobiSym.mod_left' (b := N - 2) (mod_eq_two_sub N h2N)).trans
        (jacobiSym.at_two hoddNm2)
    rw [hif, one_mul, hplus, hminus] at h
    rcases hN8 with h1 | h3 | h5 | h7
    · have hD8 : D % 8 = 1 := by rw [hDpos]; omega
      refine ⟨Or.inl hD8, ?_⟩
      rw [hplus, hD8]
      have hc : ZMod.χ₈' ((N + 2 : ℕ) : ZMod 8) = 1 := by
        rw [chi8'_nat_eq (by omega : (N + 2) % 2 = 1)]
        rw [show (N + 2) % 8 = 3 by omega]; norm_num
      rw [hc]
    · have hc1 : ZMod.χ₈' ((N + 2 : ℕ) : ZMod 8) = -1 := by
        rw [chi8'_nat_eq (by omega : (N + 2) % 2 = 1)]
        rw [show (N + 2) % 8 = 5 by omega]; norm_num
      have hc2 : ZMod.χ₈ ((N - 2 : ℕ) : ZMod 8) = 1 := by
        rw [chi8_nat_eq (by omega : (N - 2) % 2 = 1)]
        rw [show (N - 2) % 8 = 1 by omega]; norm_num
      rw [hc1, hc2] at h
      exact absurd h (by norm_num)
    · have hD8 : D % 8 = 5 := by rw [hDpos]; omega
      refine ⟨Or.inr hD8, ?_⟩
      rw [hplus, hD8]
      have hc : ZMod.χ₈' ((N + 2 : ℕ) : ZMod 8) = -1 := by
        rw [chi8'_nat_eq (by omega : (N + 2) % 2 = 1)]
        rw [show (N + 2) % 8 = 7 by omega]; norm_num
      rw [hc]; norm_num
    · have hc1 : ZMod.χ₈' ((N + 2 : ℕ) : ZMod 8) = 1 := by
        rw [chi8'_nat_eq (by omega : (N + 2) % 2 = 1)]
        rw [show (N + 2) % 8 = 1 by omega]; norm_num
      have hc2 : ZMod.χ₈ ((N - 2 : ℕ) : ZMod 8) = -1 := by
        rw [chi8_nat_eq (by omega : (N - 2) % 2 = 1)]
        rw [show (N - 2) % 8 = 5 by omega]; norm_num
      rw [hc1, hc2] at h
      exact absurd h (by norm_num)
  · have hDlt : D < 0 := by rw [hDneg]; omega
    have hif : (if 0 < D then (1 : ℤ) else -1) = -1 := if_neg (by omega)
    have hplus : jacobiSym D (N + 2) = ZMod.χ₈ ((N + 2 : ℕ) : ZMod 8) := by
      rw [hDneg]
      exact (jacobiSym.mod_left' (b := N + 2) (mod_eq_two_add N h2N)).trans
        (jacobiSym.at_two hoddNp2)
    have hminus : jacobiSym D (N - 2) = ZMod.χ₈' ((N - 2 : ℕ) : ZMod 8) := by
      rw [hDneg]
      exact (jacobiSym.mod_left' (b := N - 2) (mod_eq_neg_two_sub N h2N)).trans
        (jacobiSym.at_neg_two hoddNm2)
    rw [hif, hplus, hminus, neg_one_mul] at h
    rcases hN8 with h1 | h3 | h5 | h7
    · have hc1 : ZMod.χ₈ ((N + 2 : ℕ) : ZMod 8) = -1 := by
        rw [chi8_nat_eq (by omega : (N + 2) % 2 = 1)]
        rw [show (N + 2) % 8 = 3 by omega]; norm_num
      have hc2 : ZMod.χ₈' ((N - 2 : ℕ) : ZMod 8) = -1 := by
        rw [chi8'_nat_eq (by omega : (N - 2) % 2 = 1)]
        rw [show (N - 2) % 8 = 7 by omega]; norm_num
      rw [hc1, hc2] at h
      exact absurd h (by norm_num)
    · have hD8 : D % 8 = 5 := by rw [hDneg]; omega
      refine ⟨Or.inr hD8, ?_⟩
      rw [hplus, hD8]
      have hc : ZMod.χ₈ ((N + 2 : ℕ) : ZMod 8) = -1 := by
        rw [chi8_nat_eq (by omega : (N + 2) % 2 = 1)]
        rw [show (N + 2) % 8 = 5 by omega]; norm_num
      rw [hc]; norm_num
    · have hc1 : ZMod.χ₈ ((N + 2 : ℕ) : ZMod 8) = 1 := by
        rw [chi8_nat_eq (by omega : (N + 2) % 2 = 1)]
        rw [show (N + 2) % 8 = 7 by omega]; norm_num
      have hc2 : ZMod.χ₈' ((N - 2 : ℕ) : ZMod 8) = 1 := by
        rw [chi8'_nat_eq (by omega : (N - 2) % 2 = 1)]
        rw [show (N - 2) % 8 = 3 by omega]; norm_num
      rw [hc1, hc2] at h
      exact absurd h (by norm_num)
    · have hD8 : D % 8 = 1 := by rw [hDneg]; omega
      refine ⟨Or.inl hD8, ?_⟩
      rw [hplus, hD8]
      have hc : ZMod.χ₈ ((N + 2 : ℕ) : ZMod 8) = 1 := by
        rw [chi8_nat_eq (by omega : (N + 2) % 2 = 1)]
        rw [show (N + 2) % 8 = 1 by omega]; norm_num
      rw [hc]

end Commons.NumberTheory.JacobiSymbol