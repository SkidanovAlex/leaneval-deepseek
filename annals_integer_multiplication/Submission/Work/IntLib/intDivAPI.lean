import Mathlib

/-!
# The integer division API used by the `IntLib` area

This file records the concrete formulas for Lean's four integer division/modulus
operations `Int.tdiv`, `Int.tmod` (truncated division, i.e. rounding towards zero)
and `Int.fdiv`, `Int.fmod` (floor division) in terms of the *natural* division and
modulus of the absolute values, together with the signs of the operands.

These are exactly the facts a StackLang routine that implements integer division
on encodings of `Int` values needs: it decomposes `a = s_a * |a|`, `b = s_b * |b|`
and performs the division on the machine (natural) numbers.
-/

namespace Work.IntLib

/-- The natural-number identity behind `Int.fdiv` for a negative numerator:
`⌊(-(m+1)) / (j+1)⌋ = -⌈(m+1)/(j+1)⌉`. -/
private lemma fdiv_neg_nat (m j : ℕ) :
    (↑(m / (j + 1)) : ℤ) + 1 =
      (↑((m + 1) / (j + 1)) : ℤ) +
        (if (m + 1) % (j + 1) = 0 then (0 : ℤ) else 1) := by
  split <;> rename_i h
  · rw [Nat.succ_div_of_mod_eq_zero h]; push_cast; ring
  · rw [Nat.succ_div_of_mod_ne_zero h]

/-- The natural-number identity behind `Int.fmod` for a negative numerator. -/
private lemma fmod_neg_nat (m j : ℕ) :
    (j + 1) - (m % (j + 1) + 1) =
      if (m + 1) % (j + 1) = 0 then 0 else (j + 1) - ((m + 1) % (j + 1)) := by
  have hmod : (m % (j + 1) + 1) % (j + 1) = (m + 1) % (j + 1) := Nat.mod_add_mod m (j + 1) 1
  have hlt : m % (j + 1) < j + 1 := Nat.mod_lt _ (Nat.succ_pos j)
  by_cases h : m % (j + 1) + 1 = j + 1
  · have hz : (m + 1) % (j + 1) = 0 := by rw [← hmod, h, Nat.mod_self]
    rw [ite_eq_left hz, h, Nat.sub_self]
  · have hlt' : m % (j + 1) + 1 < j + 1 := by omega
    have hz : (m + 1) % (j + 1) = m % (j + 1) + 1 := by rw [← hmod, Nat.mod_eq_of_lt hlt']
    rw [ite_eq_right (by omega), hz]

/-- `Int`-valued form of `fmod_neg_nat`, in the shape produced by unfolding `Int.fmod`. -/
private lemma fmod_neg_int (m j : ℕ) :
    (((j + 1 : ℕ)) : ℤ) - (((m % (j + 1) + 1 : ℕ)) : ℤ) =
      if (m + 1) % (j + 1) = 0 then (0 : ℤ)
      else (((j + 1 : ℕ)) : ℤ) - (((m + 1) % (j + 1) : ℕ) : ℤ) := by
  have hmod_lt : m % (j + 1) < j + 1 := Nat.mod_lt m (by omega : 0 < j + 1)
  have hle : m % (j + 1) + 1 ≤ j + 1 := by omega
  have hle2 : (m + 1) % (j + 1) ≤ j + 1 :=
    Nat.le_of_lt (Nat.mod_lt _ (by omega : 0 < j + 1))
  rw [← Nat.cast_sub hle, ← Nat.cast_sub hle2, fmod_neg_nat m j]
  split
  · norm_num
  · rfl

theorem intDivAPI :
    (∀ a b : ℤ, b ≠ 0 → Int.tdiv a b =
      (if a < 0 then (-1 : ℤ) else 1) * (if b < 0 then (-1 : ℤ) else 1) *
        ((a.natAbs / b.natAbs : ℕ) : ℤ)) ∧
    (∀ a b : ℤ, b ≠ 0 → Int.tmod a b =
      (if a < 0 then (-1 : ℤ) else 1) * ((a.natAbs % b.natAbs : ℕ) : ℤ)) ∧
    (∀ a b : ℤ, 0 < b → Int.fdiv a b =
      (if 0 ≤ a then ((a.natAbs / b.natAbs : ℕ) : ℤ)
        else -(((a.natAbs / b.natAbs : ℕ) : ℤ) +
          (if a.natAbs % b.natAbs = 0 then 0 else 1)))) ∧
    (∀ a b : ℤ, 0 < b → Int.fmod a b =
      (if 0 ≤ a then ((a.natAbs % b.natAbs : ℕ) : ℤ)
        else (if a.natAbs % b.natAbs = 0 then 0
          else (b.natAbs : ℤ) - ((a.natAbs % b.natAbs : ℕ) : ℤ)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- truncated division
    intro a b hb
    rcases lt_or_ge a 0 with ha | ha
    · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero ha
      rcases lt_or_ge b 0 with hb' | hb'
      · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hb'
        simp [Int.tdiv, Int.natAbs_negSucc]
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb'
        simp [Int.tdiv, Int.natAbs_negSucc, Int.natAbs_natCast]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      rcases lt_or_ge b 0 with hb' | hb'
      · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hb'
        simp [Int.tdiv, Int.natAbs_negSucc, Int.natAbs_natCast]
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb'
        rw [Int.natAbs_natCast, Int.natAbs_natCast, ← Int.ofNat_tdiv m n]
        rw [ite_eq_right (show ¬ ((↑m : ℤ) < 0) by simp),
          ite_eq_right (show ¬ ((↑n : ℤ) < 0) by simp)]
        ring
  · -- truncated modulus
    intro a b hb
    rcases lt_or_ge a 0 with ha | ha
    · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero ha
      rcases lt_or_ge b 0 with hb' | hb'
      · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hb'
        simp [Int.tmod, Int.natAbs_negSucc]
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb'
        simp [Int.tmod, Int.natAbs_negSucc, Int.natAbs_natCast]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      rcases lt_or_ge b 0 with hb' | hb'
      · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hb'
        simp [Int.tmod, Int.natAbs_negSucc, Int.natAbs_natCast]
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb'
        rw [← Int.ofNat_tmod m n, Int.natAbs_natCast]
        simp
  · -- floor division
    intro a b hb
    rcases lt_or_ge a 0 with ha | ha
    · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero ha
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hb)
      subst hk
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      subst hj
      rw [Int.natAbs_negSucc, Int.natAbs_natCast]
      simp only [Int.negSucc_not_nonneg, ite_false]
      change Int.negSucc (m / (Nat.succ j)) =
        -(((Nat.succ m / Nat.succ j : ℕ) : ℤ) +
          (if Nat.succ m % Nat.succ j = 0 then (0 : ℤ) else 1))
      rw [Int.negSucc_eq]
      simp only [Nat.succ_eq_add_one]
      exact congrArg Neg.neg (fdiv_neg_nat m j)
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hb)
      subst hk
      rw [Int.natAbs_natCast, ← Int.ofNat_fdiv m k]
      simp
  · -- floor modulus
    intro a b hb
    rcases lt_or_ge a 0 with ha | ha
    · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero ha
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hb)
      subst hk
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      subst hj
      rw [Int.natAbs_negSucc, Int.natAbs_natCast]
      simp only [Int.negSucc_not_nonneg, ite_false]
      change Int.subNatNat (Nat.succ j) (Nat.succ (m % Nat.succ j)) = _
      rw [Int.subNatNat_eq_coe]
      simp only [Nat.succ_eq_add_one]
      exact fmod_neg_int m j
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hb)
      subst hk
      rw [Int.natAbs_natCast, ← Int.ofNat_fmod m k]
      simp

end Work.IntLib
