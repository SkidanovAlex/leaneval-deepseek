import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- The set of generators occurring in a nontrivial power of a single generator `a` is `{a}`.

`relatorLetters` is `{x | ∃ b, (x, b) ∈ r.toWord}`, where `toWord` is the reduced word.  For a
generator `a`, `(of a).toWord = [(a, true)]`, so a positive power reduces to a list of copies of
`(a, true)` and a negative power to a list of copies of `(a, false)`; since `m ≠ 0` the list is
nonempty and every letter has first coordinate `a`. -/
theorem relatorLetters_of_zpow {α : Type u} (a : α) (m : ℤ) (hm : m ≠ 0) :
    Work.OROneRel.relatorLetters (FreeGroup.of a ^ m) = {a} := by
  classical
  -- The reduced word of a negative power of a generator.
  have hneg : ∀ n : ℕ, (FreeGroup.of a ^ (-(n : ℤ))).toWord = List.replicate n (a, false) := by
    intro n
    rw [zpow_neg, zpow_natCast, FreeGroup.toWord_inv, FreeGroup.toWord_of_pow]
    simp [FreeGroup.invRev, List.map_replicate]
  unfold relatorLetters
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rcases lt_trichotomy m 0 with h | h | h
  · -- `m < 0`: `m = - n` with `n = (-m).toNat > 0`.
    have hm' : m = -(((-m).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have hnz : ((-m).toNat) ≠ 0 := by
      intro hc
      have : -m ≤ 0 := Int.toNat_eq_zero.mp hc
      omega
    rw [hm', hneg ((-m).toNat)]
    constructor
    · rintro ⟨b, hb⟩
      rw [List.mem_replicate] at hb
      exact congrArg Prod.fst hb.2
    · intro hx
      subst hx
      exact ⟨false, by rw [List.mem_replicate]; exact ⟨hnz, rfl⟩⟩
  · exact absurd h hm
  · -- `m > 0`: `m = n` with `n = m.toNat > 0`.
    have hm' : m = ((m.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    have hnz : m.toNat ≠ 0 := by
      intro hc
      have : m ≤ 0 := Int.toNat_eq_zero.mp hc
      omega
    rw [hm', zpow_natCast, FreeGroup.toWord_of_pow]
    constructor
    · rintro ⟨b, hb⟩
      rw [List.mem_replicate] at hb
      exact congrArg Prod.fst hb.2
    · intro hx
      subst hx
      exact ⟨true, by rw [List.mem_replicate]; exact ⟨hnz, rfl⟩⟩

end Work.OROneRel
