import Mathlib
import Submission.Work.MainP.crtLabDefs

namespace Work.MainP

/-- The update of an odometer entry: for an entry `(c, P, Q)` with `c = (i % s)·P`, `Q = s·P`, the
update `c ↦ c + P` (wrapping to `0` at `Q`) advances the residue from `i % s` to `(i+1) % s`. -/
theorem entryUpd_entry (s P i : ℕ) (hs : 1 ≤ s) (hP : 1 ≤ P) :
    Work.MainP.entryUpd (Work.MainP.triple (((i % s) * P : ℕ) : ℤ) (P : ℤ) ((s * P : ℕ) : ℤ))
      = Work.MainP.triple ((((i + 1) % s) * P : ℕ) : ℤ) (P : ℤ) ((s * P : ℕ) : ℤ) := by
  rw [Work.MainP.entryUpd_triple]
  have hs0 : 0 < s := hs
  have hP0 : 0 < P := hP
  set a := i % s with ha
  have har : a < s := by rw [ha]; exact Nat.mod_lt i hs0
  have hi : s * (i / s) + a = i := by
    rw [ha]; exact Nat.div_add_mod i s
  have hmod : (i + 1) % s = (a + 1) % s := by
    have h1 : i + 1 = (a + 1) + s * (i / s) := by omega
    rw [h1, Nat.add_mul_mod_self_left]
  rw [hmod]
  simp only [Work.MainP.triple, HvdH.Val.cons.injEq, HvdH.Val.int.injEq]
  refine ⟨?_, trivial⟩
  rcases lt_or_ge (a + 1) s with hlt | hge
  · -- no wrap: `a + 1 < s`
    have hmod_a : (a + 1) % s = a + 1 := Nat.mod_eq_of_lt hlt
    have hlt' : a * P + P < s * P := by
      rw [← Nat.succ_mul]
      exact Nat.mul_lt_mul_of_pos_right hlt hP0
    have hne : ¬ ((↑(a * P) : ℤ) + ↑P = (↑(s * P) : ℤ)) := by
      intro h
      rw [← Nat.cast_add, Nat.cast_inj] at h
      exact absurd h (Nat.ne_of_lt hlt')
    rw [ite_eq_right hne, hmod_a]
    push_cast
    ring
  · -- wrap: `a + 1 = s`
    have heq : a + 1 = s := le_antisymm (Nat.succ_le_of_lt har) hge
    have hmod_a : (a + 1) % s = 0 := by rw [heq, Nat.mod_self]
    have hcond : (↑(a * P) : ℤ) + ↑P = (↑(s * P) : ℤ) := by
      rw [← heq, ← Nat.cast_add]
      push_cast
      ring
    rw [ite_eq_left hcond, hmod_a]
    simp

end Work.MainP
