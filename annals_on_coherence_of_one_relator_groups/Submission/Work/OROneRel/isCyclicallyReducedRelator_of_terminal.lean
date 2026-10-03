import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# Terminal relators are cyclically reduced

A *terminal* relator is either `1` or a nonzero power `of x ^ m` of a single generator
(`Basic.lean`, `Work.OROneRel.IsTerminalRelator`).  In both cases the reduced word of the relator
is cyclically reduced:

* `1` has reduced word the empty word, which is cyclically reduced by convention;
* `of x ^ m` has reduced word `List.replicate m.natAbs (x, sign)` (with `sign = true` for `m > 0`
  and `sign = false` for `m < 0`), a block of copies of one letter.  It is reduced (no two
  consecutive letters are inverse to each other, since `x` is a generator and adjacent letters are
  equal) and its first and last letter are equal, so they do not cancel.

This is the base case of the Magnus--Moldavanskii hierarchy: the relator of a terminal
one-relator group is cyclically reduced, as required by the Freiheitssatz/Weinbaum interface
(`Interface.lean`).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- A positive power of a generator has cyclically reduced word `List.replicate n (x, true)`. -/
theorem isCyclicallyReducedRelator_of_pow_ofNat {x : α} (n : ℕ) :
    IsCyclicallyReducedRelator (FreeGroup.of x ^ n) := by
  classical
  rw [IsCyclicallyReducedRelator, FreeGroup.toWord_of_pow]
  have h1 : FreeGroup.IsCyclicallyReduced ([(x, true)] : List (α × Bool)) :=
    FreeGroup.IsCyclicallyReduced.singleton
  simpa [List.flatten_replicate_singleton] using h1.flatten_replicate n

/-- The inverse of a positive power of a generator also has cyclically reduced word. -/
theorem isCyclicallyReducedRelator_of_inv_pow_ofNat {x : α} (n : ℕ) :
    IsCyclicallyReducedRelator ((FreeGroup.of x ^ n)⁻¹) := by
  classical
  rw [IsCyclicallyReducedRelator, FreeGroup.toWord_inv, FreeGroup.toWord_of_pow]
  have h1 : FreeGroup.IsCyclicallyReduced ([(x, false)] : List (α × Bool)) :=
    FreeGroup.IsCyclicallyReduced.singleton
  have h2 : FreeGroup.IsCyclicallyReduced (List.replicate n (x, false)) := by
    simpa [List.flatten_replicate_singleton] using h1.flatten_replicate n
  convert h2 using 1
  simp [FreeGroup.invRev, List.map_replicate, List.reverse_replicate]

/-- **Terminal relators are cyclically reduced.**  `1` and the nonzero powers `of x ^ m` of a
single generator all have cyclically reduced reduced word. -/
theorem isCyclicallyReducedRelator_of_terminal {α : Type u} {r : FreeGroup α}
    (h : Work.OROneRel.IsTerminalRelator r) : Work.OROneRel.IsCyclicallyReducedRelator r := by
  classical
  rcases h with rfl | ⟨x, m, hm, rfl⟩
  · rw [IsCyclicallyReducedRelator, FreeGroup.toWord_one]
    exact FreeGroup.IsCyclicallyReduced.nil
  · rcases lt_or_gt_of_ne hm with hneg | hpos
    · -- `m < 0`: `of x ^ m = (of x ^ m.natAbs)⁻¹`.
      have hm' : m = -(m.natAbs : ℤ) := by
        have : (m.natAbs : ℤ) = -m := by
          rw [← Int.natAbs_neg m]
          exact Int.natAbs_of_nonneg (by omega)
        omega
      rw [hm', zpow_neg, zpow_natCast]
      exact isCyclicallyReducedRelator_of_inv_pow_ofNat m.natAbs
    · -- `m > 0`: `of x ^ m = of x ^ m.natAbs`.
      have hm' : m = (m.natAbs : ℤ) := by
        have := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ m by omega)
        omega
      rw [hm', zpow_natCast]
      exact isCyclicallyReducedRelator_of_pow_ofNat m.natAbs

end Work.OROneRel
