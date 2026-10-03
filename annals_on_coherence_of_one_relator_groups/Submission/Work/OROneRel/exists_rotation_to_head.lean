import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.sigma_mk
import Submission.Work.OROneRel.exists_rotated_relator_full

set_option linter.style.haveILetI false

/-!
# Rotating a cyclically reduced relator so that a prescribed letter is *literally* first

Given a cyclically reduced relator `r` and a generator `x` occurring in `r`, we produce a natural
number `k` and a conjugate `s` of `r` such that

* `s = FreeGroup.mk ((FreeGroup.toWord r).rotate k)` is *literally* a cyclic rotation of the reduced
  word of `r` (not merely some conjugate with the same invariants),
* `s` is cyclically reduced, has the same length (`relatorNorm`), the same letters
  (`relatorLetters`) and the same exponent sums `sigma t`, and
* the reduced word of `s` begins with `x` (with either sign).

The construction: write `r.toWord = A ++ (x, b) :: V'`.  With `V = (x, b) :: V'` the rotation
`(r.toWord).rotate A.length` equals `V ++ A`, whose head is `(x, b)`, and
`mk A * mk (V ++ A) * (mk A)⁻¹ = mk (A ++ V) = mk (r.toWord) = r`.  Taking `s = mk (V ++ A)` and
`k = A.length` gives all the claims; the only non-trivial input is that cyclic rotations of a
cyclically reduced word are cyclically reduced.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

open List

theorem exists_rotation_to_head {α : Type u} [DecidableEq α] (r : FreeGroup α) (x : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hx : x ∈ Work.OROneRel.relatorLetters r) :
    ∃ (k : ℕ) (s c : FreeGroup α), s = FreeGroup.mk ((FreeGroup.toWord r).rotate k) ∧
      Work.OROneRel.IsCyclicallyReducedRelator s ∧ r = c * s * c⁻¹ ∧
      Work.OROneRel.relatorNorm s = Work.OROneRel.relatorNorm r ∧
      Work.OROneRel.relatorLetters s = Work.OROneRel.relatorLetters r ∧
      (∀ u : α, Work.OROneRel.sigma u s = Work.OROneRel.sigma u r) ∧
      (s.toWord.head? = some (x, true) ∨ s.toWord.head? = some (x, false)) := by
  classical
  -- `Work.OROneRel`'s definitions use `Classical.decEq` internally; align the ambient instance.
  rw [Subsingleton.elim (inferInstanceAs (DecidableEq α)) (Classical.decEq α)]
  letI : DecidableEq α := Classical.decEq α
  -- `x` occurs in the reduced word of `r`, with some sign `b`.
  have hx' : ∃ b : Bool, (x, b) ∈ r.toWord := by
    simpa only [relatorLetters, Set.mem_ofPred_eq] using hx
  obtain ⟨b, hb⟩ := hx'
  -- split the reduced word just before that occurrence: `r.toWord = A ++ (x,b) :: V'`.
  obtain ⟨A, V', hWV⟩ := List.mem_iff_append.mp hb
  set V : List (α × Bool) := (x, b) :: V' with hV
  have hW : r.toWord = A ++ V := by rw [hWV, hV]
  -- the rotation `V ++ A` is cyclically reduced.
  have hWcyc : FreeGroup.IsCyclicallyReduced r.toWord := hcyc
  have hVA : V ++ A = (r.toWord).rotate A.length := by
    rw [hW, List.rotate_append_length_eq]
  have hcycVA : FreeGroup.IsCyclicallyReduced (V ++ A) := by
    rw [hVA]; exact isCyclicallyReduced_rotate hWcyc
  have hredVA : FreeGroup.IsReduced (V ++ A) := hcycVA.isReduced
  have htoWord : (FreeGroup.mk (V ++ A)).toWord = V ++ A := by
    rw [FreeGroup.toWord_mk, (FreeGroup.isReduced_iff_reduce_eq (L := V ++ A)).mp hredVA]
  refine ⟨A.length, FreeGroup.mk (V ++ A), FreeGroup.mk A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `s` is literally the rotation by `A.length`
    rw [hVA]
  · -- cyclically reduced
    rw [IsCyclicallyReducedRelator, htoWord]
    exact hcycVA
  · -- conjugate
    have hr : r = FreeGroup.mk A * FreeGroup.mk V := by
      rw [(FreeGroup.mk_toWord (x := r)).symm, hW, FreeGroup.mul_mk]
    rw [hr, ← FreeGroup.mul_mk (L₁ := V) (L₂ := A)]
    group
  · -- same norm
    rw [relatorNorm, relatorNorm, FreeGroup.norm, FreeGroup.norm, htoWord, hW]
    simp [List.length_append, Nat.add_comm]
  · -- same letters
    rw [relatorLetters, relatorLetters, htoWord, hW]
    ext a
    constructor
    · rintro ⟨b', hb'⟩
      refine ⟨b', ?_⟩
      rw [hVA] at hb'
      rw [List.mem_rotate] at hb'
      rwa [← hW]
    · rintro ⟨b', hb'⟩
      refine ⟨b', ?_⟩
      rw [hVA, List.mem_rotate]
      rwa [← hW] at hb'
  · -- same exponent sums
    intro t
    have hr : r = FreeGroup.mk (r.toWord) := (FreeGroup.mk_toWord (x := r)).symm
    rw [hr, sigma_mk t (r.toWord), sigma_mk t (V ++ A), hW, sigmaList_append_comm]
  · -- the first letter is `x`
    rw [htoWord]
    rcases b with _ | _
    · right
      rw [hV]; rfl
    · left
      rw [hV]; rfl

end Work.OROneRel
