/-
# `muColimZero` is a right identity for `muJoinAdd`

`NK.HassePrinciple.muColimZero p V` is the class of `0` at the bottom level `⊥`
(`MuColimAdd.lean`), and `muJoinAdd` adds two colimit classes by inflating them to the join of
their levels.  Since `⊥` is below every level, the sum of a class of level `L` with the zero class
can be evaluated at the single level `L` (`muJoinAdd_ofLevel_le` with `M = L`), where it reduces to
the level-wise sum `a + 0 = a`.

Note on universes: the enclosing package is built with `autoImplicit = false`, so the universe
variable appearing in the statement (`Type u`) has to be declared explicitly.
-/
import Mathlib
import Submission.NK.HassePrinciple.MuColimAdd

universe u

namespace NK.HassePrinciple

theorem muJoinAdd_zero_right {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) (x : NK.HassePrinciple.MuColim p V) :
    NK.HassePrinciple.muJoinAdd p V x (NK.HassePrinciple.muColimZero p V) = x := by
  obtain ⟨L, a, rfl⟩ := (muLevelSystem p V).ofLevel_surjective x
  -- `muColimZero` is the class of `0` at the bottom level.
  rw [← muColimZero_ofLevel (p := p) (V := V) (⊥ : FiniteGaloisIntermediateField K K')]
  -- evaluate the sum at the single level `L`, which dominates both summands.
  rw [muJoinAdd_ofLevel_le (p := p) (V := V) (L := L) (L' := ⊥) (M := L) le_rfl bot_le a
    (0 : (muLevelSystem p V).obj ⊥)]
  rw [muLevelSystem_map_refl_apply, muLevelSystem_map_zero, add_zero]

end NK.HassePrinciple
