import Submission.NK.Reconstruct.GammaSup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The meet of two finite levels

The index system of the projective system defining `Γ_K` (`NK.Reconstruct.Gamma`) is the set of
finite normal number-field levels of `K'` over `K` (`NK.Reconstruct.FrobLevel`).  This file proves
that it is closed under *intersection* (`NK.Reconstruct.FrobLevel.inf`), the lattice-dual
companion of `NK.Reconstruct.FrobLevel.sup` (`Submission/Work/Reconstruct/GammaSup.lean`).

The meet is what allows the monotonicity statements for the ℓ-ranks
(`NK.Reconstruct.RankStrictMonoInput`) to be applied to the pair `K₁ ∩ K₂ ⊆ K₁` in Shimizu's
Proposition 4f.5.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- **The intersection of two finite normal number-field levels is a finite normal number-field
level.** -/
noncomputable def FrobLevel.inf (L M : FrobLevel K K') : FrobLevel K K' where
  L := L.L ⊓ M.L
  finite := inferInstance
  normal := by
    haveI : Normal K ↥(L.L ⊓ M.L : IntermediateField K K') := inferInstance
    exact ‹Normal K ↥(L.L ⊓ M.L : IntermediateField K K')›
  numberField := by
    haveI : FiniteDimensional ℚ ↥(L.L ⊓ M.L : IntermediateField K K') :=
      Module.Finite.trans (R := ℚ) (A := K) (M := ↥(L.L ⊓ M.L : IntermediateField K K'))
    exact {}

@[simp] theorem FrobLevel.inf_L (L M : FrobLevel K K') : (L.inf M).L = L.L ⊓ M.L := rfl

theorem FrobLevel.inf_le_left (L M : FrobLevel K K') : (L.inf M).L ≤ L.L := _root_.inf_le_left
theorem FrobLevel.inf_le_right (L M : FrobLevel K K') : (L.inf M).L ≤ M.L := _root_.inf_le_right

end NK.Reconstruct
