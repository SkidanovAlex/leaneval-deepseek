import Submission.NK.Reconstruct.GammaObject

/-!
# The finite levels form a directed system

The projective system defining `Γ_K` (`NK.Reconstruct.Gamma`) is indexed by the finite normal
number-field levels of `K'` over `K` (`NK.Reconstruct.FrobLevel`).  This file records that this
index system is *directed*: any two levels are contained in a third (`NK.Reconstruct.FrobLevel.sup`),
namely their compositum, and `FrobLevel.sup` is a least upper bound.  This is what makes the
projective limit defining `Γ_K` well behaved (for instance, the projections `Γ_K → Γ_{L,ℓ}` are
surjective, `NK.Reconstruct.Gamma.proj_surjective`).
-/

namespace NK.Reconstruct

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- **The compositum of two finite normal number-field levels is a finite normal number-field
level.**  This exhibits the index system of `Γ_K` as directed. -/
noncomputable def FrobLevel.sup (L M : FrobLevel K K') : FrobLevel K K' where
  L := L.L ⊔ M.L
  finite := IntermediateField.finiteDimensional_sup L.L M.L
  normal := IntermediateField.normal_sup K K' L.L M.L
  numberField := by
    haveI : FiniteDimensional ℚ ↥(L.L ⊔ M.L) :=
      Module.Finite.trans (R := ℚ) (A := K) (M := ↥(L.L ⊔ M.L))
    exact {}

@[simp] theorem FrobLevel.sup_L (L M : FrobLevel K K') : (L.sup M).L = L.L ⊔ M.L := rfl

theorem FrobLevel.le_sup_left (L M : FrobLevel K K') : L.L ≤ (L.sup M).L :=
  _root_.le_sup_left

theorem FrobLevel.le_sup_right (L M : FrobLevel K K') : M.L ≤ (L.sup M).L :=
  _root_.le_sup_right

theorem FrobLevel.sup_le {L M N : FrobLevel K K'} (hL : L.L ≤ N.L) (hM : M.L ≤ N.L) :
    (L.sup M).L ≤ N.L := _root_.sup_le hL hM

end NK.Reconstruct
