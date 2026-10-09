import Submission.NK.FrobeniusBridge.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius bridge: the level-wise API

Basic lemmas about the level-wise Frobenius condition `NK.FrobeniusBridge.frobAtLevel` and the
infinite-level predicate `NK.FrobeniusBridge.IsFrobAtPlace`: compatibility with the restriction
maps of the projective system, and the congruence rule (the condition only depends on the
restriction to the level).
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **Two elements have the same restriction to a normal level iff their ratio lies in the fixing
subgroup of the level.** -/
theorem restrictNormalHom_eq_iff_mem_fixingSubgroup {L : IntermediateField K K'} [Normal K L]
    (σ τ : Gal(K'/K)) :
    AlgEquiv.restrictNormalHom L σ = AlgEquiv.restrictNormalHom L τ ↔
      σ * τ⁻¹ ∈ L.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker (K := K) (L := K') L, MonoidHom.mem_ker,
    map_mul, map_inv, mul_inv_eq_one]

/-- **The level-wise Frobenius condition depends only on the restriction to the level.** -/
theorem frobAtLevel_congr (A : FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] {g g' : Gal(K'/K)}
    (h : AlgEquiv.restrictNormalHom L g = AlgEquiv.restrictNormalHom L g') :
    frobAtLevel A L g ↔ frobAtLevel A L g' := by
  unfold frobAtLevel
  rw [h]

/-- **The level-wise Frobenius condition is invariant under the fixing subgroup of the level.** -/
theorem frobAtLevel_of_mul_mem_fixingSubgroup (A : FinitePlaceOf K K')
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    {g g' : Gal(K'/K)} (h : g * g'⁻¹ ∈ L.fixingSubgroup)
    (hg : frobAtLevel A L g) : frobAtLevel A L g' :=
  (frobAtLevel_congr A L ((restrictNormalHom_eq_iff_mem_fixingSubgroup g g').mpr h)).mp hg

/-- The infinite-level predicate only depends on the restriction to each level; in particular two
elements agreeing on every finite normal level are simultaneously Frobenius elements at `A`. -/
theorem isFrobAtPlace_congr (A : FinitePlaceOf K K') {g g' : Gal(K'/K)}
    (h : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
      AlgEquiv.restrictNormalHom L g = AlgEquiv.restrictNormalHom L g') :
    IsFrobAtPlace A g ↔ IsFrobAtPlace A g' :=
  forall_congr' fun L => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    frobAtLevel_congr A L (h L)

end NK.FrobeniusBridge
