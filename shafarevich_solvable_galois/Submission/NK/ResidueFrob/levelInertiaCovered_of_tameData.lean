import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level inertia subgroups are the images of the local inertia subgroup, unconditionally

This file removes the named input `NK.ResidueFrob.LevelInertiaCovered` from the boundary of the
local–global residue-field dictionary: given the local structure theory at the place `A`
(`NK.LocalTame.TameData`, i.e. the sibling chapter `Submission/Work/TameData/`'s output) and the
residue-cardinality normalisation `NK.ResidueFrob.ResidueCardMatches`, the level-inertia
statement follows.  Hence the third field of `NK.FrobeniusBridge.PlaceLevelBridgeCore` is *not*
an independent input.

The proof is short because the work is done by two theorems of this chapter:

* `NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel`: an element `h ∈ D_A` acting
  trivially on the residue field of the level `L` differs, on `L`, from an element `δ ∈ D_A`
  fixing `L` pointwise and such that `δ * h` acts trivially on the residue field of **every**
  finite normal level — the *surjectivity* of the level inertia subgroups of the tower;
* `NK.ResidueFrob.inertia_of_levels_of_tameData`: an element of `D_A` acting trivially on the
  residue field of every level lies in the local inertia subgroup `I_κ` (this is
  `NK.FrobeniusBridge.InertiaLevelBridge`, proved here).

So the projective-limit content ("the level inertia groups of the tower below `A` are the images
of `I_κ`") is a theorem in this chapter; the classical proof of the corollary below is
class field theory for the levels plus the identification `Gal(κ̄/κ(μ_{p'})) = I_κ`.
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The level inertia subgroups of the tower below `A` are the images of the local inertia
subgroup**, from the local structure theory at `A` and the residue-cardinality normalisation. -/
theorem levelInertiaCovered_of_tameData (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p q : ℕ}
    (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    (hq : ResidueCardMatches A q) : LevelInertiaCovered A p := by
  intro L _ _ _ g hg hgtriv
  obtain ⟨δ, hδ, hδfix, halltriv⟩ :=
    exists_inertia_of_isTrivialOnResidueAtLevel A L g hg hgtriv
  exact ⟨δ, hδ, hδfix,
    inertia_of_levels_of_tameData A hT hq (δ * g) halltriv (Subgroup.mul_mem _ hδ hg)⟩

/-- **The level inertia subgroups are the images of the local inertia subgroup**, from the local
data `D` of a place. -/
theorem levelInertiaCovered_of_placeLevelData (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (D : NK.FrobeniusBridge.PlaceLevelData A) (hq : ResidueCardMatches A D.q) :
    LevelInertiaCovered A D.p :=
  levelInertiaCovered_of_tameData A D.hT hq

end NK.ResidueFrob
