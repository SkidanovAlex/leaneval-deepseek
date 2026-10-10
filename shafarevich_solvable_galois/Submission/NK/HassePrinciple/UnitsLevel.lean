import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.NK.HassePrinciple.LevelDictionary
import Submission.NK.HassePrinciple.Mu
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The level group acting on the units -/

/-- **The restriction map from the level group to `Gal(L/K)`**: the descent of
`levelRestrictHom V L` along the quotient `↥V ↠ LevelGroup V L`. -/
noncomputable abbrev levelGroupRestrictHom (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : LevelGroup V L →* Gal(↥L/K) :=
  QuotientGroup.lift (L.fixingSubgroup.subgroupOf V) (levelRestrictHom V L)
    (by
      intro x hx
      have hx' : x ∈ (levelRestrictHom V L).ker := by rwa [levelRestrictHom_ker V L]
      exact MonoidHom.mem_ker.mp hx')

/-- Computation rule for `levelGroupRestrictHom`. -/
@[simp]
theorem levelGroupRestrictHom_mk (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (v : ↥V) :
    levelGroupRestrictHom V L (QuotientGroup.mk v) =
      levelRestrict L (v : Gal(K'/K)) := rfl

/-- **The representation of the level group on the units `Lˣ`.** -/
noncomputable abbrev unitsLevelRep (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : Rep CoeffInt (LevelGroup V L) :=
  Rep.res (levelGroupRestrictHom V L) (unitsRep K ↥L)

/-- The action of the level group on `Lˣ`, computed at the class of an element of `V`. -/
theorem unitsLevelRep_ρ_apply (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (v : ↥V)
    (x : (Additive (↥L)ˣ)) :
    (unitsLevelRep V L).ρ (QuotientGroup.mk v) x = (levelRestrict L (v : Gal(K'/K))) • x := rfl

/-- **The units level cohomology** `H²(U ⧸ (U ⊓ Gal(K'/L)), Lˣ)`. -/
noncomputable abbrev UnitsLevelH2 (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : ModuleCat CoeffInt :=
  groupCohomology (unitsLevelRep V L) 2

/-! ## The unit inclusion as an equivariant map -/

/-- The inclusion of units `Lˣ → L'ˣ` attached to a level inclusion `L ≤ L'`, as a monoid
homomorphism. -/
noncomputable abbrev unitsInclHom (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') :
    (↥L)ˣ →* (↥L')ˣ :=
  Units.map (IntermediateField.inclusion h).toMonoidHom

/-- The unit inclusion, as a `CoeffInt`-linear map on the additive groups. -/
noncomputable def unitsInclLinearMap (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') :
    Additive (↥L)ˣ →ₗ[CoeffInt] Additive (↥L')ˣ where
  toFun x := Additive.ofMul (unitsInclHom L L' h (Additive.toMul x))
  map_add' x y := by
    change Additive.ofMul (unitsInclHom L L' h (Additive.toMul x * Additive.toMul y)) =
      Additive.ofMul (unitsInclHom L L' h (Additive.toMul x)) +
        Additive.ofMul (unitsInclHom L L' h (Additive.toMul y))
    rw [map_mul]
    rfl
  map_smul' n x := by
    obtain ⟨z⟩ := n
    show Additive.ofMul (unitsInclHom L L' h ((Additive.toMul x) ^ z)) =
      Additive.ofMul ((unitsInclHom L L' h (Additive.toMul x)) ^ z)
    rw [map_zpow]

/-- The computation rule for `unitsInclLinearMap`. -/
theorem unitsInclLinearMap_apply (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L')
    (x : Additive (↥L)ˣ) :
    unitsInclLinearMap L L' h x = Additive.ofMul (unitsInclHom L L' h (Additive.toMul x)) := rfl

/-! ## What remains in this file

The two steps that complete the units level system are the *equivariance* of the unit inclusion

`unitsIncl_smul : unitsInclLinearMap h ((levelRestrict L σ) • x) = (levelRestrict L' σ) •
  unitsInclLinearMap h x`   (`σ : Gal(K'/K)`, `x : Additive (↥L)ˣ`),

which is proved by `Units.ext` together with `AlgEquiv.restrictNormalHom_apply` (both sides have
underlying element `σ (↑x)` in `K'`), and then the transition morphism

`unitsLevelMapCoeff h : Rep.res (levelQuotHom h) (unitsLevelRep V L) ⟶ unitsLevelRep V L'`

built from it by `Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap ...)` with the
intertwining proof by induction on `LevelGroup V L'` — exactly as
`NK.BrauerTwist.levelMapCoeff` does for `μ_p`.  The transition map of the level system is then

`unitsLevelMap h := groupCohomology.map (levelQuotHom h) (unitsLevelMapCoeff h) 2`,

and its two coherence laws (`map_refl`, `map_comp`) make
`⟨fun L => UnitsLevelH2 V L, unitsLevelMap, ...⟩` a `NK.BrauerTwist.LevelSystem`, whose colimit is
the `H2Units` of README §10.4.  The Kummer morphism from the `μ_p` level system
(`NK.BrauerTwist.LevelH2`) to it is `groupCohomology.map (MonoidHom.id _) (kummerIncl ...) 2`
level-wise, with the same naturality argument.
-/

end NK.HassePrinciple
