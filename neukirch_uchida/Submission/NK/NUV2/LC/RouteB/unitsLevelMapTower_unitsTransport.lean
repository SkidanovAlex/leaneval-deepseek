import Mathlib
import Submission.NK.NUV2.LC.finiteSupportTwistDefs
import Submission.NK.NUV2.LC.LocalLevelSystem
import Submission.NK.NUV2.LC.RouteB.survivalSetup

namespace NK.NUV2.LC.RouteB

open CategoryTheory

-- The terms produced by `groupCohomology.mapIso_hom` and by the definitions of the coefficient
-- morphisms carry `LinearEquiv.refl`-style transports; comparing them needs transparent `isDefEq`
-- (see also `NK.NUV2.LC.RouteB.unitsLift_kummerLevel`).
set_option backward.isDefEq.respectTransparency false

-- The (local) `haveI` used in the group-theoretic bookkeeping below is an *instance* (it is
-- consumed by `IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply`), not a plain hypothesis; the
-- `haveI`-style linter would wrongly suggest replacing it.
set_option linter.style.haveILetI false

/-- Composition in `Rep` evaluated at an element: `(f ≫ g).hom.toLinearMap x = g (f x)`.  This
avoids mentioning the `CoeffInt`-universe of the intermediate `LinearMap` explicitly. -/
private lemma hom_comp_toLinearMap_apply {k G : Type} [CommRing k] [Group G] {A B C : Rep k G}
    (f : A ⟶ B) (g : B ⟶ C) (x : A.V) :
    (Rep.Hom.hom (f ≫ g)).toLinearMap x =
      (Rep.Hom.hom g).toLinearMap ((Rep.Hom.hom f).toLinearMap x) := rfl

/-- **The tower level map commutes with the definite transports to the number-field vocabulary.**

`NK.NUV2.LC.unitsTransport L : UnitsLevelH2 ⊤ L ≃+ H²(Gal(↥L/F), ↥Lˣ)` is the definite transport
along `NK.NUV2.LC.levelGroupEquivTop L` (built with `groupCohomology.mapIso`), and
`NK.NUV2.LC.unitsLevelMapTower` is the inflation-compatible level map
`H²(Gal(↥L/F), ↥Lˣ) → H²(Gal(↥M/F), ↥Mˣ)` (via `AlgEquiv.restrictNormalHom` and the unit inclusion,
`NK.NUV2.LC.LocalLevelSystem`).  The claim is that the transports are natural with respect to the
level maps, i.e. that the obvious square commutes:

`unitsLevelMapTower (unitsTransport L c) = unitsTransport M (unitsLevelMap ⊤ (L ≤ M) c)`.

Route.  Expand `unitsTransport` (`groupCohomology.mapIso_hom` : it is `map (levelGroupEquivTop L).symm
(ofHom ⟨LinearEquiv.refl, ...⟩) 2`), `unitsLevelMap` (`= map (levelQuotHom h) (unitsLevelMapCoeff ⊤ h) 2`)
and `unitsLevelMapTower` (`= map (AlgEquiv.restrictNormalHom) (unitsInclTowerCoeff) 2`).  Then merge
each pair of `map`s into a single `map` with `groupCohomology.map_comp` (or the helper results
`NK.NUV2.LC.RouteB.map_f_comp_id`, `NK.NUV2.LC.RouteB.map_resFunctor_map`,
`NK.NUV2.LC.RouteB.map_id_comp_apply` in `locUnits_tower_eq_zero.lean`), using the group-map identity
`AlgEquiv.restrictNormalHom = (levelGroupEquivTop L) ∘ (levelQuotHom h) ∘ (levelGroupEquivTop M).symm`
(prove it by `MonoidHom.ext` + `QuotientGroup.induction_on` + `simp [levelGroupEquivTop_apply,
levelGroupRestrictHom_mk]`), and finally `groupCohomology.map_congr` since the two remaining
coefficient morphisms have the same underlying linear map (the unit inclusion `↥Lˣ → ↥Mˣ`; this is
where the hypothesis `hAM` is used, cmp. `NK.NUV2.LC.RouteB.unitsLift_kummerLevel`
(`unitsLift_kummerLevel.lean`) which is a complete template for this style of bookkeeping).
NOTA BENE: this file must NOT import `Submission.NK.NUV2.LC.RouteB.level_kills_aux` (or
`muLift.lean`, `locL_kummerLevel*.lean`, `hbnProfinite_top.lean`) — those transitively redeclare
`NK.NUV2.ABHN.levelCompare` and then this module cannot be imported by the requester (whose
environment already contains the version from `NUV2/ABHN/muColimEquivH2ProfiniteOfIsPrimitiveRoot`). -/
theorem unitsLevelMapTower_unitsTransport {F : Type} [Field F] [NumberField F] {F' : Type} [Field F']
    [Algebra F F'] [IsSepClosure F F']
    (L M : FiniteGaloisIntermediateField F F')
    [Algebra ↥(L : IntermediateField F F') ↥(M : IntermediateField F F')]
    [IsScalarTower F ↥(L : IntermediateField F F') ↥(M : IntermediateField F F')]
    (h : L ≤ M)
    (hAM : ∀ x : ↥(L : IntermediateField F F'),
      algebraMap ↥(L : IntermediateField F F') ↥(M : IntermediateField F F') x
        = IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L M).mp h) x)
    (c : NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L) :
    (NK.NUV2.LC.unitsLevelMapTower (F := F) (L := ↥(L : IntermediateField F F'))
        (M := ↥(M : IntermediateField F F')))
        ((NK.NUV2.LC.unitsTransport (K := F) (K' := F') L) c)
      = (NK.NUV2.LC.unitsTransport (K := F) (K' := F') M)
          (((NK.HassePrinciple.unitsLevelMap (⊤ : Subgroup Gal(F'/F))
            ((FiniteGaloisIntermediateField.le_iff L M).mp h))).hom c) := by
  -- Combining two successive applications of `H²`-maps into a single application of the composite.
  have hcomp : ∀ {X Y Z : ModuleCat NK.HassePrinciple.CoeffInt} (f : X ⟶ Y) (g : Y ⟶ Z)
      (x : X), ConcreteCategory.hom g (ConcreteCategory.hom f x) =
        ConcreteCategory.hom (f ≫ g) x := fun f g x => rfl
  -- Unfold the two transports along `levelGroupEquivTop` into `map`-applications.
  rw [show NK.NUV2.LC.unitsTransport (K := F) (K' := F') L c =
      (groupCohomology.mapIso
        (A := NK.HassePrinciple.unitsRep F ↥(L : IntermediateField F F'))
        (B := NK.HassePrinciple.unitsLevelRep (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L)
        (NK.NUV2.LC.levelGroupEquivTop (K := F) (K' := F') L)
        (LinearEquiv.refl NK.HassePrinciple.CoeffInt (Additive (↥(L : IntermediateField F F'))ˣ))
        (fun g => by induction g using QuotientGroup.induction_on with | H v => rfl) 2).hom c from rfl]
  rw [show NK.NUV2.LC.unitsTransport (K := F) (K' := F') M _ =
      (groupCohomology.mapIso
        (A := NK.HassePrinciple.unitsRep F ↥(M : IntermediateField F F'))
        (B := NK.HassePrinciple.unitsLevelRep (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) M)
        (NK.NUV2.LC.levelGroupEquivTop (K := F) (K' := F') M)
        (LinearEquiv.refl NK.HassePrinciple.CoeffInt (Additive (↥(M : IntermediateField F F'))ˣ))
        (fun g => by induction g using QuotientGroup.induction_on with | H v => rfl) 2).hom _ from rfl]
  rw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom]
  -- Unfold the tower level map and the level map of the units level system.
  rw [show (NK.NUV2.LC.unitsLevelMapTower (F := F) (L := ↥(L : IntermediateField F F'))
      (M := ↥(M : IntermediateField F F'))) =
      groupCohomology.map (AlgEquiv.restrictNormalHom (K₁ := ↥(M : IntermediateField F F'))
        (E := ↥(L : IntermediateField F F'))) (NK.NUV2.LC.unitsInclTowerCoeff
          (F := F) (L := ↥(L : IntermediateField F F')) (M := ↥(M : IntermediateField F F'))) 2 from rfl]
  simp only [NK.HassePrinciple.unitsLevelMap]
  -- Turn both sides into the application of a single composite of two `H²`-maps.
  rw [hcomp, hcomp]
  -- Merge the two `map`s on each side into a single `map` (`groupCohomology.map_comp`).
  conv_lhs => rw [← groupCohomology.map_comp]
  conv_rhs => rw [← groupCohomology.map_comp]
  refine congrArg (fun (z : NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L ⟶
      (groupCohomology (NK.HassePrinciple.unitsRep F ↥(M : IntermediateField F F')) 2)) =>
      ConcreteCategory.hom z c) ?_
  refine groupCohomology.map_congr ?_ ?_ 2
  · -- The two group homomorphisms agree: `restrictNormalHom` factors through the level quotient.
    haveI : IsScalarTower ↥(L : IntermediateField F F') ↥(M : IntermediateField F F') F' :=
      IsScalarTower.of_algebraMap_eq (fun x => by rw [hAM x]; rfl)
    have hkey : (NK.NUV2.LC.levelGroupEquivTop L).toMonoidHom.comp
        (NK.BrauerHasse.levelQuotHom (U := ⊤) ((FiniteGaloisIntermediateField.le_iff L M).mp h))
      = (AlgEquiv.restrictNormalHom (K₁ := ↥(M : IntermediateField F F'))
          (E := ↥(L : IntermediateField F F'))).comp
          ((NK.NUV2.LC.levelGroupEquivTop M).toMonoidHom) := by
      refine MonoidHom.ext (fun x => ?_)
      induction x using QuotientGroup.induction_on with
      | H u =>
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          NK.NUV2.LC.levelGroupEquivTop_apply,
          NK.HassePrinciple.levelGroupRestrictHom_mk, NK.BrauerHasse.levelQuotHom,
          QuotientGroup.map_mk, MonoidHom.id_apply]
        exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply ↥(L : IntermediateField F F')
          ↥(M : IntermediateField F F') _
    ext σ
    have hh := DFunLike.congr_fun hkey ((NK.NUV2.LC.levelGroupEquivTop M).symm σ)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hh
    simp only [MonoidHom.comp_apply]
    rw [← hh]
    exact MulEquiv.symm_apply_apply (NK.NUV2.LC.levelGroupEquivTop L) _
  · -- The two coefficient morphisms have the same underlying linear map.
    ext x
    rw [hom_comp_toLinearMap_apply, hom_comp_toLinearMap_apply]
    simp only [Rep.resMap_hom_toLinearMap, Rep.hom_ofHom,
      Representation.IntertwiningMap.toLinearMap_apply, LinearEquiv.refl_toLinearMap,
      LinearMap.id_apply]
    have h1 : (Rep.Hom.hom (NK.NUV2.LC.unitsInclTowerCoeff (F := F)
        (L := ↥(L : IntermediateField F F')) (M := ↥(M : IntermediateField F F')))) x
        = Additive.ofMul (Units.map (algebraMap ↥(L : IntermediateField F F')
            ↥(M : IntermediateField F F')).toMonoidHom (Additive.toMul x)) := rfl
    have h2 : (Rep.Hom.hom (NK.HassePrinciple.unitsLevelMapCoeff (K := F) (K' := F')
        (⊤ : Subgroup Gal(F'/F)) ((FiniteGaloisIntermediateField.le_iff L M).mp h))) x
        = Additive.ofMul (Units.map (IntermediateField.inclusion
            ((FiniteGaloisIntermediateField.le_iff L M).mp h)).toMonoidHom (Additive.toMul x)) := rfl
    -- The two unit maps agree by the hypothesis `hAM`.
    rw [h1, h2, show (algebraMap ↥(L : IntermediateField F F')
          ↥(M : IntermediateField F F')).toMonoidHom
        = (IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L M).mp h)).toMonoidHom
        from MonoidHom.ext hAM]

end NK.NUV2.LC.RouteB
