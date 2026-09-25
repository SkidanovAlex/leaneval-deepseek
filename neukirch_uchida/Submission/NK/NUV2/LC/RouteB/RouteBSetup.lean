import Mathlib
import Submission.NK.NUV2.LC.RouteB.kummerMap_locUnits
import Submission.NK.NUV2.LC.finiteSupportTwistDefs
import Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot
import Submission.NK.HassePrinciple.MuLevel
import Submission.NK.HassePrinciple.LocalUnits

/-!
# Base-`K` transports for the `μ_p` and units level cohomologies, and their Kummer compatibility

`Submission/Work/NUV2/LC/finiteSupportTwistDefs.lean` builds the definite transport
`unitsTransport L : H²(LevelGroup ⊤ L, Lˣ) ≃+ H²(Gal(↥L/K), ↥Lˣ)` along the level dictionary
`levelGroupEquivTop L : LevelGroup ⊤ L ≃* Gal(↥L/K)`.  This file adds the companion transport for
the cyclotomic coefficients, `muTransport`, and proves that the two are compatible with the Kummer
morphisms `kummerLevel`/`kummerMap`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

universe u

namespace NK.NUV2.LC.RouteB

open CategoryTheory

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The units transport over the base `K` itself** (the definition of
`NK.NUV2.LC.unitsTransport`, restated here so that it lives next to its companion `muTransport`
and its computation rule is available). -/
noncomputable def unitsTransportK (L : FiniteGaloisIntermediateField K K') :
    (NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') (⊤ : Subgroup Gal(K'/K)) L) ≃+
      (groupCohomology (NK.HassePrinciple.unitsRep K
        ↥(L.toIntermediateField : IntermediateField K K')) 2) := by
  refine ((groupCohomology.mapIso
    (A := NK.HassePrinciple.unitsRep K ↥(L.toIntermediateField : IntermediateField K K'))
    (B := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') (⊤ : Subgroup Gal(K'/K)) L)
    (levelGroupEquivTop (K := K) (K' := K') L)
    (LinearEquiv.refl NK.HassePrinciple.CoeffInt
      (Additive (↥(L.toIntermediateField : IntermediateField K K'))ˣ)) ?_ 2).toLinearEquiv).toAddEquiv
  intro g
  induction g using QuotientGroup.induction_on with
  | H v => rfl

/-- The computation rule for `unitsTransportK`. -/
theorem unitsTransportK_apply (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') (⊤ : Subgroup Gal(K'/K)) L) :
    unitsTransportK (K := K) (K' := K') L a =
      (groupCohomology.mapIso
        (A := NK.HassePrinciple.unitsRep K ↥(L.toIntermediateField : IntermediateField K K'))
        (B := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') (⊤ : Subgroup Gal(K'/K)) L)
        (levelGroupEquivTop (K := K) (K' := K') L)
        (LinearEquiv.refl NK.HassePrinciple.CoeffInt
          (Additive (↥(L.toIntermediateField : IntermediateField K K'))ˣ))
        (fun g => by
          induction g using QuotientGroup.induction_on with
          | H v => rfl) 2).hom a := rfl

/-- **The `μ_p` transport over the base `K` itself**: the level cohomology
`H²(LevelGroup ⊤ L, μ_p(L))` is the number-field cohomology `H²(Gal(↥L/K), μ_p(↥L))` along the
level dictionary `levelGroupEquivTop`. -/
noncomputable def muTransport (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L ≃+
      (groupCohomology (NK.HassePrinciple.muRep p K
        ↥(L.toIntermediateField : IntermediateField K K')) 2) := by
  refine ((groupCohomology.mapIso
    (A := NK.HassePrinciple.muRep p K ↥(L.toIntermediateField : IntermediateField K K'))
    (B := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L)
    (levelGroupEquivTop (K := K) (K' := K') L)
    (LinearEquiv.refl NK.HassePrinciple.CoeffInt
      (Additive ↥(rootsOfUnity p ↥(L.toIntermediateField : IntermediateField K K')))) ?_ 2).toLinearEquiv).toAddEquiv
  intro g
  induction g using QuotientGroup.induction_on with
  | H v => rfl

/-- The computation rule for `muTransport`. -/
theorem muTransport_apply (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L) :
    muTransport (K := K) (K' := K') p L a =
      (groupCohomology.mapIso
        (A := NK.HassePrinciple.muRep p K ↥(L.toIntermediateField : IntermediateField K K'))
        (B := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L)
        (levelGroupEquivTop (K := K) (K' := K') L)
        (LinearEquiv.refl NK.HassePrinciple.CoeffInt
          (Additive ↥(rootsOfUnity p ↥(L.toIntermediateField : IntermediateField K K'))))
        (fun g => by
          induction g using QuotientGroup.induction_on with
          | H v => rfl) 2).hom a := rfl

/-- **The Kummer morphism commutes with the base-`K` transports**: the units transport of the
level-wise Kummer image of a `μ_p`-level class is the Kummer map of its `μ_p` transport. -/
theorem kummerMap_transport (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L) :
    unitsTransportK (K := K) (K' := K') L
        ((NK.HassePrinciple.kummerLevel p (⊤ : Subgroup Gal(K'/K)) L).hom a) =
      (NK.HassePrinciple.kummerMap p K
        ↥(L.toIntermediateField : IntermediateField K K')).hom
        (muTransport (K := K) (K' := K') p L a) := by
  have hcomp : ∀ {X Y Z : ModuleCat NK.HassePrinciple.CoeffInt} (f : X ⟶ Y) (g : Y ⟶ Z)
      (x : X), ConcreteCategory.hom g (ConcreteCategory.hom f x) =
        ConcreteCategory.hom (f ≫ g) x := fun f g x => rfl
  rw [unitsTransportK_apply, muTransport_apply]
  rw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom]
  simp only [NK.HassePrinciple.kummerLevel, NK.HassePrinciple.kummerMap]
  rw [hcomp, hcomp]
  conv_lhs => rw [← groupCohomology.map_comp]
  conv_rhs => rw [← groupCohomology.map_comp]
  refine congrArg (fun (z : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L ⟶
      (groupCohomology (NK.HassePrinciple.unitsRep K
        ↥(L.toIntermediateField : IntermediateField K K')) 2)) => ConcreteCategory.hom z a) ?_
  exact groupCohomology.map_congr (by rw [MonoidHom.id_comp, MonoidHom.comp_id]) (by rfl) 2

end NK.NUV2.LC.RouteB
