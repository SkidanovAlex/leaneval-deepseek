import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.CFTLib.HR.TransferAux.descentMorphism
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.CFTLib.HR.TransferAux

open CategoryTheory

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
    [FiniteDimensional K M] [FiniteDimensional K E] [FiniteDimensional M E]
    [IsGalois K M] [IsGalois K E]

/-- The coefficient morphism of the inflation `H²(Γ⧸N, (Eˣ)^N) → H²(Γ, Eˣ)`. -/
noncomputable def infCoeff :
    Rep.res (QuotientGroup.mk' (rN K M E))
      ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)) ⟶
      (NK.CFTLib.IdeleHasse.Crux.urep K E) :=
  Rep.ofHom ((NK.CFTLib.IdeleHasse.Crux.urep K E).ρ.quotientToInvariants_lift (rN K M E))

lemma infNatTrans_app_eq :
    (groupCohomology.infNatTrans NK.HassePrinciple.CoeffInt (rN K M E) 2).app
        (NK.CFTLib.IdeleHasse.Crux.urep K E)
      = groupCohomology.map (QuotientGroup.mk' (rN K M E)) (infCoeff (K := K) (M := M) (E := E)) 2 :=
  rfl

/-- **The identification of the transport with the inflation.**  For a Galois-descent morphism `P`
of the invariants `(Eˣ)^N` onto the units `Mˣ` of the level, the transported map
`H²(G⧸N, (Eˣ)^N) → H²(Gal(M/K), Mˣ) ≅ H²(Gal(E/K), Eˣ)` is the ambient inflation. -/
lemma descent_ident (P : Rep.res ((rQuot K M E).symm.toMonoidHom)
      ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)) ⟶
      (NK.CFTLib.IdeleHasse.Crux.urep K M))
    (hP : ∀ x : ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants
        (rN K M E)).V,
      (unitsInclLinearMap K M E : Additive Mˣ →ₗ[NK.HassePrinciple.CoeffInt.{0}]
        Additive Eˣ) (P.hom x) = x.1) :
    groupCohomology.map (rQuot K M E).symm.toMonoidHom P 2 ≫ levelInfMap K M E
      = groupCohomology.map (QuotientGroup.mk' (rN K M E))
          (infCoeff (K := K) (M := M) (E := E)) 2 := by
  have hL : groupCohomology.map (rQuot K M E).symm.toMonoidHom P 2 ≫ levelInfMap K M E
      = groupCohomology.map ((rQuot K M E).symm.toMonoidHom.comp
          (AlgEquiv.restrictNormalHom (K₁ := E) (E := M)))
          ((Rep.resFunctor (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))).map P
            ≫ unitsInclCoeff K M E) 2 := by
    rw [show levelInfMap K M E = groupCohomology.map
        (AlgEquiv.restrictNormalHom (K₁ := E) (E := M)) (unitsInclCoeff K M E) 2 from rfl,
      groupCohomology.map_comp (f := (rQuot K M E).symm.toMonoidHom)
        (g := AlgEquiv.restrictNormalHom (K₁ := E) (E := M)) (φ := P)
        (ψ := unitsInclCoeff K M E) 2]
  rw [hL]
  refine groupCohomology.map_congr (f := (rQuot K M E).symm.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))) (g := QuotientGroup.mk' (rN K M E))
    (rQuot_symm_comp (K := K) (M := M) (E := E)) ?_ 2
  apply LinearMap.ext
  intro x
  change unitsInclLinearMap K M E (P.hom x)
    = (infCoeff (K := K) (M := M) (E := E)).hom.toLinearMap x
  rw [hP x]
  rfl

theorem descent {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
    [FiniteDimensional K M] [FiniteDimensional K E] [FiniteDimensional M E]
    [IsGalois K M] [IsGalois K E]
    (a : groupCohomology (NK.CFTLib.IdeleHasse.Crux.urep K E) 2)
    (h : (NK.CFTLib.HR.TransferAux.resToM K M E).hom a = 0) :
    ∃ β : groupCohomology (NK.CFTLib.IdeleHasse.Crux.urep K M) 2,
      (NK.CFTLib.HR.TransferAux.levelInfMap K M E).hom β = a := by
  have hH1 : Subsingleton (groupCohomology
      (Rep.res (rN K M E).subtype (NK.CFTLib.IdeleHasse.Crux.urep K E)) 1) :=
    h1ResUnits
  obtain ⟨P, hP⟩ : ∃ P : Rep.res ((rQuot K M E).symm.toMonoidHom)
      ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)) ⟶
      (NK.CFTLib.IdeleHasse.Crux.urep K M),
      ∀ x : ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)).V,
        (unitsInclLinearMap K M E : Additive Mˣ →ₗ[NK.HassePrinciple.CoeffInt.{0}]
          Additive Eˣ) (P.hom x) = x.1 :=
    descentMorphism.{0} (K := K) (M := M) (E := E)
  have hex :=
    Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1_general
      (rN K M E) (NK.CFTLib.IdeleHasse.Crux.urep K E) hH1
  have hmem : a ∈ (groupCohomology.map (QuotientGroup.mk' (rN K M E))
      (infCoeff (K := K) (M := M) (E := E)) 2).hom.range := by
    rw [← infNatTrans_app_eq (K := K) (M := M) (E := E), hex]
    show ((groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt
      (G := rN K M E) (H := E ≃ₐ[K] E) (rN K M E).subtype 2).app
      (NK.CFTLib.IdeleHasse.Crux.urep K E)).hom a = 0
    exact h
  obtain ⟨γ, hγ⟩ := LinearMap.mem_range.mp hmem
  refine ⟨(groupCohomology.map (rQuot K M E).symm.toMonoidHom P 2).hom γ, ?_⟩
  rw [← ConcreteCategory.comp_apply]
  exact (congrArg (fun f => f.hom γ) (descent_ident P hP)).trans hγ

end NK.CFTLib.HR.TransferAux
