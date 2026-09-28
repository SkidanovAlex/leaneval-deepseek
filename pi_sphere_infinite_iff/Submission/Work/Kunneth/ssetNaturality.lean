import Mathlib
import Submission.Work.Kunneth.pullbackHCup
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.pxTools

/-!
# Naturality of the pullback and of the Kronecker pairing for simplicial sets

Two adapter lemmas used by the Künneth-ring model of `ℂP² × ℂP²`
(`Submission/Work/Kunneth/cp2cp2ModelCpp.lean`):

* `Work.Kunneth.pullbackH_comp` — contravariant functoriality of `pullbackH` in the *pointwise*
  form needed to rewrite `pullbackH X Z (f ≫ g) n x` (the packaged form is
  `Work.Cohomology.pxSsetPullback_comp` at the cochain level);
* `Work.Kunneth.kronH_natural_sset` — the Kronecker pairing is natural:
  `⟨α, f_* c⟩ = ⟨f^* α, c⟩` for every simplicial map `f`, i.e. `kronH` is the evaluation pairing
  between the chain and cochain complexes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- **Functoriality of the pullback in cohomology**, pointwise. -/
theorem pullbackH_comp (X Y Z : SSet) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (x : ↥((cochainC ℤ Z).homology n)) :
    pullbackH X Z (f ≫ g) n x = pullbackH X Y f n (pullbackH Y Z g n x) := by
  obtain ⟨γ, hγ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ Z n x
  rw [pullbackH_cohomologyClassOf X Z (f ≫ g) n γ hγ,
    pullbackH_cohomologyClassOf Y Z g n γ hγ,
    pullbackH_cohomologyClassOf X Y f n (Kunneth.ssetPullback Y Z g n γ)
      (Work.Cohomology.pxSsetPullback_cocycle Y Z g n γ hγ)]
  apply Work.Cohomology.cohomologyClassOf_congr
  exact Work.Cohomology.pxSsetPullback_comp X Y Z f g n γ

/-- **Naturality of the Kronecker pairing for simplicial sets**: `⟨α, f_* c⟩ = ⟨f^* α, c⟩`. -/
theorem kronH_natural_sset (X Y : SSet) (f : X ⟶ Y) (n : ℕ)
    (α : ↥((cochainC ℤ Y).homology n)) (c : ↥((chainC ℤ X).homology n)) :
    kronH ℤ Y n α
        ((HomologicalComplex.homologyMap (SSet.chainComplexMap f zz) n).hom c)
      = kronH ℤ X n (pullbackH X Y f n α) c := by
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ Y n α
  have hsurj : Function.Surjective (fun z : (sChain X).cycles n =>
      ((sChain X).homologyπ n).hom z) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hsurj c
  have hnat : (HomologicalComplex.homologyMap (SSet.chainComplexMap f zz) n).hom
      (((sChain X).homologyπ n).hom z)
      = ((sChain Y).homologyπ n).hom
        ((HomologicalComplex.cyclesMap (SSet.chainComplexMap f zz) n).hom z) := by
    have h := congrArg (fun (g : (sChain X).cycles n ⟶ (sChain Y).homology n) =>
      ModuleCat.Hom.hom g z) (HomologicalComplex.homologyπ_naturality
        (SSet.chainComplexMap f zz) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have h2 : ((sChain Y).iCycles n).hom
        ((HomologicalComplex.cyclesMap (SSet.chainComplexMap f zz) n).hom z)
      = ((SSet.chainComplexMap f zz).f n).hom (((sChain X).iCycles n).hom z) := by
    have h := congrArg (fun (g : (sChain X).cycles n ⟶ (sChain Y).X n) =>
      ModuleCat.Hom.hom g z) (HomologicalComplex.cyclesMap_i (SSet.chainComplexMap f zz) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  rw [hnat,
    kronH_apply ℤ Y β hβ ((HomologicalComplex.cyclesMap (SSet.chainComplexMap f zz) n).hom z),
    pullbackH_cohomologyClassOf X Y f n β hβ,
    kronH_apply ℤ X (Kunneth.ssetPullback X Y f n β)
      (Work.Cohomology.pxSsetPullback_cocycle X Y f n β hβ) z,
    h2, Kunneth.ssetPullback, LinearMap.dualMap_apply]

end

end Work.Kunneth

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- The cochain pullback along the identity is the identity. -/
lemma ssetPullback_id (X : SSet) (n : ℕ) (γ : Cochain ℤ X n) :
    Kunneth.ssetPullback X X (𝟙 X) n γ = γ := by
  apply Work.Cohomology.cup_ext ℤ X
  intro σ
  rw [Kunneth.ssetPullback_genEval]
  rfl

/-- **The pullback along the identity is the identity.** -/
theorem pullbackH_id (X : SSet) (n : ℕ) (y : ↥((cochainC ℤ X).homology n)) :
    pullbackH X X (𝟙 X) n y = y := by
  obtain ⟨γ, hγ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ X n y
  rw [pullbackH_cohomologyClassOf X X (𝟙 X) n γ hγ]
  apply Work.Cohomology.cohomologyClassOf_congr
  exact ssetPullback_id X n γ

end

end Work.Kunneth
