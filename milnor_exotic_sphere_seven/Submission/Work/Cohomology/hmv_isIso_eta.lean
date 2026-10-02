import Mathlib
import Submission.Work.Cohomology.relCohMV_honest_defs
import Submission.Work.Cohomology.relCohMV_honest_prereq

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The comparison maps of the relative Mayer–Vietoris sequence are isomorphisms

For a space `X`, a subset `A ⊆ X` and subsets `U, V ⊆ X` (the two open pieces of a cover), the
comparison maps

* `HMV.etaU A U V : C^{U,V}(U, U∩A) ⟶ C_*(U, U∩A)`,
* `HMV.etaV A U V : C^{U,V}(V, V∩A) ⟶ C_*(V, V∩A)`,
* `relMVUVPhi X A U V : C^{U,V}(U∩V, U∩V∩A) ⟶ C_*(U∩V, (U∩V)∩A)`

identifying a *small* simplex of the subspace with the same singular simplex are isomorphisms of
chain complexes (not merely quasi-isomorphisms): a simplex of `U` (resp. `V`, `U ∩ V`) is
automatically small, so the "small chains" subcomplex is *all* of the singular chains of the
subspace.

The three maps are instances of the following elementary fact: the map induced by an isomorphism
of commutative squares on cokernels is an isomorphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

/-- **The map induced on cokernels by an isomorphism of commutative squares is an isomorphism.**

Given a commutative square `f ≫ g = g' ≫ f'` in which the two vertical maps `g`, `g'` are
isomorphisms, the induced map `cokernel f ⟶ cokernel f'` is an isomorphism.  We only need the
special case where the induced map is given as some `φ` with `cokernel.π f ≫ φ = g ≫ cokernel.π f'`
(this is how the comparison maps `HMV.etaU`, `HMV.etaV`, `relMVUVPhi` are defined, as
`cokernel.desc`). -/
theorem isIso_cokernelDesc_iso_square {C : Type*} [Category C] [HasZeroMorphisms C]
    {X₁ X₂ X₃ X₄ : C} (f : X₁ ⟶ X₂) [HasCokernel f] (f' : X₃ ⟶ X₄) [HasCokernel f']
    (g : X₂ ⟶ X₄) (g' : X₁ ⟶ X₃) (hg : IsIso g) (hg' : IsIso g') (w : f ≫ g = g' ≫ f')
    (φ : cokernel f ⟶ cokernel f') (hφ : cokernel.π f ≫ φ = g ≫ cokernel.π f') :
    IsIso φ := by
  have h1 : cokernel.π f ≫ cokernel.map f f' g' g w = g ≫ cokernel.π f' := by
    change cokernel.π f ≫ cokernel.desc f (g ≫ cokernel.π f') _ = g ≫ cokernel.π f'
    rw [cokernel.π_desc]
  have heq : φ = cokernel.map f f' g' g w := (cancel_epi (cokernel.π f)).1 (hφ.trans h1.symm)
  rw [heq]
  exact (cokernel.mapIso f f' (@asIso _ _ _ _ g' hg') (@asIso _ _ _ _ g hg) w).isIso_hom

theorem hmv_isIso_eta (X : TopCat) (A U V : Set X) :
    CategoryTheory.IsIso (Work.Cohomology.HMV.etaU A U V) ∧
      CategoryTheory.IsIso (Work.Cohomology.HMV.etaV A U V) ∧
      CategoryTheory.IsIso (Work.Cohomology.relMVUVPhi X A U V) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the `U`-piece
    let f := Work.Cohomology.relMVτ₂U U V A
    let f' := Work.Cohomology.inclChains (TopCat.of ↥U) (Work.Cohomology.interAU A U)
    let g := Work.Cohomology.smallInToSingA U V U
    let a := Work.Cohomology.smallInToSingA U V (U ∩ A)
    let b := SSet.chainComplexMap
      (TopCat.toSSet.map (Work.Cohomology.HMV.subInterIso A U).hom) (ModuleCat.of ℤ ℤ)
    have ha : IsIso a := by
      haveI : IsIso (Work.Cohomology.smallInLift U V (U ∩ A)) :=
        Work.Cohomology.HMV.isIso_smallInLift_of_le U V (U ∩ A)
          (Set.inter_subset_left : U ∩ A ⊆ U)
      exact Functor.map_isIso _ _
    have hb : IsIso b := by
      haveI : IsIso (TopCat.toSSet.map (Work.Cohomology.HMV.subInterIso A U).hom) :=
        Functor.map_isIso _ _
      exact Functor.map_isIso _ _
    have hg : IsIso g := by
      haveI : IsIso (Work.Cohomology.smallInLift U V U) :=
        Work.Cohomology.HMV.isIso_smallInLift_of_le U V U (le_refl U)
      exact Functor.map_isIso _ _
    have hg' : IsIso (a ≫ b) := @IsIso.comp_isIso _ _ _ _ _ a b ha hb
    have hw : f ≫ g = (a ≫ b) ≫ f' := by
      show Work.Cohomology.relMVτ₂U U V A ≫ Work.Cohomology.smallInToSingA U V U = _
      rw [Work.Cohomology.HMV.relMVτ₂U_eq, Category.assoc]
      exact Work.Cohomology.HMV.subInclChain_U_natural A U V
    exact isIso_cokernelDesc_iso_square f f' g (a ≫ b) hg hg' hw
      (Work.Cohomology.HMV.etaU A U V) (Work.Cohomology.HMV.etaU_comp A U V)
  · -- the `V`-piece
    let f := Work.Cohomology.relMVτ₂V U V A
    let f' := Work.Cohomology.inclChains (TopCat.of ↥V) (Work.Cohomology.interAU A V)
    let g := Work.Cohomology.smallInToSingA U V V
    let a := Work.Cohomology.smallInToSingA U V (V ∩ A)
    let b := SSet.chainComplexMap
      (TopCat.toSSet.map (Work.Cohomology.HMV.subInterIso A V).hom) (ModuleCat.of ℤ ℤ)
    have ha : IsIso a := by
      haveI : IsIso (Work.Cohomology.smallInLift U V (V ∩ A)) :=
        Work.Cohomology.HMV.isIso_smallInLift_of_le_V U V (V ∩ A)
          (Set.inter_subset_left : V ∩ A ⊆ V)
      exact Functor.map_isIso _ _
    have hb : IsIso b := by
      haveI : IsIso (TopCat.toSSet.map (Work.Cohomology.HMV.subInterIso A V).hom) :=
        Functor.map_isIso _ _
      exact Functor.map_isIso _ _
    have hg : IsIso g := by
      haveI : IsIso (Work.Cohomology.smallInLift U V V) :=
        Work.Cohomology.HMV.isIso_smallInLift_of_le_V U V V (le_refl V)
      exact Functor.map_isIso _ _
    have hg' : IsIso (a ≫ b) := @IsIso.comp_isIso _ _ _ _ _ a b ha hb
    have hw : f ≫ g = (a ≫ b) ≫ f' := by
      show Work.Cohomology.relMVτ₂V U V A ≫ Work.Cohomology.smallInToSingA U V V = _
      rw [Work.Cohomology.HMV.relMVτ₂V_eq, Category.assoc]
      exact Work.Cohomology.HMV.subInclChain_V_natural A U V
    exact isIso_cokernelDesc_iso_square f f' g (a ≫ b) hg hg' hw
      (Work.Cohomology.HMV.etaV A U V) (Work.Cohomology.HMV.etaV_comp A U V)
  · -- the overlap piece
    let f := Work.Cohomology.subInclChain U V
      (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)
    let f' := Work.Cohomology.inclChains (TopCat.of ↥(U ∩ V))
      ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)
    let g := SSet.chainComplexMap
      (Work.Cohomology.smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
    let a := SSet.chainComplexMap
      (Work.Cohomology.smallInLift U V (U ∩ V ∩ A)) (ModuleCat.of ℤ ℤ)
    let b := SSet.chainComplexMap
      (TopCat.toSSet.map (Work.Cohomology.interSubHomeo X A U V).hom) (ModuleCat.of ℤ ℤ)
    have ha : IsIso a := by
      haveI : IsIso (Work.Cohomology.smallInLift U V (U ∩ V ∩ A)) :=
        Work.Cohomology.HMV.isIso_smallInLift_of_le U V (U ∩ V ∩ A)
          (fun x hx => hx.1.1)
      exact Functor.map_isIso _ _
    have hb : IsIso b := by
      haveI : IsIso (TopCat.toSSet.map (Work.Cohomology.interSubHomeo X A U V).hom) :=
        Functor.map_isIso _ _
      exact Functor.map_isIso _ _
    have hg : IsIso g := by
      haveI : IsIso (Work.Cohomology.smallInLift U V (U ∩ V)) :=
        Work.Cohomology.HMV.isIso_smallInLift_of_le U V (U ∩ V)
          (Set.inter_subset_left : U ∩ V ⊆ U)
      exact Functor.map_isIso _ _
    have hg' : IsIso (a ≫ b) := @IsIso.comp_isIso _ _ _ _ _ a b ha hb
    have hw : f ≫ g = (a ≫ b) ≫ f' := by
      show Work.Cohomology.subInclChain U V
            (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)
          ≫ SSet.chainComplexMap (Work.Cohomology.smallInLift U V (U ∩ V))
              (ModuleCat.of ℤ ℤ) = _
      rw [Category.assoc]
      exact Work.Cohomology.subInclChain_natural A U V
    exact isIso_cokernelDesc_iso_square f f' g (a ≫ b) hg hg' hw
      (Work.Cohomology.relMVUVPhi X A U V) (Work.Cohomology.relMVUVPhi_comp X A U V)

end Work.Cohomology
