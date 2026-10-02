import Mathlib
import Submission.Work.ThomBordism.Grassmann.IncidenceMVNat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The Mayer–Vietoris extraction of the incidence step

Using the Mayer–Vietoris short exact sequence (`Work.Cohomology.mvCochainSES`), the identification of
its middle map with the honest restrictions (`IncidenceMVNat.lean`) and the element-level
biproduct decomposition, we extract: **if the two restrictions `H^i(U) → H^i(U∩V)` and
`H^i(V) → H^i(U∩V)` are bijections in degrees `i` and `i-1`, then `H^i(X) ≅ H^i(U)`.**

The proof is the standard five-term argument:
* the `U`-component of `g = homologyMap (mvCochainG U V) i` is a bijection, so `g` is surjective in
  degrees `i` and `i - 1`;
* hence the connecting map `δ_{i-1}` vanishes (exactness at `H^{i-1}(U∩V)`), so
  `homologyMap (mvCochainF U V) i` is injective, with image `ker g` (exactness at `H^i(C₂)`);
* `ker g ≅ H^i(U)` by the explicit map `x ↦ fst x` (using that both components of `g` are
  isomorphisms), and `H^i(C₁) ≅ H^i(X)` by `cohSmallIso`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

/-- **The `U`-component of the Mayer–Vietoris map is a bijection, hence so is the whole map
(projected onto the `U`-summand).**  In particular `g` is surjective. -/
theorem mvCochainG_surjective_of_restriction {X : TopCat} (U V : Set ↑X) (i : ℕ)
    (hU : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U)
      (inclUVU U V) i).hom)) :
    Function.Surjective ((HomologicalComplex.homologyMap (mvCochainG U V) i).hom) := by
  have hnat := mvCochainG_inl_homology_eq U V i
  have hcomp : ((HomologicalComplex.homologyMap (mvCochainG U V) i).hom).comp
      ((HomologicalComplex.homologyMap
        (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) i).hom)
      = (singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (inclUVU U V) i).hom := by
    have h := congrArg (fun f : (cochainU U V).homology i ⟶
      (cochainUV U V).homology i => ModuleCat.Hom.hom f) hnat
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  refine Function.Surjective.of_comp
    (f := (HomologicalComplex.homologyMap (mvCochainG U V) i).hom)
    (g := (HomologicalComplex.homologyMap
      (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) i).hom) ?_
  rw [← LinearMap.coe_comp, hcomp]
  exact hU.2

/-- **The two components of the Mayer–Vietoris map on homology**, evaluated: for
`a ∈ H^i(U)` and `b ∈ H^i(V)`, `g (inl a) = rest_U a` and `g (inr b) = rest_V b`. -/
theorem mvCochainG_apply_inl {X : TopCat} (U V : Set ↑X) (i : ℕ)
    (a : (cochainU U V).homology i) :
    (HomologicalComplex.homologyMap (mvCochainG U V) i).hom
        ((HomologicalComplex.homologyMap
          (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) i).hom a)
      = (singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (inclUVU U V) i).hom a := by
  have hnat := mvCochainG_inl_homology_eq U V i
  have h := congrArg (fun f : (cochainU U V).homology i ⟶ (cochainUV U V).homology i =>
    ModuleCat.Hom.hom f a) hnat
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

theorem mvCochainG_apply_inr {X : TopCat} (U V : Set ↑X) (i : ℕ)
    (b : (cochainV U V).homology i) :
    (HomologicalComplex.homologyMap (mvCochainG U V) i).hom
        ((HomologicalComplex.homologyMap
          (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) i).hom b)
      = (singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V) (inclUVV U V) i).hom b := by
  have hnat := mvCochainG_inr_homology_eq U V i
  have h := congrArg (fun f : (cochainV U V).homology i ⟶ (cochainUV U V).homology i =>
    ModuleCat.Hom.hom f b) hnat
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The five-term extraction at the level of the Mayer–Vietoris sequence**: if the restrictions
`H^i(U) → H^i(U∩V)` and `H^{i-1}(U) → H^{i-1}(U∩V)` are bijections, then the first map of the MV
sequence is injective in degree `i`, with image the kernel of the second map. -/
theorem mvCochainF_injective_range {X : TopCat} (U V : Set ↑X) (i : ℕ) (hi : 1 ≤ i)
    (hU : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U)
      (inclUVU U V) i).hom))
    (hU' : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U)
      (inclUVU U V) (i - 1)).hom)) :
    Function.Injective ((HomologicalComplex.homologyMap (mvCochainF U V) i).hom) ∧
      ((HomologicalComplex.homologyMap (mvCochainF U V) i).hom).range
        = ((HomologicalComplex.homologyMap (mvCochainG U V) i).hom).ker := by
  have hS := mvCochainSES U V
  have hij : (ComplexShape.up ℕ).Rel (i - 1) i := by
    rw [ComplexShape.up_Rel]; omega
  -- the connecting map vanishes, because the second map is surjective in degree `i - 1`
  have hδ : (hS.δ (i - 1) i hij).hom = 0 := by
    have hex := ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₃ (i - 1) i hij)
    have hsurj := mvCochainG_surjective_of_restriction U V (i - 1) hU'
    have htop : (hS.δ (i - 1) i hij).hom.ker = ⊤ := by
      rw [← hex, LinearMap.range_eq_top]
      exact hsurj
    exact LinearMap.ker_eq_top.mp htop
  -- hence the first map is injective ...
  have hinj : Function.Injective ((HomologicalComplex.homologyMap (mvCochainF U V) i).hom) := by
    have hex := ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₁ (i - 1) i hij)
    have hbot : ((HomologicalComplex.homologyMap (mvCochainF U V) i).hom).ker = ⊥ := by
      rw [← hex, hδ, LinearMap.range_zero]
    exact LinearMap.ker_eq_bot.mp hbot
  -- ... and its image is the kernel of the second map
  have hrange : ((HomologicalComplex.homologyMap (mvCochainF U V) i).hom).range
      = ((HomologicalComplex.homologyMap (mvCochainG U V) i).hom).ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ i)
  exact ⟨hinj, hrange⟩




end

end Work.ThomBordism.Grassmann
