import Mathlib
import Submission.Work.Cohomology.MVCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# Naturality of the cohomological Mayer–Vietoris maps

The cohomological Mayer–Vietoris short exact sequence of `Submission/Work/Cohomology/MVCohomology.lean`

`0 ⟶ C^*(C^{U,V}) --mvCochainF--> C^*(U) ⊞ C^*(V) --mvCochainG--> C^*(U ∩ V) ⟶ 0`

has terms `cochainU U V = singularCochainComplex ℤ (TopCat.of U)`, etc.  The purpose of this module
is to record that its maps are the **honest restriction maps**: the induced map on homology of the
`U`-component of `mvCochainG` is the map `H^i(U) ⟶ H^i(U ∩ V)` induced by the inclusion of spaces.

This is what makes the Mayer–Vietoris long exact sequence usable for the incidence step: its middle
map is `(rest_U, -rest_V)`, so if both restrictions are isomorphisms then
`H^i(X) ≅ ker (rest_U, -rest_V) ≅ H^i(U)`.

Everything here is (definitionally) naturality of the dual of the chain inclusion
`chainInclU U V = SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) ℤ`
(`Submission/Work/Cohomology/mvCochainDefs.lean`) and of `mvCochainG = biprod.desc` of the two dual
maps; the two lemmas below are the identities `biprod.inl_desc` and `biprod.inr_desc` together with
`rfl`-identifications with `Work.Cohomology.singularCohomologyMap`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- **The `U`-component of `mvCochainG` is the dual of the chain inclusion.** -/
theorem mvCochainG_inl_eq (U V : Set ↑X) :
    (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) ≫ mvCochainG U V
      = dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of U)) (chainInclU U V) := by
  rw [mvCochainG]
  exact biprod.inl_desc _ _

/-- **The `V`-component of `mvCochainG` is the dual of the chain inclusion.** -/
theorem mvCochainG_inr_eq (U V : Set ↑X) :
    (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) ≫ mvCochainG U V
      = dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of V)) (chainInclV U V) := by
  rw [mvCochainG]
  exact biprod.inr_desc
    (dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
      (singularChains ℤ (TopCat.of U)) (chainInclU U V))
    (dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
      (singularChains ℤ (TopCat.of V)) (chainInclV U V))

/-- **The induced map on homology of the `U`-component of the Mayer–Vietoris map is the honest
restriction `H^i(U) ⟶ H^i(U ∩ V)`.** -/
theorem mvCochainG_inl_homology_eq (U V : Set ↑X) (i : ℕ) :
    HomologicalComplex.homologyMap
        (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) i
      ≫ HomologicalComplex.homologyMap (mvCochainG U V) i
    = singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (inclUVU U V) i := by
  rw [← HomologicalComplex.homologyMap_comp, mvCochainG_inl_eq]
  rfl

/-- **The induced map on homology of the `V`-component of the Mayer–Vietoris map is the honest
restriction `H^i(V) ⟶ H^i(U ∩ V)` (up to the sign convention of `mvCochainG`).** -/
theorem mvCochainG_inr_homology_eq (U V : Set ↑X) (i : ℕ) :
    HomologicalComplex.homologyMap
        (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) i
      ≫ HomologicalComplex.homologyMap (mvCochainG U V) i
    = singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V) (inclUVV U V) i := by
  rw [← HomologicalComplex.homologyMap_comp, mvCochainG_inr_eq]
  rfl

/-- **The element-level decomposition of the homology of a biproduct**: an element of
`H^k(C ⊞ D)` is the sum of the images of its two components.  This is `coh_homologyMap_total`
applied to the element; it is the form in which the Mayer–Vietoris extraction needs it (the
projections of an element of a biproduct of `ModuleCat`s do not exist syntactically, only the maps
induced by `biprod.fst`/`biprod.snd`). -/
theorem mv_homology_biprod_decomp_elem (U V : Set ↑X) (k : ℕ)
    (z : (cochainU U V ⊞ cochainV U V).homology k) :
    z = HomologicalComplex.homologyMap
          (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) k
            (HomologicalComplex.homologyMap
              (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V) k z) +
        HomologicalComplex.homologyMap
          (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) k
            (HomologicalComplex.homologyMap
              (biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V) k z) := by
  have h := congrArg (fun f => f z) (coh_homologyMap_total (cochainU U V) (cochainV U V) k)
  simpa [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
    LinearMap.id_apply] using h.symm

/-- The dual form: the components of a sum of an `inl`- and an `inr`-component. -/
theorem mv_homology_biprod_fst_inl (U V : Set ↑X) (k : ℕ)
    (a : (cochainU U V).homology k) :
    HomologicalComplex.homologyMap
        (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V) k
      (HomologicalComplex.homologyMap
        (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) k a) = a := by
  have h := congrArg (fun f => f a) (HomologicalComplex.homologyMap_comp
    (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V)
    (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V) k)
  rw [biprod.inl_fst] at h
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] using h.symm

/-- The dual form, second component. -/
theorem mv_homology_biprod_snd_inr (U V : Set ↑X) (k : ℕ)
    (b : (cochainV U V).homology k) :
    HomologicalComplex.homologyMap
        (biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V) k
      (HomologicalComplex.homologyMap
        (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) k b) = b := by
  have h := congrArg (fun f => f b) (HomologicalComplex.homologyMap_comp
    (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V)
    (biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V) k)
  rw [biprod.inr_snd] at h
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] using h.symm


/-- The mixed component identity: the `fst`-component of an `inr`-component vanishes. -/
theorem mv_homology_biprod_fst_inr (U V : Set ↑X) (k : ℕ)
    (b : (cochainV U V).homology k) :
    HomologicalComplex.homologyMap
        (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V) k
      (HomologicalComplex.homologyMap
        (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) k b) = 0 := by
  have h := congrArg (fun f => f b) (HomologicalComplex.homologyMap_comp
    (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V)
    (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V) k)
  rw [biprod.inr_fst] at h
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] using h.symm

/-- The mixed component identity: the `snd`-component of an `inl`-component vanishes. -/
theorem mv_homology_biprod_snd_inl (U V : Set ↑X) (k : ℕ)
    (a : (cochainU U V).homology k) :
    HomologicalComplex.homologyMap
        (biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V) k
      (HomologicalComplex.homologyMap
        (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) k a) = 0 := by
  have h := congrArg (fun f => f a) (HomologicalComplex.homologyMap_comp
    (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V)
    (biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V) k)
  rw [biprod.inl_snd] at h
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] using h.symm


end

end Work.Cohomology
