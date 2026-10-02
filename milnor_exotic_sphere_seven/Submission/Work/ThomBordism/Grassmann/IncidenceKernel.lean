import Mathlib
import Submission.Work.ThomBordism.Grassmann.IncidenceMVIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The Mayer–Vietoris extraction of the incidence step: the composite isomorphism

This module completes the extraction described in `INCIDENCE_FIBRE_NOTES.md` §6: if the
restrictions `H^i(U) → H^i(U ∩ V)` and `H^{i-1}(U) → H^{i-1}(U ∩ V)` are bijections (so that the
first map of the Mayer–Vietoris sequence is injective with image the kernel of the second) and the
`V`-restriction `H^i(V) → H^i(U ∩ V)` is a bijection, then

`H^i(X) ≅ H^i(C^{U,V}) ≅ H^i(U)`.

The two ingredients are the element-level biproduct decomposition
(`Work.Cohomology.mv_homology_biprod_decomp_elem`) and the identification of the components of the
Mayer–Vietoris map with the honest restrictions
(`Work.Cohomology.mvCochainG_apply_inl` / `mvCochainG_apply_inr`).

The composite is used *directly* (rather than passing through the subtype `ker g` of the biproduct
cohomology): this keeps the `ℤ`-module structures of the two sides in agreement, which is what the
`LinearEquiv` packaging needs.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

variable {X : TopCat}

/-- The `U`-restriction of a cover, `H^i(U) ⟶ H^i(U ∩ V)`. -/
abbrev restU (U V : Set ↑X) (i : ℕ) : (cochainU U V).homology i →ₗ[ℤ] (cochainUV U V).homology i :=
  (singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (inclUVU U V) i).hom

/-- The `V`-restriction of a cover, `H^i(V) ⟶ H^i(U ∩ V)`. -/
abbrev restV (U V : Set ↑X) (i : ℕ) : (cochainV U V).homology i →ₗ[ℤ] (cochainUV U V).homology i :=
  (singularCohomologyMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V) (inclUVV U V) i).hom

/-- **The composite `H^i(C^{U,V}) → H^i(U)`**: the first Mayer–Vietoris map followed by the
projection to the `U`-summand. -/
noncomputable def mvExtract (U V : Set ↑X) (i : ℕ) :
    (dualComplex ℤ (smallChains U V)).homology i →ₗ[ℤ] (cochainU U V).homology i :=
  ((HomologicalComplex.homologyMap
      (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V) i).hom).comp
    ((HomologicalComplex.homologyMap (mvCochainF U V) i).hom)

/-- **The extraction is bijective.** -/
theorem mvExtract_bijective (U V : Set ↑X) (i : ℕ) (hi : 1 ≤ i)
    (hU : Function.Bijective (restU U V i))
    (hU' : Function.Bijective (restU U V (i - 1)))
    (hV : Function.Bijective (restV U V i)) :
    Function.Bijective (mvExtract U V i) := by
  obtain ⟨hinjF, hrangeF⟩ := mvCochainF_injective_range U V i hi hU hU'
  set g := (HomologicalComplex.homologyMap (mvCochainG U V) i).hom with hg
  set f := (HomologicalComplex.homologyMap (mvCochainF U V) i).hom with hf
  set F := (HomologicalComplex.homologyMap
      (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V) i).hom with hF
  set I₁ := (HomologicalComplex.homologyMap
      (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) i).hom with hI₁
  set I₂ := (HomologicalComplex.homologyMap
      (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) i).hom with hI₂
  set S := (HomologicalComplex.homologyMap
      (biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V) i).hom with hS
  have hdecomp : ∀ z : (cochainU U V ⊞ cochainV U V).homology i,
      z = I₁ (F z) + I₂ (S z) := by
    intro z
    have h := mv_homology_biprod_decomp_elem U V i z
    rw [hF, hI₁, hI₂, hS]
    exact h
  have hfstI₁ : ∀ a : (cochainU U V).homology i, F (I₁ a) = a := by
    intro a
    have h := mv_homology_biprod_fst_inl U V i a
    rw [hF, hI₁]; exact h
  have hfstI₂ : ∀ b : (cochainV U V).homology i, F (I₂ b) = 0 := by
    intro b
    have h := mv_homology_biprod_fst_inr U V i b
    rw [hF, hI₂]; exact h
  have hgI₁ : ∀ a : (cochainU U V).homology i, g (I₁ a) = restU U V i a := by
    intro a
    have h := mvCochainG_apply_inl U V i a
    rw [hg, hI₁]; exact h
  have hgI₂ : ∀ b : (cochainV U V).homology i, g (I₂ b) = restV U V i b := by
    intro b
    have h := mvCochainG_apply_inr U V i b
    rw [hg, hI₂]; exact h
  have hmv : ∀ x, mvExtract U V i x = F (f x) := fun x => rfl
  constructor
  · intro x y hxy
    have hxy' : F (f x) = F (f y) := hxy
    have hm : f (x - y) = f x - f y := map_sub f x y
    have hF0 : F (f (x - y)) = 0 := by
      rw [hm, map_sub, hxy', sub_self]
    have hin : f (x - y) ∈ g.ker := by
      rw [← hrangeF]; exact ⟨x - y, rfl⟩
    have hg0 : g (f (x - y)) = 0 := hin
    have hdec := hdecomp (f (x - y))
    have hg0' : g (I₁ (F (f (x - y))) + I₂ (S (f (x - y)))) = 0 := by rw [← hdec]; exact hg0
    rw [map_add, hgI₁, hgI₂, hF0, map_zero, zero_add] at hg0'
    have hS0 : S (f (x - y)) = 0 := hV.1 (by simpa using hg0')
    have hfz : f (x - y) = 0 := by rw [hdec, hF0, hS0, map_zero, map_zero, add_zero]
    exact sub_eq_zero.mp (hinjF (by rw [hfz, map_zero]))
  · intro a
    obtain ⟨b, hb⟩ := hV.2 (restU U V i a)
    have hy : I₁ a - I₂ b ∈ g.ker := by
      rw [LinearMap.mem_ker, map_sub, hgI₁, hgI₂, hb, sub_self]
    obtain ⟨x, hx⟩ := (show (I₁ a - I₂ b) ∈ f.range from by rw [hrangeF]; exact hy)
    refine ⟨x, ?_⟩
    rw [hmv, hx]
    show F (I₁ a - I₂ b) = a
    rw [map_sub, hfstI₁, hfstI₂, sub_zero]

/-- **The Mayer–Vietoris extraction of the incidence step**: `H^i(C^{U,V}) ≅ H^i(U)`. -/
noncomputable def mvExtractEquiv (U V : Set ↑X) (i : ℕ) (hi : 1 ≤ i)
    (hU : Function.Bijective (restU U V i))
    (hU' : Function.Bijective (restU U V (i - 1)))
    (hV : Function.Bijective (restV U V i)) :
    (dualComplex ℤ (smallChains U V)).homology i ≃ₗ[ℤ] (cochainU U V).homology i :=
  LinearEquiv.ofBijective (mvExtract U V i) (mvExtract_bijective U V i hi hU hU' hV)

end

end Work.ThomBordism.Grassmann
