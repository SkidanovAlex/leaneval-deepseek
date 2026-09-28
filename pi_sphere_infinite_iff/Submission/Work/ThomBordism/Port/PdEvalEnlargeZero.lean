-- Copied verbatim from `Submission.Work.Cohomology.pd_evalEnlarge_zero`, with imports re-routed to the
-- clash-free chain (`Work.Thom.Relocate.*` / the local copies in this directory), exactly as
-- `Submission/Work/Thom/README.md` ADDENDUM 16 did for the Thom area: the workspace contains
-- two *identical* duplicate modules `Work.Cohomology.Crux.ovlRestrictionSurjective` and
-- `Work.Cohomology.Crux.vkCruxRestr`, so a module importing one cannot be combined with a
-- module importing the other.  The `Work.ThomBordism` chapter imports
-- `ovlRestrictionSurjective` (via `Interface.lean`), hence these copies.  All declarations
-- keep their original names and proofs.
import Mathlib
import Submission.Work.Cohomology.pd_good
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.exists_relComplexMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The pair map is functorial in the pair up to an ambient identity.**

`relComplexMap` of `(A', A)` along `𝟙 X` composed with the restriction to `Z` along `ι` equals the
restriction followed by `relComplexMap` of `(C', C)` along `𝟙 Z`, whenever `A' ⊆ A`, `C' ⊆ C`,
`ι '' C ⊆ A` and `ι '' C' ⊆ A'`.

This is a restatement of `capRel_relComplexMap_comp` (twice) and `capRel_relComplexMap_congr`. -/
theorem relComplexMap_id_map_aux {X Z : TopCat} (ι : Z ⟶ X) {A A' : Set X} {C C' : Set Z}
    (hA : A' ⊆ A) (hC : C' ⊆ C) (hι : ∀ x ∈ C, ι x ∈ A) (hι' : ∀ x ∈ C', ι x ∈ A') :
    relComplexMap ℤ A' A (𝟙 X) (fun x hx => hA hx) ≫ relComplexMap ℤ C' A' ι hι'
      = relComplexMap ℤ C A ι hι ≫ relComplexMap ℤ C' C (𝟙 Z) (fun x hx => hC hx) := by
  rw [← capRel_relComplexMap_comp (R := ℤ) (X₀ := Z) (X₁ := X) (X₂ := X)
    C' A' A ι (𝟙 X) hι' (fun x hx => hA hx)]
  rw [← capRel_relComplexMap_comp (R := ℤ) (X₀ := Z) (X₁ := Z) (X₂ := X)
    C' C A (𝟙 Z) ι (fun x hx => hC hx) hι]
  exact capRel_relComplexMap_congr (R := ℤ) (A₁ := C') (A₂ := A)
    (by simp) (fun x hx => by simpa using hι x (hC hx)) (fun x hx => by simpa using hι x (hC hx))

/-- **Naturality of the enlargement of the excluded set with respect to the restriction to a
subspace.**  For `I ⊆ W` and `K ⊆ K'`, the square

```
C^*(W, W∖K)  --ρ-->  C^*(I, I∖K)
     |enlarge W          |enlarge I
     v                   v
C^*(W, W∖K') --ρ'->  C^*(I, I∖K')
```

commutes, where `ρ`, `ρ'` are the restriction maps of pairs along `I ⊆ W`. -/
theorem pdRelComplexEnlarge_id_map {M : TopCat} (W I : Set M) (hI : I ⊆ W)
    {K K' : Set M} (h : K ⊆ K') :
    pdRelComplexEnlarge W h ≫ relComplexMap ℤ (X₁ := TopCat.of I) (X₂ := TopCat.of W)
        (pdRelSub I K') (pdRelSub W K') (pdIncl W I hI) (fun x hx => hx)
      = relComplexMap ℤ (X₁ := TopCat.of I) (X₂ := TopCat.of W)
          (pdRelSub I K) (pdRelSub W K) (pdIncl W I hI) (fun x hx => hx)
        ≫ pdRelComplexEnlarge I h := by
  rw [pdRelComplexEnlarge, pdRelComplexEnlarge]
  exact relComplexMap_id_map_aux (X := TopCat.of W) (Z := TopCat.of I) (ι := pdIncl W I hI)
    (A := pdRelSub W K) (A' := pdRelSub W K') (C := pdRelSub I K) (C' := pdRelSub I K')
    (pdRelSub_mono h) (pdRelSub_mono h) (fun x hx => hx) (fun x hx => hx)

theorem pd_evalEnlarge_zero {M : TopCat} [T2Space M] {U V : Set M} (hU : IsOpen U)
    (hV : IsOpen V) {k : ℕ} {K₁ K₂ L'' : Set M}
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
    (hKI : K₁ ∩ K₂ ⊆ L'') (hL''I : L'' ⊆ U ∩ V) (hL''c : IsCompact L'')
    (y : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).homology (k+1))
    (hy : (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∩ V : Set M) (K := K₁ ∩ K₂) (K' := L'') hKI) (k+1))
            ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
              (Work.Cohomology.pdRelSub (U ∩ V : Set M) (K₁ ∩ K₂)) (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))
              (Work.Cohomology.pdIncl (U ∪ V : Set M) (U ∩ V : Set M)
                (Set.inter_subset_left.trans Set.subset_union_left)) (fun x hx => hx)) (k+1)) y) = 0) :
    (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M) (K := K₁ ∩ K₂) (K' := L'') hKI) (k+1)) y = 0 := by
  have hsq := pdRelComplexEnlarge_id_map (M := M) (U ∪ V : Set M) (U ∩ V : Set M)
      (Set.inter_subset_left.trans Set.subset_union_left) (K := (K₁ ∩ K₂)) (K' := L'') hKI
  haveI hiso : IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ
      (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∩ V : Set M) L'') (pdRelSub (U ∪ V : Set M) L'')
      (pdIncl (U ∪ V : Set M) (U ∩ V : Set M)
        (Set.inter_subset_left.trans Set.subset_union_left)) (fun x hx => hx)) (k+1)) :=
    pdCohExcision (M := M) (W := (U ∪ V : Set M)) (U := (U ∩ V : Set M))
      (Set.inter_subset_left.trans Set.subset_union_left) (hU.inter hV) (hU.union hV)
      hL''I hL''c (k+1)
  have hhom := congrArg (fun φ => HomologicalComplex.homologyMap φ (k+1)) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  have happ := congrArg (fun φ => φ.hom y) hhom
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  have hzero := happ.trans hy
  have h2 := IsIso.hom_inv_id_apply (HomologicalComplex.homologyMap (relComplexMap ℤ
      (X₁ := TopCat.of (U ∩ V : Set M)) (X₂ := TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∩ V : Set M) L'') (pdRelSub (U ∪ V : Set M) L'')
      (pdIncl (U ∪ V : Set M) (U ∩ V : Set M)
        (Set.inter_subset_left.trans Set.subset_union_left)) (fun x hx => hx)) (k+1))
      ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) (K := (K₁ ∩ K₂)) (K' := L'') hKI) (k+1)) y)
  rw [hzero] at h2
  simpa using h2.symm

end

end Work.Cohomology
