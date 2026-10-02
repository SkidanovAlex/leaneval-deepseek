import Mathlib
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.relCohMV_shortExact
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.homology_biprod_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative Mayer–Vietoris long exact sequence in cohomology

The relative cohomological Mayer–Vietoris short exact sequence of cochain complexes
(`Submission/Work/Cohomology/relCohMV_shortExact.lean`)

`0 ⟶ C^*(X,A) --relCohMVF--> C^*(U,U∩A) ⊞ C^*(V,V∩A) --relCohMVG--> C^*(U∩V,U∩V∩A) ⟶ 0`

gives, for every `n`, the long exact sequence

`⋯ ⟶ H^n(X,A) ⟶ H^n(U,U∩A) ⊞ H^n(V,V∩A) ⟶ H^n(U∩V,U∩V∩A) --δ--> H^{n+1}(X,A) ⟶ ⋯`

The only point that is not literally the homology sequence of `HomologySequence.lean` is that the
middle term of the short complex is the *homology of a biproduct* of cochain complexes, which is
identified with the biproduct of the homologies by `Work.Cohomology.homology_biprod_iso`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (X : TopCat) (A U V : Set X)

/-! ## The dual cochain complexes involved -/

/-- The dual of the `U`-part of the middle term, `C^*(U, U ∩ A)`. -/
abbrev relCohMVUUDual : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (relMVUU X A U V)

/-- The dual of the `V`-part of the middle term, `C^*(V, V ∩ A)`. -/
abbrev relCohMVVVDual : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (relMVVV X A U V)

/-- The dual of the first term, `C^*(U ∩ V, U ∩ V ∩ A)`. -/
abbrev relCohMVUVDual : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (relMVUV X A U V)

/-- The dual of the last term, `C^*(X, A)`. -/
abbrev relCohMVTopDual : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (relMVTopC X A U V)

/-! ## The short exact sequence of cochain complexes -/

/-- The relative cohomological Mayer–Vietoris short complex is short exact. -/
theorem relCohMVShortComplex_shortExact :
    (relCohMVShortComplex X A U V).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact (relCohMVShortComplex X A U V)
    (fun n => relCohMV_degreewise_shortExact X A U V n)

/-! ## The maps of the long exact sequence -/

/-- The chosen identification of the homology of the middle biproduct of cochain complexes with
the biproduct of the homologies. -/
noncomputable def relCohMVMidIso (n : ℕ) :
    (relCohMVUUDual X A U V ⊞ relCohMVVVDual X A U V).homology n ≅
      (relCohMVUUDual X A U V).homology n ⊞ (relCohMVVVDual X A U V).homology n :=
  (homology_biprod_iso (relCohMVUUDual X A U V) (relCohMVVVDual X A U V) n).choose

/-- The first map `H^n(X,A) ⟶ H^n(U,U∩A) ⊞ H^n(V,V∩A)` of the relative cohomological
Mayer–Vietoris sequence. -/
noncomputable def relCohMVLesF (n : ℕ) :
    (relCohMVTopDual X A U V).homology n ⟶
      (relCohMVUUDual X A U V).homology n ⊞ (relCohMVVVDual X A U V).homology n :=
  HomologicalComplex.homologyMap (relCohMVF X A U V) n ≫ (relCohMVMidIso X A U V n).hom

/-- The second map `H^n(U,U∩A) ⊞ H^n(V,V∩A) ⟶ H^n(U∩V,U∩V∩A)` of the relative cohomological
Mayer–Vietoris sequence. -/
noncomputable def relCohMVLesG (n : ℕ) :
    (relCohMVUUDual X A U V).homology n ⊞ (relCohMVVVDual X A U V).homology n ⟶
      (relCohMVUVDual X A U V).homology n :=
  (relCohMVMidIso X A U V n).inv ≫ HomologicalComplex.homologyMap (relCohMVG X A U V) n

/-- The shape relation `n`-`n+1` for the complex shape `ComplexShape.up ℕ`. -/
theorem relCohMVUpRel (n : ℕ) : (ComplexShape.up ℕ).Rel n (n + 1) :=
  ComplexShape.up_mk n (n + 1) rfl

/-- The connecting homomorphism `H^n(U∩V,U∩V∩A) ⟶ H^{n+1}(X,A)` of the relative cohomological
Mayer–Vietoris sequence. -/
noncomputable def relCohMVLesDelta (n : ℕ) :
    (relCohMVUVDual X A U V).homology n ⟶ (relCohMVTopDual X A U V).homology (n + 1) :=
  (relCohMVShortComplex_shortExact X A U V).δ n (n + 1) (relCohMVUpRel n)

/-! ## The three composites vanish -/

/-- `F n ≫ G n = 0`. -/
theorem relCohMVLesFG (n : ℕ) :
    relCohMVLesF X A U V n ≫ relCohMVLesG X A U V n = 0 := by
  rw [relCohMVLesF, relCohMVLesG]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp, relCohMV_comp, HomologicalComplex.homologyMap_zero]

/-- `G n ≫ δ n = 0`. -/
theorem relCohMVLesGδ (n : ℕ) :
    relCohMVLesG X A U V n ≫ relCohMVLesDelta X A U V n = 0 := by
  have h : HomologicalComplex.homologyMap (relCohMVG X A U V) n ≫
      relCohMVLesDelta X A U V n = 0 :=
    (relCohMVShortComplex_shortExact X A U V).comp_δ n (n + 1) (relCohMVUpRel n)
  rw [relCohMVLesG, Category.assoc, h, comp_zero]

/-- `δ n ≫ F (n+1) = 0`. -/
theorem relCohMVLesδF (n : ℕ) :
    relCohMVLesDelta X A U V n ≫ relCohMVLesF X A U V (n + 1) = 0 := by
  have h : relCohMVLesDelta X A U V n ≫
      HomologicalComplex.homologyMap (relCohMVF X A U V) (n + 1) = 0 :=
    (relCohMVShortComplex_shortExact X A U V).δ_comp n (n + 1) (relCohMVUpRel n)
  rw [relCohMVLesF, ← Category.assoc, h, zero_comp]

/-! ## Exactness -/

/-- The second short complex, `H^n(U,U∩A) ⊞ H^n(V,V∩A) ⟶ H^n(U∩V,U∩V∩A) --δ--> H^{n+1}(X,A)`. -/
noncomputable def relCohMVLesSC₃ (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (relCohMVLesG X A U V n) (relCohMVLesDelta X A U V n)
    (relCohMVLesGδ X A U V n)

/-- The first short complex, `H^n(X,A) ⟶ H^n(U,U∩A) ⊞ H^n(V,V∩A) ⟶ H^n(U∩V,U∩V∩A)`. -/
noncomputable def relCohMVLesSC₂ (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (relCohMVLesF X A U V n) (relCohMVLesG X A U V n)
    (relCohMVLesFG X A U V n)

/-- The third short complex, `H^n(U∩V,U∩V∩A) --δ--> H^{n+1}(X,A) ⟶ H^{n+1}(U,U∩A) ⊞ ⋯`. -/
noncomputable def relCohMVLesSC₁ (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (relCohMVLesDelta X A U V n) (relCohMVLesF X A U V (n + 1))
    (relCohMVLesδF X A U V n)

/-- The corresponding short complex of the homology sequence, second term. -/
noncomputable def relCohMVHomSC₂ (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (relCohMVF X A U V) n)
    (HomologicalComplex.homologyMap (relCohMVG X A U V) n)
    (by rw [← HomologicalComplex.homologyMap_comp, relCohMV_comp,
        HomologicalComplex.homologyMap_zero])

/-- The corresponding short complex of the homology sequence, third term. -/
noncomputable def relCohMVHomSC₃ (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (relCohMVG X A U V) n)
    (relCohMVLesDelta X A U V n)
    ((relCohMVShortComplex_shortExact X A U V).comp_δ n (n + 1) (relCohMVUpRel n))

/-- The corresponding short complex of the homology sequence, first term. -/
noncomputable def relCohMVHomSC₁ (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (relCohMVLesDelta X A U V n)
    (HomologicalComplex.homologyMap (relCohMVF X A U V) (n + 1))
    ((relCohMVShortComplex_shortExact X A U V).δ_comp n (n + 1) (relCohMVUpRel n))

/-- The comparison isomorphism at the second term. -/
noncomputable def relCohMVLesIso₂ (n : ℕ) :
    relCohMVHomSC₂ X A U V n ≅ relCohMVLesSC₂ X A U V n :=
  ShortComplex.isoMk (Iso.refl _) (relCohMVMidIso X A U V n) (Iso.refl _)
    (by
      show (Iso.refl _).hom ≫ relCohMVLesF X A U V n =
        HomologicalComplex.homologyMap (relCohMVF X A U V) n ≫ (relCohMVMidIso X A U V n).hom
      rw [Iso.refl_hom, Category.id_comp]
      rfl)
    (by
      show (relCohMVMidIso X A U V n).hom ≫ relCohMVLesG X A U V n =
        HomologicalComplex.homologyMap (relCohMVG X A U V) n ≫ (Iso.refl _).hom
      rw [Iso.refl_hom, Category.comp_id, relCohMVLesG, Iso.hom_inv_id_assoc])

/-- The comparison isomorphism at the third term. -/
noncomputable def relCohMVLesIso₃ (n : ℕ) :
    relCohMVHomSC₃ X A U V n ≅ relCohMVLesSC₃ X A U V n :=
  ShortComplex.isoMk (relCohMVMidIso X A U V n) (Iso.refl _) (Iso.refl _)
    (by
      show (relCohMVMidIso X A U V n).hom ≫ relCohMVLesG X A U V n =
        HomologicalComplex.homologyMap (relCohMVG X A U V) n ≫ (Iso.refl _).hom
      rw [Iso.refl_hom, Category.comp_id, relCohMVLesG, Iso.hom_inv_id_assoc])
    (by
      show (Iso.refl _).hom ≫ relCohMVLesDelta X A U V n =
        relCohMVLesDelta X A U V n ≫ (Iso.refl _).hom
      rw [Iso.refl_hom, Category.id_comp, Iso.refl_hom, Category.comp_id])

/-- The comparison isomorphism at the first term. -/
noncomputable def relCohMVLesIso₁ (n : ℕ) :
    relCohMVHomSC₁ X A U V n ≅ relCohMVLesSC₁ X A U V n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (relCohMVMidIso X A U V (n + 1))
    (by
      show (Iso.refl _).hom ≫ relCohMVLesDelta X A U V n =
        relCohMVLesDelta X A U V n ≫ (Iso.refl _).hom
      rw [Iso.refl_hom, Category.id_comp, Iso.refl_hom, Category.comp_id])
    (by
      show (Iso.refl _).hom ≫ relCohMVLesF X A U V (n + 1) =
        HomologicalComplex.homologyMap (relCohMVF X A U V) (n + 1) ≫
          (relCohMVMidIso X A U V (n + 1)).hom
      rw [Iso.refl_hom, Category.id_comp]
      rfl)

/-- Exactness at the second term `H^n(U,U∩A) ⊞ H^n(V,V∩A)`. -/
theorem relCohMVLes_exact₂ (n : ℕ) : (relCohMVLesSC₂ X A U V n).Exact :=
  ShortComplex.exact_of_iso (relCohMVLesIso₂ X A U V n)
    ((relCohMVShortComplex_shortExact X A U V).homology_exact₂ n)

/-- Exactness at the third term `H^n(U∩V,U∩V∩A)`. -/
theorem relCohMVLes_exact₃ (n : ℕ) : (relCohMVLesSC₃ X A U V n).Exact :=
  ShortComplex.exact_of_iso (relCohMVLesIso₃ X A U V n)
    ((relCohMVShortComplex_shortExact X A U V).homology_exact₃ n (n + 1) (relCohMVUpRel n))

/-- Exactness at the first term `H^{n+1}(X,A)`. -/
theorem relCohMVLes_exact₁ (n : ℕ) : (relCohMVLesSC₁ X A U V n).Exact :=
  ShortComplex.exact_of_iso (relCohMVLesIso₁ X A U V n)
    ((relCohMVShortComplex_shortExact X A U V).homology_exact₁ n (n + 1) (relCohMVUpRel n))

/-! ## The long exact sequence -/

theorem relCohMV_les (X : TopCat) (A U V : Set X) :
    ∃ (F : ∀ n : ℕ, HomologicalComplex.homology
          (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relSmallTop U V A)) n ⟶
        CategoryTheory.Limits.biprod
          (HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
            (Work.Cohomology.relSmallChains U V U (U ∩ A) Set.inter_subset_left)) n)
          (HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
            (Work.Cohomology.relSmallChains U V V (V ∩ A) Set.inter_subset_left)) n))
      (G : ∀ n : ℕ,
        CategoryTheory.Limits.biprod
          (HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
            (Work.Cohomology.relSmallChains U V U (U ∩ A) Set.inter_subset_left)) n)
          (HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
            (Work.Cohomology.relSmallChains U V V (V ∩ A) Set.inter_subset_left)) n) ⟶
        HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
          (Work.Cohomology.relSmallChains U V (U ∩ V) (U ∩ V ∩ A) Set.inter_subset_left)) n)
      (δ : ∀ n : ℕ, HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
          (Work.Cohomology.relSmallChains U V (U ∩ V) (U ∩ V ∩ A) Set.inter_subset_left)) n ⟶
        HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
          (Work.Cohomology.relSmallTop U V A)) (n + 1))
      (hFG : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (F n) (G n) = 0)
      (hGδ : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (G n) (δ n) = 0)
      (hδF : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (δ n) (F (n + 1)) = 0),
      (∀ n : ℕ, (CategoryTheory.ShortComplex.mk (F n) (G n) (hFG n)).Exact) ∧
      (∀ n : ℕ, (CategoryTheory.ShortComplex.mk (G n) (δ n) (hGδ n)).Exact) ∧
      (∀ n : ℕ, (CategoryTheory.ShortComplex.mk (δ n) (F (n + 1)) (hδF n)).Exact) :=
  ⟨relCohMVLesF X A U V, relCohMVLesG X A U V, relCohMVLesDelta X A U V,
    relCohMVLesFG X A U V, relCohMVLesGδ X A U V, relCohMVLesδF X A U V,
    fun n => relCohMVLes_exact₂ X A U V n,
    fun n => relCohMVLes_exact₃ X A U V n,
    fun n => relCohMVLes_exact₁ X A U V n⟩

end

end Work.Cohomology
