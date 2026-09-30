import Mathlib
import Submission.Work.Serre.mvDeltaAuxDefs

/-!
# Naturality of the honest cup with a relative cocycle

For a space `X`, subsets `A, U, V ⊆ X` and a relative cocycle `t ∈ C^{n₀}(X,A;ℚ)`, the honest cup
chain map `ψ ↦ ψ ⌣ t` (`Work.Serre.cupTop` and its restrictions `cupTopU`, `cupTopV`, `cupTopUV`
to the pieces of the cover) commutes with the restriction maps `mvFU`, `mvGWU`, `mvGWV` of the
Mayer–Vietoris cover:

* `mvFU X ∅ U ≫ cupTopU = cupTop ≫ shMap (mvFU X A U) n₀` (and the same for `V`);
* `mvGWU X ∅ U V ≫ cupTopUV = cupTopU ≫ shMap (mvGWU X A U V) n₀` (and the same for `V`).

These are the two squares of the "honest cup morphism of the cover"
(`Work.Serre.cupSES` in `Submission/Work/Serre/mvDeltaAuxAssembly.lean`).  Everything is a
formal consequence of the naturality of the mixed Alexander–Whitney product
(`Work.Serre.MVShift.relMapLM_mixedRelStar`) along a map of pairs, the only bookkeeping being the
identification of the empty set with `interAU ∅ U` (definitional) and of the two spellings of the
restriction of `t` to the overlap (through `U` or through `V`, from `mvFU_comp_mvGWU`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

open Work.Cohomology

/-! ## §1. The component of the honest cup -/

/-- The degree-`k` component of `cupRelLM` is the mixed cup product. -/
theorem cupRelLM_apply (Y : TopCat) (B : Set Y) (n₀ : ℕ)
    (t : ↥(relKern ℚ Y B n₀)) (k : ℕ) (x : ↥(relKern ℚ Y (∅ : Set Y) k)) :
    cupRelLM Y B n₀ t k x
      = (mixedRelStar ℚ Y B k n₀) (show Cochain ℚ (TopCat.toSSet.obj Y) k from x.1) t := rfl

/-! ## §2. Naturality of the mixed cup along a map of pairs -/

/-- Naturality of the mixed cup product along a map of pairs, at the level of the linear maps
`cupRelLM`. -/
theorem cupRelLM_comp_relMapLM {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h₂ : ∀ x ∈ A₁, f x ∈ A₂) (k n₀ : ℕ)
    (t : ↥(relKern ℚ X₂ A₂ n₀)) :
    (cupRelLM X₁ A₁ n₀ (relMapLM ℚ A₁ A₂ f h₂ n₀ t) k).comp
        (relMapLM ℚ (∅ : Set X₁) (∅ : Set X₂) f (fun x hx => hx) k)
      = (relMapLM ℚ A₁ A₂ f h₂ (k + n₀)).comp (cupRelLM X₂ A₂ n₀ t k) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [cupRelLM_apply, cupRelLM_apply]
  rw [relMapLM_coe]
  exact congrArg Subtype.val (MVShift.relMapLM_mixedRelStar A₁ A₂ f h₂ k n₀
    (show Cochain ℚ (TopCat.toSSet.obj X₂) k from x.1) t).symm

/-! ## §3. Chain-level naturality of the honest cup -/

/-- **Chain-level naturality of the honest cup with a relative cocycle** along a map of pairs:
cupping with the pullback of `t` and then restricting is the same as restricting and then cupping
with `t`. -/
theorem relComplexMap_cupRelChain {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h₂ : ∀ x ∈ A₁, f x ∈ A₂) (n₀ : ℕ)
    (t : ↥(relKern ℚ X₂ A₂ n₀)) (ht : relDiffLM ℚ X₂ A₂ n₀ t = 0) :
    relComplexMap ℚ (∅ : Set X₁) (∅ : Set X₂) f (fun x hx => hx) ≫
        cupRelChain X₁ A₁ n₀ (relMapLM ℚ A₁ A₂ f h₂ n₀ t)
          (relDiffLM_relMapLM ℚ A₁ A₂ f h₂ t ht)
      = cupRelChain X₂ A₂ n₀ t ht ≫ MVShift.shMap (relComplexMap ℚ A₁ A₂ f h₂) n₀ := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, MVShift.shMap_f, cupRelChain_f,
    cupRelChain_f, relComplexMap_f, relComplexMap_f]
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
  exact congrArg ModuleCat.ofHom (cupRelLM_comp_relMapLM A₁ A₂ f h₂ k n₀ t)

/-! ## §4. The empty-set normalisations -/

/-- `mvFU` computed with the empty subset is `relComplexMap` for the empty subsets. -/
theorem mvFU_empty (X : TopCat) (U : Set X) :
    mvFU X (∅ : Set X) U
      = relComplexMap ℚ (∅ : Set (↥U)) (∅ : Set X) (subtypeIncl X U)
          (fun x hx => hx) := rfl

theorem mvGWU_empty (X : TopCat) (U V : Set X) :
    mvGWU X (∅ : Set X) U V
      = relComplexMap ℚ (∅ : Set (↥(U ∩ V))) (∅ : Set (↥U))
          (pdIncl U (U ∩ V) Set.inter_subset_left) (fun x hx => hx) := rfl

theorem mvGWV_empty (X : TopCat) (U V : Set X) :
    mvGWV X (∅ : Set X) U V
      = relComplexMap ℚ (∅ : Set (↥(U ∩ V))) (∅ : Set (↥V))
          (pdIncl V (U ∩ V) Set.inter_subset_right) (fun x hx => hx) := rfl

/-! ## §5. The two spellings of the restriction of the cocycle to the overlap -/

/-- The iterated pullback along a composite of continuous maps. -/
theorem dualChainMap_comp_apply' {X₁ X₂ X₃ : TopCat} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (n : ℕ)
    (x : (singularCochainComplex ℚ X₃).X n) :
    ((dualChainMap ℚ X₁ X₂ f).f n) (((dualChainMap ℚ X₂ X₃ g).f n) x)
      = ((dualChainMap ℚ X₁ X₃ (f ≫ g)).f n) x := by
  rw [dualChainMap_comp]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The restriction of the cocycle `t` to the overlap, computed through `U`, agrees with the one
computed through `V`. -/
theorem cupTgtUV_eq_V (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (t : ↥(relKern ℚ X A n₀)) :
    cupTgtUV X A U V n₀ t
      = relMapLM ℚ (interAU A (U ∩ V)) (interAU A V)
          (pdIncl V (U ∩ V) Set.inter_subset_right) (interAU_incl_pdIncl_V X A U V) n₀
          (cupTgtU X A V n₀ t) := by
  have hmap : (pdIncl U (U ∩ V) Set.inter_subset_left) ≫ subtypeIncl X U
      = (pdIncl V (U ∩ V) Set.inter_subset_right) ≫ subtypeIncl X V := by
    ext x
    rfl
  apply Subtype.ext
  rw [cupTgtUV, cupTgtU, cupTgtU]
  rw [relMapLM_coe, relMapLM_coe, relMapLM_coe, relMapLM_coe]
  rw [dualChainMap_comp_apply' (pdIncl U (U ∩ V) Set.inter_subset_left) (subtypeIncl X U) n₀,
    dualChainMap_comp_apply' (pdIncl V (U ∩ V) Set.inter_subset_right) (subtypeIncl X V) n₀]
  rw [hmap]

/-! ## §6. `cupRelChain` depends on the cocycle only through the cocycle -/

theorem cupRelChain_congr {Y : TopCat} {B : Set Y} {n₀ : ℕ}
    {t t' : ↥(relKern ℚ Y B n₀)} (h : t = t')
    (ht : relDiffLM ℚ Y B n₀ t = 0) (ht' : relDiffLM ℚ Y B n₀ t' = 0) :
    cupRelChain Y B n₀ t ht = cupRelChain Y B n₀ t' ht' := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [cupRelChain_f, cupRelChain_f]
  exact congrArg ModuleCat.ofHom (congrArg (fun s => cupRelLM Y B n₀ s k) h)

/-- The chain-level naturality of the honest cup, with the pulled-back cocycle given by an
arbitrary term equal to the pullback. -/
theorem relComplexMap_cupRelChain_gen {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h₂ : ∀ x ∈ A₁, f x ∈ A₂) (n₀ : ℕ)
    (t : ↥(relKern ℚ X₂ A₂ n₀)) (ht : relDiffLM ℚ X₂ A₂ n₀ t = 0)
    (s : ↥(relKern ℚ X₁ A₁ n₀)) (hs : s = relMapLM ℚ A₁ A₂ f h₂ n₀ t)
    (hs' : relDiffLM ℚ X₁ A₁ n₀ s = 0) :
    relComplexMap ℚ (∅ : Set X₁) (∅ : Set X₂) f (fun x hx => hx) ≫
        cupRelChain X₁ A₁ n₀ s hs'
      = cupRelChain X₂ A₂ n₀ t ht ≫ MVShift.shMap (relComplexMap ℚ A₁ A₂ f h₂) n₀ := by
  rw [cupRelChain_congr hs hs' (relDiffLM_relMapLM ℚ A₁ A₂ f h₂ t ht)]
  exact relComplexMap_cupRelChain A₁ A₂ f h₂ n₀ t ht

/-! ## §7. The four naturality squares -/

/-- The first naturality square. -/
theorem mvDeltaAuxCupNat_1 (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : ↥(Work.Cohomology.relKern ℚ X A n₀))
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    (CategoryTheory.CategoryStruct.comp (Work.Serre.mvFU X (∅ : Set X) U)
        (Work.Serre.cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.cupTop X A n₀ t ht)
          (Work.Serre.MVShift.shMap (Work.Serre.mvFU X A U) n₀)) := by
  rw [mvFU_empty]
  simp only [cupTopU, cupTop, cupTgtU, cupTgtU_cocycle, mvFU]
  exact relComplexMap_cupRelChain (X₁ := TopCat.of ↥U) (X₂ := X)
    (A₁ := interAU A U) (A₂ := A) (f := subtypeIncl X U)
    (h₂ := interAU_incl_subtypeIncl X A U) n₀ t ht

/-- The second naturality square. -/
theorem mvDeltaAuxCupNat_2 (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : ↥(Work.Cohomology.relKern ℚ X A n₀))
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    (CategoryTheory.CategoryStruct.comp (Work.Serre.mvFU X (∅ : Set X) V)
        (Work.Serre.cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.cupTop X A n₀ t ht)
          (Work.Serre.MVShift.shMap (Work.Serre.mvFU X A V) n₀)) := by
  rw [mvFU_empty]
  simp only [cupTopV, cupTop, cupTgtU, cupTgtU_cocycle, mvFU]
  exact relComplexMap_cupRelChain (X₁ := TopCat.of ↥V) (X₂ := X)
    (A₁ := interAU A V) (A₂ := A) (f := subtypeIncl X V)
    (h₂ := interAU_incl_subtypeIncl X A V) n₀ t ht

/-- The third naturality square. -/
theorem mvDeltaAuxCupNat_3 (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : ↥(Work.Cohomology.relKern ℚ X A n₀))
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    (CategoryTheory.CategoryStruct.comp (Work.Serre.mvGWU X (∅ : Set X) U V)
        (Work.Serre.cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.cupTopU X A U n₀ t ht)
          (Work.Serre.MVShift.shMap (Work.Serre.mvGWU X A U V) n₀)) := by
  simp only [cupTopUV, cupTopU, cupTgtUV, mvGWU]
  exact relComplexMap_cupRelChain (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥U)
    (A₁ := interAU A (U ∩ V)) (A₂ := interAU A U)
    (f := pdIncl U (U ∩ V) Set.inter_subset_left)
    (h₂ := interAU_incl_pdIncl_U X A U V) n₀
    (cupTgtU X A U n₀ t) (cupTgtU_cocycle X A U n₀ t ht)

/-- The fourth naturality square. -/
theorem mvDeltaAuxCupNat_4 (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : ↥(Work.Cohomology.relKern ℚ X A n₀))
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    (CategoryTheory.CategoryStruct.comp (Work.Serre.mvGWV X (∅ : Set X) U V)
        (Work.Serre.cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.cupTopV X A V n₀ t ht)
          (Work.Serre.MVShift.shMap (Work.Serre.mvGWV X A U V) n₀)) := by
  simp only [cupTopUV, cupTopV, mvGWV]
  exact relComplexMap_cupRelChain_gen (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥V)
    (A₁ := interAU A (U ∩ V)) (A₂ := interAU A V)
    (f := pdIncl V (U ∩ V) Set.inter_subset_right)
    (h₂ := interAU_incl_pdIncl_V X A U V) n₀
    (cupTgtU X A V n₀ t) (cupTgtU_cocycle X A V n₀ t ht)
    (cupTgtUV X A U V n₀ t) (cupTgtUV_eq_V X A U V n₀ t)
    (cupTgtUV_cocycle X A U V n₀ t ht)

theorem mvDeltaAuxCupNat (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : ↥(Work.Cohomology.relKern ℚ X A n₀))
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    (CategoryTheory.CategoryStruct.comp (Work.Serre.mvFU X (∅ : Set X) U)
        (Work.Serre.cupTopU X A U n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.cupTop X A n₀ t ht)
          (Work.Serre.MVShift.shMap (Work.Serre.mvFU X A U) n₀))
    ∧ (CategoryTheory.CategoryStruct.comp (Work.Serre.mvFU X (∅ : Set X) V)
        (Work.Serre.cupTopV X A V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.cupTop X A n₀ t ht)
          (Work.Serre.MVShift.shMap (Work.Serre.mvFU X A V) n₀))
    ∧ (CategoryTheory.CategoryStruct.comp (Work.Serre.mvGWU X (∅ : Set X) U V)
        (Work.Serre.cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.cupTopU X A U n₀ t ht)
          (Work.Serre.MVShift.shMap (Work.Serre.mvGWU X A U V) n₀))
    ∧ (CategoryTheory.CategoryStruct.comp (Work.Serre.mvGWV X (∅ : Set X) U V)
        (Work.Serre.cupTopUV X A U V n₀ t ht)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.cupTopV X A V n₀ t ht)
          (Work.Serre.MVShift.shMap (Work.Serre.mvGWV X A U V) n₀)) :=
  ⟨mvDeltaAuxCupNat_1 X A U V n₀ t ht, mvDeltaAuxCupNat_2 X A U V n₀ t ht,
    mvDeltaAuxCupNat_3 X A U V n₀ t ht, mvDeltaAuxCupNat_4 X A U V n₀ t ht⟩

end

end Work.Serre
