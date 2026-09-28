import Mathlib
import Submission.Work.Serre.mvLadder
import Submission.Work.Serre.mvDeltaAuxAssembly
import Submission.Work.Serre.MVShift.cupRelChainMap
import Submission.Work.Serre.MVShift.cupRelChain_homology
import Submission.Work.Serre.MVShift.relMapLM_mixedRelStar
import Submission.Work.Serre.mvDeltaAuxDefs

/-!
# The mixed cup product commutes with the Mayer–Vietoris connecting map

The target `Work.Serre.mvDeltaCupMixed` (statement unchanged, below) is the "derivation rule"

  `δ_∅(x) ⌣ U₀ = δ_A (x ⌣ U₀|)`

for the rational Mayer–Vietoris connecting map `Work.Serre.mvDelta` of the cover `X = U ∪ V` and
the pairs `(X,∅)` and `(X,A)`.

The proof reduces, via a cocycle representative `t` of `U₀`
(`Work.Cohomology.exists_relClassOf`), to the chain-level `δ`-square
`Work.Serre.deltaSquare` of `Submission/Work/Serre/mvDeltaAuxAssembly.lean`, which is the
"derivation rule at the level of cocycle representatives"; its six hypotheses (the four
naturality squares of the cup chain maps and the two homology identifications) are supplied here,
the first four by local copies of the lemmas of `Submission/Work/Serre/MVShift/deltaCupAssembly.lean`
(proved from `MVShift.cupRelChainMap` / `MVShift.relMapLM_mixedRelStar`) and the last two by
`MVShift.cupRelChain_homology`.  The remaining bookkeeping is
`Work.Serre.ovlClass_relClassOf` (the restriction of the class of a cocycle is the class of the
restricted cocycle).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- `eqToHom` only depends on the target of the equation. -/
theorem eqToHom_congrArg_irrel' {X : TopCat} (A : Set X) {a b : ℕ} (h₁ h₂ : a = b) :
    CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) h₁)
      = CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) h₂) := by
  rw [Subsingleton.elim h₁ h₂]

/-! ## The four chain-level naturality squares (local copies) -/

theorem relMapLM_comp_apply_local {X₁ X₂ X₃ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (A₃ : Set X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : ∀ x ∈ A₁, f x ∈ A₂) (h' : ∀ x ∈ A₂, g x ∈ A₃)
    (h'' : ∀ x ∈ A₁, g (f x) ∈ A₃) (n : ℕ) (y : ↥(Work.Cohomology.relKern ℚ X₃ A₃ n)) :
    Work.Cohomology.relMapLM (R := ℚ) (X₁ := X₁) (X₂ := X₂) A₁ A₂ f h n
        (Work.Cohomology.relMapLM (R := ℚ) (X₁ := X₂) (X₂ := X₃) A₂ A₃ g h' n y)
      = Work.Cohomology.relMapLM (R := ℚ) (X₁ := X₁) (X₂ := X₃) A₁ A₃ (f ≫ g) h'' n y := by
  apply Subtype.ext
  simp only [Work.Cohomology.relMapLM_coe]
  show ((Work.Cohomology.dualChainMap ℚ X₂ X₃ g).f n ≫
      (Work.Cohomology.dualChainMap ℚ X₁ X₂ f).f n).hom y.1
    = ((Work.Cohomology.dualChainMap ℚ X₁ X₃ (f ≫ g)).f n).hom y.1
  rw [← HomologicalComplex.comp_f, ← Work.Cohomology.dualChainMap_comp]

theorem cupTgtU_V_restrict_local (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀) :
    Work.Cohomology.relMapLM (R := ℚ) (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥V)
        (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A V)
        (Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right)
        (fun _ hx => hx) n₀ (cupTgtU X A V n₀ t)
      = cupTgtUV X A U V n₀ t := by
  have hL := relMapLM_comp_apply_local (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥V) (X₃ := X)
    (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A V) A
    (Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right) (Work.Cohomology.subtypeIncl X V)
    (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) n₀ t
  have hR := relMapLM_comp_apply_local (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥U) (X₃ := X)
    (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U) A
    (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left) (Work.Cohomology.subtypeIncl X U)
    (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) n₀ t
  rw [show (cupTgtU X A V n₀ t) = Work.Cohomology.relMapLM (R := ℚ) (X₁ := TopCat.of ↥V)
      (X₂ := X) (Work.Cohomology.interAU A V) A (Work.Cohomology.subtypeIncl X V)
      (fun _ hx => hx) n₀ t from rfl]
  rw [show (cupTgtUV X A U V n₀ t) = Work.Cohomology.relMapLM (R := ℚ)
      (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥U)
      (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U)
      (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left) (fun _ hx => hx) n₀
      (Work.Cohomology.relMapLM (R := ℚ) (X₁ := TopCat.of ↥U) (X₂ := X)
        (Work.Cohomology.interAU A U) A (Work.Cohomology.subtypeIncl X U)
        (fun _ hx => hx) n₀ t) from rfl]
  rw [hL, hR]
  apply Subtype.ext
  show ((Work.Cohomology.dualChainMap ℚ (TopCat.of ↥(U ∩ V)) X
      ((Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right) ≫
        (Work.Cohomology.subtypeIncl X V))).f n₀).hom t.1
    = ((Work.Cohomology.dualChainMap ℚ (TopCat.of ↥(U ∩ V)) X
      ((Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left) ≫
        (Work.Cohomology.subtypeIncl X U))).f n₀).hom t.1
  rw [show ((Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right) ≫
        (Work.Cohomology.subtypeIncl X V))
      = ((Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left) ≫
        (Work.Cohomology.subtypeIncl X U)) from by
    ext x
    rfl]

theorem cupSquareFU (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.cupTop X A n₀ t ht)
        (MVShift.shMap (Work.Serre.mvFU X A U) n₀)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.mvFU X (∅ : Set X) U)
          (Work.Serre.cupTopU X A U n₀ t ht) :=
  MVShift.cupRelChainMap (X₁ := TopCat.of ↥U) (X₂ := X)
    (Work.Cohomology.interAU A U) A (Work.Cohomology.subtypeIncl X U) (fun _ hx => hx) n₀ t ht

theorem cupSquareFV (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.cupTop X A n₀ t ht)
        (MVShift.shMap (Work.Serre.mvFU X A V) n₀)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.mvFU X (∅ : Set X) V)
          (Work.Serre.cupTopV X A V n₀ t ht) :=
  MVShift.cupRelChainMap (X₁ := TopCat.of ↥V) (X₂ := X)
    (Work.Cohomology.interAU A V) A (Work.Cohomology.subtypeIncl X V) (fun _ hx => hx) n₀ t ht

theorem cupSquareGWU (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.cupTopU X A U n₀ t ht)
        (MVShift.shMap (Work.Serre.mvGWU X A U V) n₀)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.mvGWU X (∅ : Set X) U V)
          (Work.Serre.cupTopUV X A U V n₀ t ht) :=
  MVShift.cupRelChainMap (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥U)
    (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U)
    (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left) (fun _ hx => hx) n₀
    (cupTgtU X A U n₀ t) (cupTgtU_cocycle X A U n₀ t ht)

theorem cupSquareGWV (X : TopCat) (A : Set X) (U V : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.cupTopV X A V n₀ t ht)
        (MVShift.shMap (Work.Serre.mvGWV X A U V) n₀)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.mvGWV X (∅ : Set X) U V)
          (Work.Serre.cupTopUV X A U V n₀ t ht) := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hkey := MVShift.relMapLM_mixedRelStar
    (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := TopCat.of ↥V)
    (A₁ := Work.Cohomology.interAU A (U ∩ V)) (A₂ := Work.Cohomology.interAU A V)
    (f := Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right) (h := fun _ hx => hx) k n₀
    (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj (TopCat.of ↥V)) k from x.1)
    (cupTgtU X A V n₀ t)
  rw [cupTgtU_V_restrict_local X A U V n₀ t] at hkey
  exact hkey


theorem mvDeltaCupMixed (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (m : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.mvDelta X (∅ : Set X) U V hU hV hcov m)
        (Work.Serre.vertM X A n₀ U₀ (m + 1))
      = CategoryTheory.CategoryStruct.comp (Work.Serre.vertQ X A U V n₀ U₀ m)
        (Work.Serre.mvDeltaShift X A U V hU hV hcov n₀ m) := by
  classical
  obtain ⟨t, ht, rfl⟩ := Work.Cohomology.exists_relClassOf ℚ X A n₀ U₀
  have hsq := deltaSquare X A U V hU hV hcov n₀ t ht
    (cupSquareFU X A U V n₀ t ht).symm
    (cupSquareFV X A U V n₀ t ht).symm
    (cupSquareGWU X A U V n₀ t ht).symm
    (cupSquareGWV X A U V n₀ t ht).symm
    (MVShift.cupRelChain_homology X A n₀ t ht)
    (MVShift.cupRelChain_homology (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
      (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)) m
  rw [vertM, vertQ, mvDeltaShift]
  have hcupX : Work.Serre.cupVert A (m + 1) n₀ (Work.Cohomology.relClassOf ℚ X A t ht)
      = ModuleCat.ofHom (MVGlue.cupWith X A (m + 1) n₀
          (Work.Cohomology.relClassOf ℚ X A t ht)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hcupUV : Work.Serre.cupVert {y : ↥(U ∩ V) | (y : X) ∈ A} m n₀
        (Work.Serre.U₀ovl X A U V n₀ (Work.Cohomology.relClassOf ℚ X A t ht))
      = ModuleCat.ofHom (MVGlue.cupWith ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) m n₀
          (Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V))
            (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht))) := by
    rw [ovlClass_relClassOf X A U V n₀ t ht]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  rw [hcupX, hcupUV, eqToHom_congrArg_irrel' A (mvShiftEq m n₀)
    (by omega : (m + n₀) + 1 = (m + 1) + n₀)]
  exact hsq

end

end Work.Serre
