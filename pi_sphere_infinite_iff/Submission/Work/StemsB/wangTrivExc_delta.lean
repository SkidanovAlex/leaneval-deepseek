import Mathlib
import Submission.Work.StemsB.wangCollarDerivDefs
import Submission.Work.StemsB.pairDelta_relComplexMap

/-!
# The identification `Triv ∘ Exc ∘ δ ∘ γ⁻¹ = λ_G^*`

For the collar pair `(Q, C_Q) = (↥(sphLoopBig b) × F_G, C × F_G)`, this file proves that the
composite of the excision comparison `wangExc`, the trivialisation comparison `wangTriv` and the
connecting homomorphism `pairδ` of the pair `(E, E|_O)`, applied to the source identification
`γ⁻¹ = wangRetr^*`, is the connecting homomorphism of the collar pair applied to the pullback
`λ_G^*` along the clutching map:

`Triv (Exc (δ (γ⁻¹ a))) = δ_{collar} (λ_G^* a)`.

The proof uses the naturality of `pairδ` under the two maps of pairs (`pairDelta_relComplexMap`)
and the `rfl`-level identity `wangRetr (Ψ_G q) = λ_G q` (`wangRetr_fibTrivΨ`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- The map of pairs `(Q, C_Q) → (E|_G, E|_C)` induced by `Ψ_G`, followed by the inclusion
`E|_G ↪ E` and the retraction `wangRetr`, is the clutching map `λ_G`. -/
lemma wangAbsMap_eq (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.relMapSub (wangCQ b p d_G) (wangA1 b p)
          (TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G)) (wangTrivMap_mem b p d_G hT_G))
        (Work.Cohomology.relMapSub (wangA1 b p) (wangA b p)
          (TopCat.ofHom (wangExcMap b p)) (wangExcMap_mem b p)))
      (TopCat.ofHom (wangRetr b p hT_O))
      = TopCat.ofHom (collarLambdaG b p d_G hT_G hT_O) := by
  apply TopCat.ext
  intro q
  apply Subtype.ext
  show ((wangRetr b p hT_O) ⟨((fibTrivΨ p (sphLoopBig b) d_G hT_G) q.1).1, _⟩ : E)
      = (collarLambdaG b p d_G hT_G hT_O q : E)
  exact congrArg Subtype.val (wangRetr_fibTrivΨ b p hT_O d_G hT_G q)

/-- The map of pairs `(E|_G, E|_C) → (E, E|_O)` of `wangExc`, as a map of subspaces. -/
abbrev wangK1 (b : ℕ) (p : C(E, SphModel b)) :
    TopCat.of ↥(wangA1 b p) ⟶ TopCat.of ↥(wangA b p) :=
  Work.Cohomology.relMapSub (wangA1 b p) (wangA b p)
    (TopCat.ofHom (wangExcMap b p)) (wangExcMap_mem b p)

/-- The map of pairs `(Q, C_Q) → (E|_G, E|_C)` of `wangTriv`, as a map of subspaces. -/
abbrev wangK2 (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    TopCat.of ↥(wangCQ b p d_G) ⟶ TopCat.of ↥(wangA1 b p) :=
  Work.Cohomology.relMapSub (wangCQ b p d_G) (wangA1 b p)
    (TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G)) (wangTrivMap_mem b p d_G hT_G)

/-- **The pullback composite is the clutching pullback**:  `λ_G^*` is the composite of `γ⁻¹`
(`wangRetr^*`), the absolute companion of `wangExc` and the absolute companion of `wangTriv`. -/
lemma wangAbsComp_eq (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.singularCohomologyMap ℤ (WangAO b p) (WangFO b p)
        (TopCat.ofHom (wangRetr b p hT_O)) (n + b))
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangA1 b p))
          (TopCat.of ↥(wangA b p)) (wangK1 b p) (n + b))
        (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangCQ b p d_G))
          (TopCat.of ↥(wangA1 b p)) (wangK2 b p d_G hT_G) (n + b)))
      = collarLambdaGCoh b p d_G hT_G hT_O (n + b) := by
  have h1 : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangA1 b p))
        (TopCat.of ↥(wangA b p)) (wangK1 b p) (n + b))
      (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangCQ b p d_G))
        (TopCat.of ↥(wangA1 b p)) (wangK2 b p d_G hT_G) (n + b))
      = Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangCQ b p d_G))
          (TopCat.of ↥(wangA b p))
          (CategoryTheory.CategoryStruct.comp (wangK2 b p d_G hT_G) (wangK1 b p)) (n + b) :=
    (Work.Cohomology.singularCohomologyMap_comp (R := ℤ) (f := wangK2 b p d_G hT_G)
      (g := wangK1 b p) (n := n + b)).symm
  have h2 : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.singularCohomologyMap ℤ (WangAO b p) (WangFO b p)
        (TopCat.ofHom (wangRetr b p hT_O)) (n + b))
      (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangCQ b p d_G))
        (TopCat.of ↥(wangA b p))
        (CategoryTheory.CategoryStruct.comp (wangK2 b p d_G hT_G) (wangK1 b p)) (n + b))
      = Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangCQ b p d_G)) (WangFO b p)
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp (wangK2 b p d_G hT_G) (wangK1 b p))
            (TopCat.ofHom (wangRetr b p hT_O))) (n + b) :=
    (Work.Cohomology.singularCohomologyMap_comp (R := ℤ)
      (f := CategoryTheory.CategoryStruct.comp (wangK2 b p d_G hT_G) (wangK1 b p))
      (g := TopCat.ofHom (wangRetr b p hT_O)) (n := n + b)).symm
  rw [h1, h2, wangAbsMap_eq b p d_G hT_G hT_O]
  rfl

/-- **The identification of Step 5**: the composite of the excision comparison, the trivialisation
comparison and the connecting homomorphism of `(E, E|_O)`, applied to the source identification
`γ⁻¹`, is the connecting homomorphism of the collar pair applied to the clutching pullback
`λ_G^*`. -/
theorem wangTrivExc_delta (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (n : ℕ)
    (a : Work.Cohomology.singularCohomology ℤ (n + b) (wangCohFsp b p)) :
    (wangTriv b p d_G hT_G (n + b + 1)).hom
        ((wangExc b p (n + b + 1)).hom
          ((Work.Cohomology.pairδ ℤ (TopCat.of E) (wangA b p) (n + b)).hom
            ((wangRetrCoh b p hT_O (n + b)).hom a)))
      = (collarDelta b (wangFY b p d_G) n)
          ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom a) := by
  simp only [wangExc, wangTriv]
  have hAbs : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.singularCohomologyMap ℤ (WangAO b p) (WangFO b p)
        (TopCat.ofHom (wangRetr b p hT_O)) (n + b))
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangA1 b p))
          (TopCat.of ↥(wangA b p)) (wangK1 b p) (n + b))
        (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangCQ b p d_G))
          (TopCat.of ↥(wangA1 b p)) (wangK2 b p d_G hT_G) (n + b)))
      = collarLambdaGCoh b p d_G hT_G hT_O (n + b) := wangAbsComp_eq b p d_G hT_G hT_O n
  have hAbs' := congrArg (fun φ => φ.hom a) hAbs
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hAbs'
  have hExc := pairDelta_relComplexMap (X1 := wangEG b p) (X2 := TopCat.of E)
    (wangA1 b p) (wangA b p) (TopCat.ofHom (wangExcMap b p)) (wangExcMap_mem b p) (n + b)
  have hExc' := congrArg (fun φ => φ.hom ((wangRetrCoh b p hT_O (n + b)).hom a)) hExc
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hExc'
  have hTriv := pairDelta_relComplexMap
    (X1 := TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (X2 := wangEG b p)
    (wangCQ b p d_G) (wangA1 b p)
    (TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G)) (wangTrivMap_mem b p d_G hT_G) (n + b)
  have hTriv' := congrArg (fun φ => φ.hom
    ((HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ (TopCat.of ↥(wangA1 b p))
      (TopCat.of ↥(wangA b p)) (Work.Cohomology.relMapSub (wangA1 b p) (wangA b p)
        (TopCat.ofHom (wangExcMap b p)) (wangExcMap_mem b p))) (n + b)).hom
        ((wangRetrCoh b p hT_O (n + b)).hom a))) hTriv
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hTriv'
  rw [← hExc', ← hTriv']
  change (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
        (wangCQ b p d_G) (n + b)).hom
      ((Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangCQ b p d_G))
          (TopCat.of ↥(wangA1 b p)) (wangK2 b p d_G hT_G) (n + b)).hom
        ((Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(wangA1 b p))
          (TopCat.of ↥(wangA b p)) (wangK1 b p) (n + b)).hom
          ((Work.Cohomology.singularCohomologyMap ℤ (WangAO b p) (WangFO b p)
            (TopCat.ofHom (wangRetr b p hT_O)) (n + b)).hom a)))
      = (collarDelta b (wangFY b p d_G) n)
          ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom a)
  exact congrArg (fun z => (Work.Cohomology.pairδ ℤ
    (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (wangCQ b p d_G) (n + b)).hom z) hAbs'


end

end Work.StemsB
