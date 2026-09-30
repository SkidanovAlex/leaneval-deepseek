import Mathlib
import Submission.Work.StemsB.Rat.WangThetaLow

/-!
# The value of the low-degree Wang transgression `τS`

This file proves the value statement of the **low-degree** Wang transport `τS`,
the analogue of `Work.StemsB.Rat.wangTauS_value` in degree `b - 1`
(the degree of the fundamental class of the fibre):

`τSLow (δ (γ⁻¹ a)) = θLow a`,   `θLow = ρ ∘ Σ_low ∘ λ_G^*`.

The transport `τS_low` is the five-fold composite
`Exc ≫ Triv ≫ (degree transport) ≫ Φ⁻¹ ≫ ρ` of `Work.StemsB.Rat.wangTauSLow`, and the
low-degree transgression `θLow` is `Work.StemsB.Rat.wangThetaLow`.

The two new ingredients are

* `wangTauSLow_hom_apply` — the computation rule of the composite `τS_low` (bookkeeping);
* `wangTrivExc_delta_gen` — the low-degree form of `Work.StemsB.Rat.wangTrivExc_delta`:
  `Triv (Exc (δ (γ⁻¹ a))) = δ_{collar} (λ_G^* a)`, stated for an **arbitrary** degree `k`
  (the existing statement is only available in degrees of the form `n + b`, which cannot
  reach the top fibre degree `b - 1`).

The remaining steps are the definitional identifications
`collarSigmaLow = Φ⁻¹ ∘ relCohZeroAdd ∘ collarDeltaLow` and
`wangRelEqIsoLow.hom = (eqToHom lowCast) ≫ (eqToHom (Nat.zero_add b).symm)`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Work.StemsB.Rat

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-! ## The degree-general form of `Triv ∘ Exc ∘ δ ∘ γ⁻¹ = λ_G^*` -/

/-- **The pullback composite is the clutching pullback, in an arbitrary degree**: `λ_G^*` is the
composite of `γ⁻¹` (`wangRetr^*`), the absolute companion of `wangExc` and the absolute companion
of `wangTriv`.  This is the degree-general form of `Work.StemsB.Rat.wangAbsComp_eq` (which is
stated only in the degrees `n + b`). -/
lemma wangAbsComp_eq_gen (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.singularCohomologyMap ℚ (WangAO b p) (WangFO b p)
        (TopCat.ofHom (wangRetr b p hT_O)) k)
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangA1 b p))
          (TopCat.of ↥(wangA b p)) (wangK1 b p) k)
        (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangCQ b p d_G))
          (TopCat.of ↥(wangA1 b p)) (wangK2 b p d_G hT_G) k))
      = collarLambdaGCoh b p d_G hT_G hT_O k := by
  have h1 : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangA1 b p))
        (TopCat.of ↥(wangA b p)) (wangK1 b p) k)
      (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangCQ b p d_G))
        (TopCat.of ↥(wangA1 b p)) (wangK2 b p d_G hT_G) k)
      = Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangCQ b p d_G))
          (TopCat.of ↥(wangA b p))
          (CategoryTheory.CategoryStruct.comp (wangK2 b p d_G hT_G) (wangK1 b p)) k :=
    (Work.Cohomology.singularCohomologyMap_comp (R := ℚ) (f := wangK2 b p d_G hT_G)
      (g := wangK1 b p) (n := k)).symm
  have h2 : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.singularCohomologyMap ℚ (WangAO b p) (WangFO b p)
        (TopCat.ofHom (wangRetr b p hT_O)) k)
      (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangCQ b p d_G))
        (TopCat.of ↥(wangA b p))
        (CategoryTheory.CategoryStruct.comp (wangK2 b p d_G hT_G) (wangK1 b p)) k)
      = Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangCQ b p d_G)) (WangFO b p)
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp (wangK2 b p d_G hT_G) (wangK1 b p))
            (TopCat.ofHom (wangRetr b p hT_O))) k :=
    (Work.Cohomology.singularCohomologyMap_comp (R := ℚ)
      (f := CategoryTheory.CategoryStruct.comp (wangK2 b p d_G hT_G) (wangK1 b p))
      (g := TopCat.ofHom (wangRetr b p hT_O)) (n := k)).symm
  rw [h1, h2, wangAbsMap_eq b p d_G hT_G hT_O]
  rfl

/-- **The identification of `Triv ∘ Exc ∘ δ ∘ γ⁻¹ = λ_G^*` in an arbitrary degree `k`**: the
composite of the excision comparison, the trivialisation comparison and the connecting
homomorphism of `(E, E|_O)`, applied to the source identification `γ⁻¹ = wangRetr^*`, is the
connecting homomorphism of the collar pair applied to the clutching pullback `λ_G^*`.

This is the degree-general form of `Work.StemsB.Rat.wangTrivExc_delta`; the degree-`b - 1` case is
what the low-degree Wang transgression needs. -/
theorem wangTrivExc_delta_gen (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ)
    (a : Work.Cohomology.singularCohomology ℚ k (wangCohFsp b p)) :
    (wangTriv b p d_G hT_G (k + 1)).hom
        ((wangExc b p (k + 1)).hom
          ((Work.Cohomology.pairδ ℚ (TopCat.of E) (wangA b p) k).hom
            ((wangRetrCoh b p hT_O k).hom a)))
      = (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
          (wangCQ b p d_G) k).hom
          ((collarLambdaGCoh b p d_G hT_G hT_O k).hom a) := by
  simp only [wangExc, wangTriv]
  have hAbs : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.singularCohomologyMap ℚ (WangAO b p) (WangFO b p)
        (TopCat.ofHom (wangRetr b p hT_O)) k)
      (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangA1 b p))
          (TopCat.of ↥(wangA b p)) (wangK1 b p) k)
        (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangCQ b p d_G))
          (TopCat.of ↥(wangA1 b p)) (wangK2 b p d_G hT_G) k))
      = collarLambdaGCoh b p d_G hT_G hT_O k := wangAbsComp_eq_gen b p d_G hT_G hT_O k
  have hAbs' := congrArg (fun φ => φ.hom a) hAbs
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hAbs'
  have hExc := pairDelta_relComplexMap (X1 := wangEG b p) (X2 := TopCat.of E)
    (wangA1 b p) (wangA b p) (TopCat.ofHom (wangExcMap b p)) (wangExcMap_mem b p) k
  have hExc' := congrArg (fun φ => φ.hom ((wangRetrCoh b p hT_O k).hom a)) hExc
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hExc'
  have hTriv := pairDelta_relComplexMap
    (X1 := TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (X2 := wangEG b p)
    (wangCQ b p d_G) (wangA1 b p)
    (TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G)) (wangTrivMap_mem b p d_G hT_G) k
  have hTriv' := congrArg (fun φ => φ.hom
    ((HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℚ (TopCat.of ↥(wangA1 b p))
      (TopCat.of ↥(wangA b p)) (Work.Cohomology.relMapSub (wangA1 b p) (wangA b p)
        (TopCat.ofHom (wangExcMap b p)) (wangExcMap_mem b p))) k).hom
        ((wangRetrCoh b p hT_O k).hom a))) hTriv
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hTriv'
  rw [← hExc', ← hTriv']
  change (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
        (wangCQ b p d_G) k).hom
      ((Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangCQ b p d_G))
          (TopCat.of ↥(wangA1 b p)) (wangK2 b p d_G hT_G) k).hom
        ((Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(wangA1 b p))
          (TopCat.of ↥(wangA b p)) (wangK1 b p) k).hom
          ((Work.Cohomology.singularCohomologyMap ℚ (WangAO b p) (WangFO b p)
            (TopCat.ofHom (wangRetr b p hT_O)) k).hom a)))
      = (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
          (wangCQ b p d_G) k).hom ((collarLambdaGCoh b p d_G hT_G hT_O k).hom a)
  exact congrArg (fun z => (Work.Cohomology.pairδ ℚ
    (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (wangCQ b p d_G) k).hom z) hAbs'

/-! ## The computation rule of `τS_low` -/

/-- **The computation rule of `wangTauSLow`**: applying it to a class factors through the five maps
of which it is composed (excision, the trivialisation, the degree transport, the inverse Thom
isomorphism of the collar, the clutching identification). -/
theorem wangTauSLow_hom_apply (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (z : (Work.Cohomology.relComplex ℚ (TopCat.of E) (wangA b p)).homology ((b - 1) + 1)) :
    (wangTauSLow b hb E p hT_O d_G hT_G).hom z =
      (rhoCoh b (by omega) p d_G hT_G hT_O 0).hom
        ((collarPhiIso b (by omega) (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
            (wangSusT_thom b hb (wangFY b p d_G)) 0).inv
          ((wangRelEqIsoLow b (by omega) E p d_G).hom
            ((wangTriv b p d_G hT_G ((b - 1) + 1)).hom
              ((wangExc b p ((b - 1) + 1)).hom z)))) := by
  simp only [wangTauSLow, wangExcIso, wangTrivIso, wangRelEqIsoLow, rhoIso, Iso.trans_hom,
    Iso.symm_hom, asIso_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

/-! ## The degree transport versus the connecting homomorphism of the collar -/

/-- **The degree transport of `τS_low` is the degree transport of the collar connecting
homomorphism**: `wangRelEqIsoLow` is the composite of the two `eqToHom`s of which `collarDeltaLow`
and `relCohZeroAdd` are made. -/
lemma wangRelEqIsoLow_pairδ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b (wangFY b p d_G)))).homology (b - 1)) :
    (wangRelEqIsoLow b hb E p d_G).hom
      ((Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
        (wangCQ b p d_G) (b - 1)).hom x)
      = relCohZeroAdd (Y := wangFY b p d_G) b
          (collarDeltaLow b hb (wangFY b p d_G) x) := by
  rw [collarDeltaLow_apply]
  show (eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℚ
        (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (wangCQ b p d_G)).homology t)
        ((lowCast b hb).trans (Nat.zero_add b).symm)))
      ((Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
        (wangCQ b p d_G) (b - 1)).hom x)
    = (eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℚ
        (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (wangCQ b p d_G)).homology t)
        (Nat.zero_add b).symm))
      ((eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℚ
        (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (wangCQ b p d_G)).homology t)
        (lowCast b hb)))
      ((Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
        (wangCQ b p d_G) (b - 1)).hom x))
  exact (eqToHom_homology_trans_apply _ (lowCast b hb) (Nat.zero_add b).symm _).symm

/-- **The inverse Thom isomorphism of `τS_low` inverts the collar transgression**: applied to
`δ x` (transported along `relCohZeroAdd` to the degree of the Thom map), `Φ⁻¹` is
`collarSigmaLow`.  This is the defining property of `collarSigmaLow`, read backwards. -/
lemma collarPhiIso_inv_relCohZeroAdd (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1)) :
    (collarPhiIso b hb Y τ hτ 0).inv
        (relCohZeroAdd (Y := Y) b (collarDeltaLow b hb Y x))
      = collarSigmaLow b hb Y τ hτ x := by
  rfl

/-! ## The value of `τS_low` -/

/-- **The value of the low-degree Wang transport `τS`**: on the image of the connecting
homomorphism of the source identification, `τS_low` is the geometric transgression
`θLow = ρ ∘ Σ_low ∘ λ_G^*`. -/
theorem wangTauSLow_value (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b))
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G)
    (a : Work.Cohomology.singularCohomology ℚ (b - 1) (Work.StemsB.wangCohFsp b p)) :
    (Work.StemsB.Rat.wangTauSLow b hb E p hT_O d_G hT_G).hom
        ((Work.Cohomology.pairδ ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p) (b - 1)).hom
          ((Work.StemsB.Rat.wangGammaExplicit b p hT_O (b - 1)).inv a))
      = Work.StemsB.Rat.wangThetaLow b hb E p d_G hT_G hT_O a := by
  rw [wangTauSLow_hom_apply]
  rw [wangGammaExplicit_inv]
  rw [show (wangTriv b p d_G hT_G ((b - 1) + 1)).hom
        ((wangExc b p ((b - 1) + 1)).hom
          ((Work.Cohomology.pairδ ℚ (TopCat.of E) (wangA b p) (b - 1)).hom
            ((wangRetrCoh b p hT_O (b - 1)).hom a)))
      = (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
          (wangCQ b p d_G) (b - 1)).hom
          ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom a)
      from wangTrivExc_delta_gen b hb E p d_G hT_G hT_O (b - 1) a]
  rw [wangRelEqIsoLow_pairδ]
  rw [wangThetaLow_apply]
  rw [collarPhiIso_inv_relCohZeroAdd]

end

end Work.StemsB.Rat
