import Mathlib
import Submission.Work.Cohomology.Endgame.relComplexMapExcision
import Submission.Work.Thom.ATools
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.tubeTrans_modelSpan
import Submission.Work.ThomBordism.tubePointLocalisationIso
import Submission.Work.ThomBordism.chartModelClass_pairing_eq_pm_one
import Submission.Work.ThomBordism.localDegreeGenExists
import Submission.Work.ThomBordism.exists_zeroSection_pairing_one
import Submission.Work.Tubular.ThomRepOfLocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The pullback of the standard model generator to the punctured point pair of the tube
generates.**  Both the translation `y ↦ y - E.e x` (a homeomorphism of pairs) and the inclusion of
the tube (excision at the removed interior point `E.e x`) preserve generators. -/
theorem vpv_tubeTransModel (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Submodule.span ℤ
      ({ ((Work.Thom.relCohMap (tubeTransMap E C x) (tubePtSet E C x)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubeTransMap_mem E C x) ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))) } :
        Set (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U) (tubePtSet E C x))) = ⊤ := by
  exact Work.ThomBordism.tubeTrans_modelSpan E C x

/-- **The localisation of the tube pair at the point `E.e x` is an isomorphism.** -/
theorem vpv_tubePointLocalisationIso [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Function.Bijective ((Work.Thom.relCohMap (ContinuousMap.id ↥C.U)
      (Work.ThomBordism.tubeInvPunct E C) (tubePtSet E C x)
      (tubePtSet_subset E C x) ℤ (8 + k)).hom) := by
  exact Work.ThomBordism.tubePointLocalisationIso E C x

/-- **The ambient standard class generates** the relative cohomology of the tube pair in degree
`8 + k`. -/
theorem span_ambientStandardClass [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Submodule.span ℤ
      ({Work.ThomBordism.ambientStandardClass E C x} :
        Set (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U)
          (Work.ThomBordism.tubeInvPunct E C))) = ⊤ := by
  set x0 : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U) (tubePtSet E C x) :=
    (Work.Thom.relCohMap (tubeTransMap E C x) (tubePtSet E C x)
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubeTransMap_mem E C x) ℤ (8 + k)).hom
      (Work.ThomBordism.stdModelGen (8 + k)) with hx0
  have hx0span : Submodule.span ℤ ({x0} :
      Set (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U) (tubePtSet E C x))) = ⊤ :=
    vpv_tubeTransModel E C x
  have hfac : Work.ThomBordism.ambientStandardClass E C x
      = (Work.Thom.relCohMap (ContinuousMap.id ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
          (tubePtSet E C x) (tubePtSet_subset E C x) ℤ (8 + k)).hom x0 := by
    have h1 : Work.ThomBordism.ambientStandardClass E C x
        = (Work.Thom.relCohMap (tubeTransMap E C x) (Work.ThomBordism.tubeInvPunct E C)
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubeTransMap_mem_inv E C x)
            ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) := rfl
    rw [h1]
    have h2 := Work.Thom.relCohMap_comp' (Work.ThomBordism.tubeInvPunct E C)
      (tubePtSet E C x) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      (ContinuousMap.id ↥C.U) (tubeTransMap E C x) (tubePtSet_subset E C x)
      (tubeTransMap_mem E C x)
      (fun y hy => tubeTransMap_mem E C x y (tubePtSet_subset E C x hy)) ℤ (8 + k)
    have h3 : Work.Thom.relCohMap ((tubeTransMap E C x).comp (ContinuousMap.id ↥C.U))
          (Work.ThomBordism.tubeInvPunct E C) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (fun y hy => tubeTransMap_mem E C x y (tubePtSet_subset E C x hy)) ℤ (8 + k)
        = Work.Thom.relCohMap (tubeTransMap E C x) (Work.ThomBordism.tubeInvPunct E C)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubeTransMap_mem_inv E C x) ℤ (8 + k) :=
      Work.Thom.relCohMap_congr' _ _ (ContinuousMap.comp_id _) _ _ ℤ (8 + k)
    rw [← h3, ← h2]
    show (ModuleCat.Hom.hom (Work.Thom.relCohMap (tubeTransMap E C x) (tubePtSet E C x)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubeTransMap_mem E C x) ℤ (8 + k) ≫
      Work.Thom.relCohMap (ContinuousMap.id ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
        (tubePtSet E C x) (tubePtSet_subset E C x) ℤ (8 + k)))
        (Work.ThomBordism.stdModelGen (8 + k))
      = (ModuleCat.Hom.hom (Work.Thom.relCohMap (ContinuousMap.id ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C) (tubePtSet E C x) (tubePtSet_subset E C x)
        ℤ (8 + k))) x0
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, hx0]
  rw [hfac]
  exact Work.Tubular.span_singleton_map_eq_top _
    (vpv_tubePointLocalisationIso E C x).2 x0 hx0span

theorem valuePmOneV2 {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] (k : ℕ) (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
    (hδ : Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox) :
    (Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ = 1) ∨
    (Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ = -1) := by
  haveI hcomp : CompactSpace (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.compactSpace_normalDiscSub E ε
  have hU : IsCompact C.U := C.isCompact_U
  obtain ⟨q⟩ := Work.Tubular.nonempty_normalSphSub E C.eps_pos (by omega : 8 < 8 + k)
  obtain ⟨U₀, hU₀span, hU₀ld⟩ :=
    Work.ThomBordism.localDegreeGenExists (V := V) hk E C.eps_pos C q hU hR hbox g hg hg2
  obtain ⟨w, hw⟩ := Work.ThomBordism.exists_zeroSection_pairing_one (V := V) k E
  have hτ0 : Submodule.span ℤ
      ({Work.ThomBordism.ambientStandardClass E C x} :
        Set (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U)
          (Work.ThomBordism.tubeInvPunct E C))) = ⊤ :=
    span_ambientStandardClass E C x
  -- the primitive functional: `⟨(tubeInvMap)^* (w ⌣ U₀), −⟩` on the tube
  set β₀ : Work.Thom.RelCoh ℤ (k + 8) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) :=
    ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) 8 k w U₀)) with hβ₀
  set β : Work.Thom.RelCoh ℤ (k + 8) (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) :=
    (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C) (Work.ThomBordism.tubeInvPunct E C)
      (Work.Tubular.normalNonzero E) (fun y hy => hy) ℤ (k + 8)).hom β₀ with hβ
  have hφ : (Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
      (k + 8) β) δ = 1 := by
    rw [hβ, hβ₀]
    rw [Work.Tubular.relKronH_natural (X := TopCat.of ↥C.U)
      (Y := TopCat.of (Work.Tubular.NormalTotal E))
      (A := Work.ThomBordism.tubeInvPunct E C) (B := Work.Tubular.normalNonzero E)
      (f := TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
      (g := tubeInvSub E C)
      (hf := fun y hy => hy) (w := tubeInv_compat E C) (n := k + 8)
      ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) 8 k w U₀)) δ]
    rw [show (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
        (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
        (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
        (tubeInvSub E C) (tubeInv_compat E C)) (k + 8)).hom δ
        = Work.ThomBordism.tubeInvHomology E C δ from rfl]
    rw [hδ]
    exact (hU₀ld w).trans hw
  refine relKronH_pm_one_of_span_top_of_primitive
    ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x)
    (Work.Tubular.span_cast_singleton_eq_top (M := fun n => Work.Thom.RelCoh ℤ n
      (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C)) (Nat.add_comm 8 k) hτ0) δ
    (Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8) β) hφ

end

end Work.ThomBordism
