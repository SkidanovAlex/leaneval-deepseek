import Mathlib
import Submission.Work.ThomBordism.localThom_iUnion_aux
import Submission.Work.ThomBordism.iUnion.psiInterface
import Submission.Work.ThomBordism.ltmConeAux
import Submission.Work.ThomBordism.ltmCone.surjectiveSucc
import Submission.Work.ThomBordism.ltmCone.injectiveSuccSucc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false


open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- The `psiAbs`/`localThomMap` interface with the restricted class replaced by `τ` itself. -/
theorem psiClassHyp_self (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (hψ : PsiClassHyp Z n U τ U (fun x hx => hx)) (m : ℕ) (a : BaseC U m)
    (ha : cochainDiff ℤ (baseSSet U) a = 0)
    (hcyc : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) (m + n)
      (psiAbs Z n U τ U (fun x hx => hx) m a) = 0) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U)
        (psiAbs Z n U τ U (fun x hx => hx) m a) hcyc
      = Work.Thom.localThomMap Z n U τ m (cohomologyClassOf ℤ (baseSSet U) a ha) := by
  have h := hψ m a ha hcyc
  rwa [pdCohMap_preim_self Z n U τ] at h

/-- `psiAbsLM` agrees with `psiAbs` (a rewriting lemma for the `psiAbsLM`/`psiAbs` boundary). -/
theorem psiAbsLM_apply' (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) (m : ℕ) (a : BaseC W m) :
    psiAbsLM Z n U τ W hW m a = psiAbs Z n U τ W hW m a := rfl

/-- **Surjectivity in degree `0`** (from the Extra-term cyclicity). -/
theorem ltmSurjectiveZero (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n)
    (hψ : PsiClassHyp Z n U τ U (fun x hx => hx))
    (hzero : ConeCyclicZero Z n U τ U (fun x hx => hx)) :
    Function.Surjective (Work.Thom.localThomMap Z n U τ 0) := by
  intro y
  obtain ⟨b, hb, hbcls⟩ :=
    exists_relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) (0 + n) y
  have hb' : totShiftD Z n U 0 b = 0 := totShiftD_eq_zero_of_relDiffLM Z U n 0 b hb
  obtain ⟨q, hq⟩ := coneCyclicZero_surj Z n U τ U (fun x hx => hx) hzero hb'
  obtain ⟨a, b'⟩ := q
  have hdaL : (cochainDiffLM ℤ (baseSSet U) 0) a = 0 := by
    have h1 := congrArg Prod.fst hq
    simpa only [extraD, prod_zero_fst, neg_eq_zero] using h1
  have hda : cochainDiff ℤ (baseSSet U) a = 0 := hdaL
  have hsplitL : psiAbsLM Z n U τ U (fun x hx => hx) 0 a + totDpred Z n U b' = b := by
    have h2 := congrArg Prod.snd hq
    simpa only [extraD] using h2
  have hsplit : psiAbs Z n U τ U (fun x hx => hx) 0 a + totDpred Z n U b' = b := hsplitL
  have hcycψ : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) (0 + n)
      (psiAbs Z n U τ U (fun x hx => hx) 0 a) = 0 :=
    psiAbs_relDiff_zero Z n U τ U (fun x hx => hx) 0 a hda
  refine ⟨cohomologyClassOf ℤ (baseSSet U) a hda, ?_⟩
  rw [← psiClassHyp_self Z n U τ hψ 0 a hda hcycψ, ← hbcls]
  refine (relClassOf_eq_of_sub_eq_d Z U (n - 1) (0 + n) b
    (psiAbs Z n U τ U (fun x hx => hx) 0 a) b' hb hcycψ ?_).symm
  show b - psiAbs Z n U τ U (fun x hx => hx) 0 a = totDpred Z n U b'
  rw [← hsplit]
  abel

/-- **Injectivity in degree `1`** (from the Extra-term cyclicity). -/
theorem ltmEqZeroOne (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n)
    (hψ : PsiClassHyp Z n U τ U (fun x hx => hx))
    (hzero : ConeCyclicZero Z n U τ U (fun x hx => hx))
    (x : Work.Thom.Coh ℤ 1 ↥U) (hx : Work.Thom.localThomMap Z n U τ 1 x = 0) : x = 0 := by
  obtain ⟨a, ha, hxa⟩ := exists_cohomologyClassOf ℤ (baseSSet U) 1 x
  rw [← hxa] at hx ⊢
  have hcycψ : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) (1 + n)
      (psiAbs Z n U τ U (fun x hx => hx) 1 a) = 0 :=
    psiAbs_relDiff_zero Z n U τ U (fun x hx => hx) 1 a ha
  have hclass : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U)
      (psiAbs Z n U τ U (fun x hx => hx) 1 a) hcycψ = 0 := by
    rw [psiClassHyp_self Z n U τ hψ 1 a ha hcycψ]
    exact hx
  obtain ⟨w, hw⟩ := exists_totShiftD_of_relClass_eq_zero Z U n 0
    (psiAbs Z n U τ U (fun x hx => hx) 1 a) hcycψ hclass
  have hcyc : ConeCycle Z n U τ U (fun x hx => hx) 0 (a, -w) := by
    show coneD Z n U τ U (fun x hx => hx) 0 (a, -w) = 0
    rw [coneD_apply]
    refine Prod.ext ?_ ?_
    · show -(cochainDiffLM ℤ (baseSSet U) 1 a) = 0
      rw [cochainDiffLM_apply, ha, neg_zero]
    · show psiAbsLM Z n U τ U (fun x hx => hx) 1 a + totShiftD Z n U 0 (-w) = 0
      rw [show psiAbsLM Z n U τ U (fun x hx => hx) 1 a
          = psiAbs Z n U τ U (fun x hx => hx) 1 a from rfl]
      rw [totShiftD_neg, hw, add_neg_cancel]
  obtain ⟨a', ha'⟩ := coneCyclicZero_inj Z n U τ U (fun x hx => hx) hzero hcyc
  refine (baseClass_eq_zero_iff_coboundary U 0 a ha).mpr ⟨-a', ?_⟩
  show ((cochainDiffLM ℤ (baseSSet U) 0) (-a') : BaseC U (0 + 1)) = a
  rw [map_neg, ha', neg_neg]

/-- Kernel form of injectivity in degree `1`. -/
theorem ltmInjectiveOne (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n)
    (hψ : PsiClassHyp Z n U τ U (fun x hx => hx))
    (hzero : ConeCyclicZero Z n U τ U (fun x hx => hx)) :
    Function.Injective (Work.Thom.localThomMap Z n U τ 1) := by
  refine fun x y hxy => ?_
  have h : x - y = 0 :=
    ltmEqZeroOne Z n U τ hψ hzero (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp h

theorem localThomMap_bijective_of_coneData {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (hψ : Work.ThomBordism.PsiClassHyp Z n U τ U (fun x hx => hx))
    (hpos : ∀ m, Work.ThomBordism.ConeCyclicPos Z n U τ U (fun x hx => hx) m)
    (hzero : Work.ThomBordism.ConeCyclicZero Z n U τ U (fun x hx => hx))
    (h0inj : Function.Injective (Work.Thom.localThomMap Z n U τ 0)) :
    ∀ k, Function.Bijective (Work.Thom.localThomMap Z n U τ k) := by
  intro k
  rcases k with _ | _ | m
  · exact ⟨h0inj, ltmSurjectiveZero Z n U τ hψ hzero⟩
  · exact ⟨ltmInjectiveOne Z n U τ hψ hzero,
      ltmCone.surjectiveSucc Z n U τ hψ 0 (hpos 0)⟩
  · exact ⟨ltmCone.injectiveSuccSucc Z n U τ hψ m (hpos m),
      ltmCone.surjectiveSucc Z n U τ hψ (m + 1) (hpos (m + 1))⟩

end

end Work.ThomBordism
