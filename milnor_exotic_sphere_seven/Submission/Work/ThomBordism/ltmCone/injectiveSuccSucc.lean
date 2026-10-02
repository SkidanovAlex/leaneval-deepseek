import Mathlib
import Submission.Work.ThomBordism.ltmConeAux
import Submission.Work.ThomBordism.localThom_iUnion_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Injectivity of the local Thom map two degrees above cone cyclicity

This is the "injectivity half" of the cone-to-isomorphism step of
`Work.ThomBordism.localThomMap_bijective_of_coneData`.

`ConeCyclicPos Z n U τ U hU m` says that every cycle of the mapping cone of the cochain-level
Thom map `ψ = cup(-, tauRep)` in degree `m+1` is a boundary.  The cone sits in the indexing
`ConeC m = Base^{m+1} ⊕ Tot^{m+n}`, so a *base* cocycle of degree `m+2` whose `ψ`-image is a
coboundary assembles with that primitive into a cone-`(m+1)`-cycle; cyclicity at `m` makes its base
component a coboundary, i.e. the class vanishes.  Reading this through the class/coboundary
dictionary (`PsiClassHyp` identifies the class of `psiAbs a` with the local Thom map of the class of
`a`) gives the injectivity of `localThomMap Z n U τ (m+2)`.

The proof is the mirror image of the first block of
`Work.ThomBordism.coneCyclicPos_of_localThomMap`, with the roles of the hypothesis and the
conclusion exchanged.
-/

namespace Work.ThomBordism.ltmCone

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

theorem injectiveSuccSucc {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (hψ : Work.ThomBordism.PsiClassHyp Z n U τ U (fun x hx => hx))
    (m : ℕ) (hpos : Work.ThomBordism.ConeCyclicPos Z n U τ U (fun x hx => hx) m) :
    Function.Injective (Work.Thom.localThomMap Z n U τ (m + 2)) := by
  intro x y hxy
  -- It suffices to show that the kernel vanishes.
  have hker : ∀ x : Work.Thom.Coh ℤ (m+2) ↥U,
      Work.Thom.localThomMap Z n U τ (m+2) x = 0 → x = 0 := by
    intro x hx0
    obtain ⟨a, ha, hca⟩ :=
      Work.Cohomology.exists_cohomologyClassOf ℤ (Work.ThomBordism.baseSSet U) (m+2) x
    -- `psiAbs` of the cocycle `a` is a relative cocycle.
    have hψd : Work.ThomBordism.totShiftD Z n U (m+2)
        (Work.ThomBordism.psiAbs Z n U τ U (fun x hx => hx) (m+2) a) = 0 := by
      show ((Work.ThomBordism.TotComplex Z U).d ((m+2)+n) (((m+2)+1)+n)).hom
        (Work.ThomBordism.psiAbs Z n U τ U (fun x hx => hx) (m+2) a) = 0
      rw [Work.ThomBordism.psiAbs_diff Z n U τ U (fun x hx => hx) (m+2) a, ha]
      exact map_zero (Work.ThomBordism.psiAbsLM Z n U τ U (fun x hx => hx) ((m+2)+1))
    have hcycψ : Work.Cohomology.relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' U))
        (Work.ThomBordism.relPiece Z U) (m+2+n)
        (Work.ThomBordism.psiAbs Z n U τ U (fun x hx => hx) (m+2) a) = 0 :=
      Work.ThomBordism.relDiffLM_eq_zero_of_totShiftD Z U n (m+2)
        (Work.ThomBordism.psiAbs Z n U τ U (fun x hx => hx) (m+2) a) hψd
    -- the class of `psiAbs a` is `localThomMap x`, which vanishes by hypothesis
    have hclass : Work.Cohomology.relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U))
        (Work.ThomBordism.relPiece Z U)
        (Work.ThomBordism.psiAbs Z n U τ U (fun x hx => hx) (m+2) a) hcycψ = 0 := by
      rw [hψ (m+2) a ha hcycψ, Work.ThomBordism.pdCohMap_preim_self Z n U τ, hca]
      exact hx0
    -- hence `psiAbs a` is a `totShiftD`-coboundary
    obtain ⟨b, hb⟩ :=
      Work.ThomBordism.exists_totShiftD_of_relClass_eq_zero Z U n (m+1) _ hcycψ hclass
    -- so `(a, -b)` is a cone-`(m+1)`-cycle
    have hcyc : Work.ThomBordism.ConeCycle Z n U τ U (fun x hx => hx) (m+1) (a, -b) := by
      show Work.ThomBordism.coneD Z n U τ U (fun x hx => hx) (m+1) (a, -b) = 0
      rw [Work.ThomBordism.coneD_apply]
      have h1 : (Work.Cohomology.cochainDiffLM ℤ (Work.ThomBordism.baseSSet U) ((m+1)+1)) a = 0 :=
        ha
      have h3 : (Work.ThomBordism.psiAbsLM Z n U τ U (fun x hx => hx) ((m+1)+1)) a
          = Work.ThomBordism.psiAbs Z n U τ U (fun x hx => hx) (m+2) a := rfl
      rw [h1, neg_zero, Work.ThomBordism.totShiftD_neg, hb, h3, add_neg_cancel]
      rfl
    -- cyclicity of the cone makes the base component a coboundary
    obtain ⟨q, hq⟩ := hpos (a, -b) hcyc
    obtain ⟨a', b'⟩ := q
    have hfirst : -(Work.Cohomology.cochainDiffLM ℤ (Work.ThomBordism.baseSSet U) (m+1) a')
        = (a : Work.ThomBordism.BaseC U ((m+1)+1)) := by
      have h := congrArg Prod.fst hq
      simpa only [Work.ThomBordism.coneD_apply, LinearMap.neg_apply] using h
    have hcob : ∃ w : Work.ThomBordism.BaseC U (m+1),
        Work.Cohomology.cochainDiff ℤ (Work.ThomBordism.baseSSet U) w = a := by
      refine ⟨-a', ?_⟩
      rw [show Work.Cohomology.cochainDiff ℤ (Work.ThomBordism.baseSSet U) (-a')
          = Work.Cohomology.cochainDiffLM ℤ (Work.ThomBordism.baseSSet U) (m+1) (-a') from rfl,
        map_neg]
      exact hfirst
    rw [← hca]
    exact (Work.ThomBordism.baseClass_eq_zero_iff_coboundary U (m+1) a ha).mpr hcob
  have h := hker (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp h

end Work.ThomBordism.ltmCone
