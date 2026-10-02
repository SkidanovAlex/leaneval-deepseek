import Mathlib
import Submission.Work.ThomBordism.ltmConeAux
import Submission.Work.ThomBordism.localThom_iUnion_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

/-!
# Surjectivity of the local Thom map in positive degrees

`Work.ThomBordism.ConeCyclicPos Z n U τ U id m` says that the mapping cone of the cochain-level
Thom map `psiAbs` over `U` is *cyclic* at degree `m + 1`: every cone-`(m+1)`-cycle is the
`coneD m`-image of a cone-`m`-cochain.  The cone's differential is
`coneD m (a, b) = (-(d a), ψ a + totShiftD m b)`, so expanding a cone-cycle `(0, b)` produced by
`coneCyclicPos_surj` writes a `Tot`-cocycle `b` as

  `b = ψ a + totShiftD m b'`   with `d a = 0`,

i.e. every relative class in degree `(m+1) + n` is the class of a `psiAbs` of a **cycle** of the
base, up to a relative coboundary.  Reading the cup map `ψ` through the `psiAbs`/`localThomMap`
interface (`psiClassHyp_self`) turns this into the surjectivity of `localThomMap` in degree `m + 1`.

This is one of the two halves of the equivalence "cone cyclicity ⟺ bijectivity of the local Thom
map" (compare `Work.ThomBordism.coneCyclicPos_of_localThomMap` for the converse).
-/

namespace Work.ThomBordism.ltmCone

noncomputable section

/-- **The `psiAbs`/`localThomMap` interface with the restricted class replaced by `τ` itself.**

`Work.ThomBordism.PsiClassHyp Z n U τ U id` states that the relative class of `psiAbs … a` is the
local Thom map of the *restricted* class `τ|_U = (pdCohMap …).hom τ`.  Over the whole piece `U` the
restriction is `τ` (`Work.ThomBordism.pdCohMap_preim_self`), so the interface may be read with `τ`
itself in the class slot — the form in which the surjectivity argument needs it. -/
theorem psiClassHyp_self {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (hψ : Work.ThomBordism.PsiClassHyp Z n U τ U (fun x hx => hx)) (m : ℕ)
    (a : Work.ThomBordism.BaseC U m)
    (ha : Work.Cohomology.cochainDiff ℤ (Work.ThomBordism.baseSSet U) a = 0)
    (hcyc : Work.Cohomology.relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' U))
      (Work.ThomBordism.relPiece Z U) (m + n)
      (Work.ThomBordism.psiAbs Z n U τ U (fun x hx => hx) m a) = 0) :
    Work.Cohomology.relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (Work.ThomBordism.relPiece Z U)
        (Work.ThomBordism.psiAbs Z n U τ U (fun x hx => hx) m a) hcyc
      = Work.Thom.localThomMap Z n U τ m
          (Work.Cohomology.cohomologyClassOf ℤ (Work.ThomBordism.baseSSet U) a ha) := by
  have h := hψ m a ha hcyc
  rwa [Work.ThomBordism.pdCohMap_preim_self Z n U τ] at h

theorem surjectiveSucc {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (hψ : Work.ThomBordism.PsiClassHyp Z n U τ U (fun x hx => hx))
    (m : ℕ) (hpos : Work.ThomBordism.ConeCyclicPos Z n U τ U (fun x hx => hx) m) :
    Function.Surjective (Work.Thom.localThomMap Z n U τ (m + 1)) := by
  intro y
  -- A relative cocycle representative of the target class `y`.
  obtain ⟨b, hb, hbcls⟩ :=
    exists_relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) ((m + 1) + n) y
  have hb' : totShiftD Z n U (m + 1) b = 0 :=
    totShiftD_eq_zero_of_relDiffLM Z U n (m + 1) b hb
  -- Cyclicity of the cone produces a primitive of the `(0, b)`-cycle.
  obtain ⟨q, hq⟩ := coneCyclicPos_surj Z n U τ U (fun x hx => hx) m hpos hb'
  obtain ⟨a, b'⟩ := q
  -- Read off the two components of `coneD m (a, b') = (0, b)`.
  have hunfold : coneD Z n U τ U (fun x hx => hx) m (a, b') =
      (-(cochainDiffLM ℤ (baseSSet U) (m + 1) a),
        psiAbsLM Z n U τ U (fun x hx => hx) (m + 1) a + totShiftD Z n U m b') := rfl
  have h1 : -(cochainDiffLM ℤ (baseSSet U) (m + 1) a) = 0 := by
    have h := congrArg Prod.fst hq
    rw [hunfold] at h
    exact h
  have hdaLM : cochainDiffLM ℤ (baseSSet U) (m + 1) a = 0 := neg_eq_zero.mp h1
  have hda : cochainDiff ℤ (baseSSet U) a = 0 := by
    change cochainDiffLM ℤ (baseSSet U) (m + 1) a = 0
    exact hdaLM
  have hsplit : psiAbsLM Z n U τ U (fun x hx => hx) (m + 1) a + totShiftD Z n U m b' = b := by
    have h := congrArg Prod.snd hq
    rw [hunfold] at h
    exact h
  -- `psiAbs … a` is a relative cocycle, being `ψ` of a base cycle.
  have hcycψ : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) ((m + 1) + n)
      (psiAbs Z n U τ U (fun x hx => hx) (m + 1) a) = 0 :=
    psiAbs_relDiff_zero Z n U τ U (fun x hx => hx) (m + 1) a hda
  refine ⟨cohomologyClassOf ℤ (baseSSet U) a hda, ?_⟩
  -- The class of `psiAbs … a` is `localThomMap … (class a)` (the interface), and its class agrees
  -- with that of `b` because the two cocycles differ by the differential of `b'`.
  rw [← psiClassHyp_self Z n U τ hψ (m + 1) a hda hcycψ, ← hbcls]
  refine (relClassOf_eq_of_sub_eq_d Z U (m + n) ((m + 1) + n) b
    (psiAbs Z n U τ U (fun x hx => hx) (m + 1) a) b' hb hcycψ ?_).symm
  show b - psiAbsLM Z n U τ U (fun x hx => hx) (m + 1) a = totShiftD Z n U m b'
  rw [← hsplit]
  abel

end

end Work.ThomBordism.ltmCone
