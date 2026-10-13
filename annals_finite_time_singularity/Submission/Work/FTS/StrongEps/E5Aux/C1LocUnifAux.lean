/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Aux/C1LocUnifAux.lean` — the CLM `(a, L) ↦ ((x,y) ↦ a x + L y)`

The joint `C¹`-statement `c1_of_locUnif_slots_lip` needs the Fréchet derivative of a map
`(x, y) ↦ f (x, y)` on `ℝ × E` assembled from its `x`-derivative (a number, `g₁`) and its
`y`-derivative (a continuous linear functional, `g₂`).  The candidate derivative is therefore
the continuous linear map

`clmHead E a L : (ℝ × E) →L[ℝ] ℝ`,  `clmHead E a L (x, y) = a * x + L y`.

This file provides that map together with its basic API:
`clmPre`/`clmHeadL` (the constructors, which are continuous linear maps in `(a,L)` — this is
what makes the *continuity* of the assembled derivative automatic), `clmHead` (the evaluation),
`clmHead_apply`, and the one-dimensional identification with the pair-API
`Work.FTS.StrongEps.E5Aux.clmPair` of `clmPairAPI.lean`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Submission.Work.FTS.StrongEps.E5Aux.clmPairAPI

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- Precomposition with the second projection, as a continuous linear map in the first
argument: `L ↦ L.comp (Prod.snd)`. -/
noncomputable def clmPre (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E →L[ℝ] ℝ) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (ℝ × E) E ℝ).flip (ContinuousLinearMap.snd ℝ ℝ E)

theorem clmPre_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) :
    clmPre E L = L.comp (ContinuousLinearMap.snd ℝ ℝ E) := rfl

/-- The continuous linear map `(a, L) ↦ ((x,y) ↦ a * x + L y)`. -/
noncomputable def clmHeadL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (ℝ × (E →L[ℝ] ℝ)) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.smulRightL ℝ (ℝ × E) ℝ (ContinuousLinearMap.fst ℝ ℝ E)).comp
      (ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] ℝ)))
    + ((clmPre E).comp (ContinuousLinearMap.snd ℝ ℝ (E →L[ℝ] ℝ)))

/-- The continuous linear map `(x, y) ↦ a * x + L y`. -/
noncomputable def clmHead (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (L : E →L[ℝ] ℝ) : (ℝ × E) →L[ℝ] ℝ := clmHeadL E (a, L)

theorem clmHead_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a x : ℝ) (L : E →L[ℝ] ℝ) (y : E) :
    clmHead E a L (x, y) = a * x + L y := by
  simp only [clmHead, clmHeadL, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    clmPre]
  show x * a + L y = a * x + L y
  ring

theorem clmHead_fst (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a x : ℝ) (L : E →L[ℝ] ℝ) : clmHead E a L (x, 0) = a * x := by
  rw [clmHead_apply, map_zero, add_zero]

/-- In the one-dimensional case `clmHead` is the pair-API `clmPair`. -/
theorem clmHead_eq_clmPair (a b : ℝ) :
    clmHead ℝ a (b • (1 : ℝ →L[ℝ] ℝ)) = clmPair (a, b) := by
  refine clm_eq_of_fst_snd ?_ ?_
  · rw [clmHead_apply, clmPair_fst]
    simp
  · rw [clmHead_apply, clmPair_snd]
    simp

end Work.FTS.StrongEps.E5Aux
