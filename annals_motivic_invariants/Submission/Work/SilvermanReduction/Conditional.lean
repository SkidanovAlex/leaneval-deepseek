/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.map_redPoint
import Submission.Work.PointlessTwist.Place

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The class-(a) hook, conditional on the additivity of the reduction map

`Place.lean` produces the place datum `Work.PointlessTwist.ReductionPlace D` from the local-model
data at a place of `L`, using the *proved* additivity `redPoint_add` (in `Add.lean`).  This file
records the same construction with additivity taken as a hypothesis, which isolates exactly what
additivity is responsible for and gives the fallback form of the hook.

Everything is phrased in terms of the twist datum `D : QuinticTwist 𝕜` and its own data
(`D.E`, `D.ext.L`, `D.LPoints`, `D.PL`), so no unfolding of the construction of `D` is needed and
the produced `ReductionPlace` is definitionally the one the PointlessTwist chain consumes.

## Main results

* `redPointHomOfAdd` — the reduction map as a homomorphism, from a proof of additivity.
* `hasReductionPlace_of_localModelData_of_add` — the class-(a) named input, conditional on the
  additivity of the reduction map.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-- **The reduction map as a homomorphism `E(K) →+ Ẽ(k)`**, from a proof of its additivity. -/
noncomputable def redPointHomOfAdd {K : Type} [Field K] [DecidableEq K]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (ResidueField R)]
    {W : Affine K} [W.HasGoodReduction R]
    (hadd : ∀ P Q : WeierstrassCurve.Affine.Point W,
      redPoint R W (P + Q) = redPoint R W P + redPoint R W Q) :
    WeierstrassCurve.Affine.Point W →+ WeierstrassCurve.Affine.Point (W.reduction R) where
  toFun := redPoint R W
  map_zero' := redPoint_zero R
  map_add' := hadd

@[simp]
theorem redPointHomOfAdd_apply {K : Type} [Field K] [DecidableEq K]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (ResidueField R)]
    {W : Affine K} [W.HasGoodReduction R]
    (hadd : ∀ P Q : WeierstrassCurve.Affine.Point W,
      redPoint R W (P + Q) = redPoint R W P + redPoint R W Q)
    (P : WeierstrassCurve.Affine.Point W) :
    redPointHomOfAdd R hadd P = redPoint R W P := rfl

/-- **The local-model data of the class-(a) residual**: a discrete valuation ring `R` inside the
top field `L = D.ext.L` of the twist, at which the curve `D.E` has good reduction, on whose
residue field the generator `σ = D.ext.gen` of `Gal(L/𝕜)` acts trivially, which `σ` preserves,
and under which the marker `D.PL` has non-zero reduction. -/
structure LocalModelData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.PointlessTwist.QuinticTwist 𝕜) where
  /-- The valuation ring of the place (the local model). -/
  R : Type
  [commRing : CommRing R]
  [isDomain : IsDomain R]
  [isDiscreteValuationRing : IsDiscreteValuationRing R]
  [algebra : Algebra R D.ext.L]
  [isFractionRing : IsFractionRing R D.ext.L]
  [decEqResidue : DecidableEq (ResidueField R)]
  /-- **The curve has good reduction at the place.** -/
  [goodReduction : (D.E.baseChange D.ext.L).HasGoodReduction R]
  /-- `σ` preserves the valuation (the place is unique over `𝕜`, the case for the totally ramified
  place `5` of the number-field class). -/
  preservesValuation : PreservesValuation R (D.ext.gen : D.ext.L →+* D.ext.L)
  /-- `σ` acts trivially on the residue field of the place. -/
  trivialOnResidue : TrivialOnResidue R (D.ext.gen : D.ext.L →+* D.ext.L)
  /-- **The marker has non-zero reduction** at the place. -/
  red_PL_ne_zero : redPoint R (D.E.baseChange D.ext.L) D.PL ≠ 0

attribute [instance] LocalModelData.commRing LocalModelData.isDomain
  LocalModelData.isDiscreteValuationRing LocalModelData.algebra LocalModelData.isFractionRing
  LocalModelData.decEqResidue LocalModelData.goodReduction

/-- **The class-(a) named input, conditional on the additivity of the reduction map.** -/
theorem hasReductionPlace_of_localModelData_of_add {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.PointlessTwist.QuinticTwist 𝕜) (h : LocalModelData D)
    (hadd : ∀ P Q : D.LPoints,
      redPoint h.R (D.E.baseChange D.ext.L) (P + Q)
        = redPoint h.R (D.E.baseChange D.ext.L) P
          + redPoint h.R (D.E.baseChange D.ext.L) Q) :
    Work.PointlessTwist.HasReductionPlace D := by
  classical
  refine ⟨{
    G := WeierstrassCurve.Affine.Point ((D.E.baseChange D.ext.L).reduction h.R)
    addCommGroup := inferInstance
    red := redPointHomOfAdd h.R hadd
    red_galMap := ?_
    red_PL_ne_zero := ?_ }⟩
  · intro P
    exact map_redPoint h.R D.E D.ext.gen h.preservesValuation h.trivialOnResidue P
  · simpa only [redPointHomOfAdd_apply] using h.red_PL_ne_zero

end

end Work.SilvermanReduction
