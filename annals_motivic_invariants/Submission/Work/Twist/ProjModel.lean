/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Twist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Twist.Defs
import Submission.Work.Twist.away_chart_mvPolynomial
import Submission.Work.Twist.away_chart_mvPolynomial_X
import Submission.Work.Twist.topologicalKrullDim_projectiveSpace
import Submission.Work.Twist.smooth_projectiveSpaceToSpec
import Submission.Work.Twist.isIntegral_projectiveSpace
import Submission.Work.Twist.curveModel_projectiveSpace_one

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The projective model layer

The lead's brief for this area says that the projective-model layer (`ℙⁿ` as a `Variety`,
properness, `ProjectiveModelGap`) "is BUILT in `PointlessIndexFive` — reuse it".  What was in fact
built there is properness, separatedness, finite type and quasicompactness of
`projectiveSpaceToSpec 𝕜 n` (`Work.PointlessIndexFive.Model`); the three *missing* facts were named
`ProjectiveModelGap 𝕜 n`:

  `Smooth (projectiveSpaceToSpec 𝕜 n) ∧ GeometricallyIntegral (projectiveSpaceToSpec 𝕜 n) ∧
    topologicalKrullDim (projectiveSpace 𝕜 n) = n`.

This module records what is now available, all of it proved in the sibling modules of this
directory:

* `Twist.away_chart_mvPolynomial` / `Twist.away_chart_mvPolynomial_X` — **the chart ring**: the
  degree-zero part of the homogeneous localization of `𝕜[X₀,…,Xₙ]` at `X_i` is a polynomial ring
  `𝕜[y₁,…,yₙ]` (via the dehomogenisation `Twist.chartDhom` and the map `Twist.chartPsi`).  This is
  the algebra input for every other item, and the one that was missing from Mathlib;
* `Twist.topologicalKrullDim_projectiveSpace` — `topologicalKrullDim (ℙⁿ_𝕜) = n`;
* `Twist.smooth_projectiveSpaceToSpec` — `ℙⁿ_𝕜` is smooth over `Spec 𝕜`;
* `Twist.isIntegral_projectiveSpace` — `ℙⁿ_𝕜` is integral (irreducible and reduced), with the
  reusable general facts `Twist.irreducibleSpace_proj_of_isDomain` and
  `Twist.isReduced_proj_of_isReduced` for `Proj` of any graded ring.

Consequently `ProjectiveModelGap 𝕜 n` reduces to its **third** conjunct,
`GeometricallyIntegral (projectiveSpaceToSpec 𝕜 n)` (`projectiveModelGap_iff`), and
`Variety 𝕜 (ℙⁿ)` is available unconditionally (`variety_projectiveSpace_uncond`), whereas
`Work.PointlessIndexFive.variety_projectiveSpace` had to assume `GeometricallyIntegral`.

**What is still missing, and why it matters for the twist.**  `GeometricallyIntegral` for `ℙⁿ`
requires the integrality of `ℙⁿ ×_{Spec 𝕜} Spec K` for every field extension `K/𝕜`: over `K` one
would repeat the cover argument above, using that the base change of `Proj` of the standard graded
ring is `Proj` of the graded ring base-changed to `K` — a compatibility that Mathlib does not have.
For the twist of a quintic twist (`TwistRealization`), much more is needed; see `NOTES.md` §4.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open CategoryTheory AlgebraicGeometry
open Work.Twist

namespace Work.Twist

noncomputable section

/-- **The remaining gap of the projective model layer.**  After the chart-ring computation and the
dimension, smoothness and integrality of `ℙⁿ`, the only conjunct of
`Work.PointlessIndexFive.ProjectiveModelGap 𝕜 n` that is still open is the geometric integrality. -/
theorem projectiveModelGap_iff {𝕜 : Type} [Field 𝕜] (n : ℕ) :
    Work.PointlessIndexFive.ProjectiveModelGap 𝕜 n ↔
      GeometricallyIntegral (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n) := by
  simp only [Work.PointlessIndexFive.ProjectiveModelGap, smooth_projectiveSpaceToSpec 𝕜 n,
    topologicalKrullDim_projectiveSpace 𝕜 n, true_and, and_true]

/-- **`ℙⁿ_𝕜` is a variety over `𝕜`**, unconditionally: this is
`Work.PointlessIndexFive.variety_projectiveSpace` with its hypothesis discharged by
`Twist.isIntegral_projectiveSpace`. -/
noncomputable def variety_projectiveSpace_uncond (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    MotivicInvariants.Variety 𝕜 (Work.PointlessIndexFive.projectiveSpace 𝕜 n) := by
  haveI : IsIntegral (Work.PointlessIndexFive.projectiveSpace 𝕜 n) :=
    isIntegral_projectiveSpace 𝕜 n
  haveI : IsSeparated
      (Work.PointlessIndexFive.projectiveSpace 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) :=
    Work.PointlessIndexFive.isSeparated_projectiveSpaceToSpec 𝕜 n
  haveI : LocallyOfFiniteType
      (Work.PointlessIndexFive.projectiveSpace 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) :=
    Work.PointlessIndexFive.locallyOfFiniteType_projectiveSpaceToSpec 𝕜 n
  haveI : QuasiCompact
      (Work.PointlessIndexFive.projectiveSpace 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) :=
    Work.PointlessIndexFive.quasiCompact_projectiveSpaceToSpec 𝕜 n
  exact ⟨⟩

/-- **A `CurveModel` for `ℙ¹_𝕜` from the one remaining model-layer gap.**  This is
`curveModel_projectiveSpace_one` with its `Smooth` and dimension hypotheses now discharged, so the
only input left is `GeometricallyIntegral (ℙ¹_𝕜)`.  (Recall that `ℙ¹` has rational points, so this
is *not* the `C(𝕜) = ∅` configuration: it is the model-layer half of it.) -/
theorem curveModel_projectiveSpace_one_of_geometricallyIntegral (𝕜 : Type) [Field 𝕜]
    (hG : GeometricallyIntegral (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 1)) :
    Nonempty (CurveModel 𝕜) :=
  curveModel_projectiveSpace_one 𝕜 (smooth_projectiveSpaceToSpec 𝕜 1) hG
    (topologicalKrullDim_projectiveSpace 𝕜 1)

end

end Work.Twist
