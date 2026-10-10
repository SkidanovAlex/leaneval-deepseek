/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TwistModel.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The base change of `ℙⁿ` along a field extension

`GeometricallyIntegral (projectiveSpaceToSpec 𝕜 n)` — the single remaining conjunct of
`Work.PointlessIndexFive.ProjectiveModelGap 𝕜 n` (`Work.Twist.ProjModel.projectiveModelGap_iff`)
— unfolds to: for every field extension `K/𝕜`, the base change `ℙⁿ_𝕜 ×_{Spec 𝕜} Spec K` is
integral.  This file sets up that base change and its charts.

The base change is covered by the preimages `chartPullbackOpen 𝕜 n K i` of the standard charts
`D₊(Xᵢ)` of `ℙⁿ`, and each of these is, after base change, the affine space `𝔸ⁿ_K`:

  `chartPullbackIso 𝕜 n K i : chartPullback 𝕜 n K i ≅ Spec K[y₁,…,yₙ]`

(`Work.TwistModel.chartPullbackIso`, proved in the sibling module of the same name).  Since
`Spec K[y₁,…,yₙ]` is an integral affine scheme and the charts cover the base change with pairwise
non-empty intersections, `GeometricallyIntegral` follows; that assembly is
`Work.TwistModel.isIntegral_projectiveSpaceBaseChange`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace Work.TwistModel

noncomputable section

/-- **The base change of `ℙⁿ_𝕜` along a field extension `K/𝕜`.** -/
noncomputable def projectiveSpaceBaseChange (𝕜 : Type) [Field 𝕜] (n : ℕ) (K : Type) [Field K]
    [Algebra 𝕜 K] : Scheme :=
  pullback (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
    (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K)))

/-- **The chart `D₊(X_i)` inside the base change of `ℙⁿ`**: the preimage of the standard chart
under the projection `ℙⁿ_K ⟶ ℙⁿ`. -/
noncomputable def chartPullbackOpen (𝕜 : Type) [Field 𝕜] (n : ℕ) (K : Type) [Field K]
    [Algebra 𝕜 K] (i : Fin (n + 1)) : (projectiveSpaceBaseChange 𝕜 n K).Opens :=
  (TopologicalSpace.Opens.map (pullback.fst
      (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K)))).base).obj
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) (MvPolynomial.X i))

/-- The chart of the base change, as a scheme: `𝔸ⁿ_K` by `chartPullbackIso`. -/
noncomputable def chartPullback (𝕜 : Type) [Field 𝕜] (n : ℕ) (K : Type) [Field K] [Algebra 𝕜 K]
    (i : Fin (n + 1)) : Scheme :=
  Scheme.Opens.toScheme (chartPullbackOpen 𝕜 n K i)

end

end Work.TwistModel
