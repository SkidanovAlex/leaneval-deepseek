/-
# `ELAssembly` — the six `c`-side conditions of the two chains, proved at `c₀`

`Work.ELAssembly.ChainInputs c d` collects the six inputs of the two certified ELPull chains that
are *not* the data of the parameter: the `c`-side conditions `hcv₀` (C5, the `u`-chain), `hcv`
(C6, the `z₁`-nest) and `hcvA`/`hcvB`/`hcvC` (C4, the three arm chains), together with
`hc : c ∈ M*`.  This file proves all six from the root-parabolic bundle `d` and the two-ray
portrait `hzero` at `z₁` — following the lead's design `NOTES_LEAD_mandelbar_hcv.md`:

* the side condition at a step is
  `Work.ELAssembly.cv_mem_arcSide_of_W0` applied to the pair `Q` of that step, its unwrapped arc
  `I` (`Work.ELAssembly.isUnwrappedArcOf_nestArc` / `isUnwrappedArcOf_armArcOf` /
  `isUnwrappedArcOf_of_isUnwrappedArcQ`), and the fact that the wake arc `W₀ = (α₁, α₂)` lies in
  the *reversed* arc `(I.2, I.1)`;
* the latter is the rational arithmetic of `nest_W0`, `armA_W0`, `armB_W0`, `armC_W0`, `uChain_W0`;
* `hc` is `Work.FSeed.API.mem_Mandelbar d`.

Hence `ChainInputs` is no longer an input at all, and (via
`Work.ELAssembly.NestPairs.ofChains`) neither is the pair data of the two nests.
-/
import Mathlib
import Submission.Work.ELAssembly.ELPullChains
import Submission.Work.ELAssembly.ArcFacts
import Submission.Work.ELAssembly.cv_mem_arcSide_of_W0
import Submission.Work.ELAssembly.nest_W0
import Submission.Work.ELAssembly.armA_W0
import Submission.Work.ELAssembly.armB_W0
import Submission.Work.ELAssembly.armC_W0
import Submission.Work.ELAssembly.uChain_W0
import Submission.Work.FSeed.API.mem_Mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The six `c`-side conditions of the two chains, at `c₀`.** -/
noncomputable def chainInputs_of {c : ℂ} (d : Work.EL.RootParabolic c)
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)) :
    ChainInputs c d where
  hc := Work.FSeed.API.mem_Mandelbar d
  hcv₀ := fun i Q ha hb =>
    cv_mem_arcSide_of_W0 d hzero Q
      (((Work.ELPull.Cert.uChainArc i).1 : ℚ), ((Work.ELPull.Cert.uChainArc i).2 : ℚ))
      (Work.ELNest.isUnwrappedArcOf_of_isUnwrappedArcQ (P := Work.ELPull.Cert.uChain i.succ)
        (I := Work.ELPull.Cert.uChainArc i) ha hb
        (Work.ELNest.uChainArc_isUnwrappedQ i).1)
      (uChain_W0 i)
  hcv := fun n t Q ht ha hb =>
    cv_mem_arcSide_of_W0 d hzero Q
      (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t))
      (isUnwrappedArcOf_nestArc ha hb (9 - t))
      (nest_W0 (c := c) n t ht)
  hcvA := fun n t Q ht ha hb =>
    cv_mem_arcSide_of_W0 d hzero Q
      (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA
          (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t))
      (isUnwrappedArcOf_armArcOf ha hb Work.ELNest.nearA (5 - t))
      (armA_W0 (c := c) n t ht)
  hcvB := fun n t Q ht ha hb =>
    cv_mem_arcSide_of_W0 d hzero Q
      (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB
          (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t))
      (isUnwrappedArcOf_armArcOf ha hb Work.ELNest.nearB (5 - t))
      (armB_W0 (c := c) n t ht)
  hcvC := fun n t Q ht ha hb =>
    cv_mem_arcSide_of_W0 d hzero Q
      (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC
          (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t))
      (isUnwrappedArcOf_armArcOf ha hb Work.ELNest.nearC (5 - t))
      (armC_W0 (c := c) n t ht)

end Work.ELAssembly
