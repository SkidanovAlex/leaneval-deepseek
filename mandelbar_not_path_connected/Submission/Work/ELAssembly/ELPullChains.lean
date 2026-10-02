/-
# `ELAssembly` — the two ELPull chains as a source of the pair sequences

`Work.ELAssembly.NestPairs.ofCoLanding` builds the seven pair sequences of the two nests from the
co-landing statements, and those statements are consequences of **ELPull's chains**: the certified
ten-step chain at `z₁` (`Work.ELNest.nest_pair_coLands`, via `coLand_Q`) and the three six-step arm
chains at `b₂` (`Work.ELNest.armPair_coLands`, via `coLand_Z`), both transported to the `Work.EL`
vocabulary.

**What is left as input.**  After `Instantiate.lean` (which derives the ELPull-side data
`hNcan`/`hφcan`/`hψ`/`htop` and the portrait count from `d` and the flower),
`armChainInputs_of` (the three level-`0` arm bases and the angle non-degeneracy, from the root
rays) and `nestChainBase_of` (the level-`0` base of the `z₁`-chain from the C5 chain) — which are
combined into `NestPairs.ofChains` in `Chains.lean` — the only inputs of the two chains are

* `hc : c ∈ M*`, and
* the **`c`-side conditions** `hcv₀`, `hcv`, `hcvA`/`hcvB`/`hcvC` of the certified chains C5, C6,
  C4 — the rational/wake data that the lead's item 4 plans to discharge from
  `RootParabolic.wake` and the certificate (C9/C10).

`ChainInputs` packages exactly those; `Work.ELAssembly.NestPairs.ofChains` (`Chains.lean`) turns
them into the pair data.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELAssembly.Instantiate
import Submission.Work.ELAssembly.coLand_Q
import Submission.Work.ELAssembly.coLand_Z
import Submission.Work.ELNest.z0_notMem_clA
import Submission.Work.ELPull.Cert.Data
import Submission.Work.ELPull.Cert.Basic

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

/-- **The inputs of the two certified co-landing chains** at `c`: the `c`-side conditions of the
chains C5 (`uChain`), C6 (`nestPair`) and C4 (the three arm chains), plus `c ∈ M*`. -/
structure ChainInputs (c : ℂ) (d : Work.EL.RootParabolic c) where
  /-- the parameter lies in the Mandelbar set (the hypothesis of `pb1Top`). -/
  hc : c ∈ Mandelbar
  /-- the `c`-side conditions of the C5 chain at `z₁` (`uPair_lands`), level by level. -/
  hcv₀ : ∀ (i : Fin 10) (Q : Work.ELPull.CoPair (hNcanOf d)),
    Q.a = ((Work.ELPull.Cert.uChain i.succ).1 : ℝ) →
    Q.b = ((Work.ELPull.Cert.uChain i.succ).2 : ℝ) →
    c ∈ Work.ELPull.arcSide (hNcanOf d) Q ((Work.ELPull.Cert.uChainArc i).2 : ℝ)
      ((Work.ELPull.Cert.uChainArc i).1 : ℝ)
  /-- the `c`-side conditions of the C6 chain (`nestPair`), at every level. -/
  hcv : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair (hNcanOf d)), t < 10 →
    Q.a = (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t).1 →
    Q.b = (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t).2 →
    c ∈ Work.ELPull.arcSide (hNcanOf d) Q
      (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t)).2
      (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t)).1
  /-- the `c`-side conditions of the C4 arm-`A` chain, at every level. -/
  hcvA : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair (hNcanOf d)), t < 6 →
    Q.a = (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA
      (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t).1 →
    Q.b = (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA
      (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t).2 →
    c ∈ Work.ELPull.arcSide (hNcanOf d) Q
      (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA
          (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t)).2
      (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA
          (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t)).1
  /-- the `c`-side conditions of the C4 arm-`B` chain, at every level. -/
  hcvB : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair (hNcanOf d)), t < 6 →
    Q.a = (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB
      (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t).1 →
    Q.b = (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB
      (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t).2 →
    c ∈ Work.ELPull.arcSide (hNcanOf d) Q
      (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB
          (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t)).2
      (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB
          (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t)).1
  /-- the `c`-side conditions of the C4 arm-`C` chain, at every level. -/
  hcvC : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair (hNcanOf d)), t < 6 →
    Q.a = (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC
      (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t).1 →
    Q.b = (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC
      (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t).2 →
    c ∈ Work.ELPull.arcSide (hNcanOf d) Q
      (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC
          (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t)).2
      (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t)
        (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC
          (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t)).1

/-- The level-`0` arm-`C` pair is the deep pair `P₄ = uChain 10` of the C5 chain (the two angles
agree, `821/1023` and `326/1023`). -/
theorem uChain10_eq_armC_zero :
    (((Work.ELPull.Cert.uChain 10).1 : ℚ) : ℝ) = Work.ELNest.armC1 0 ∧
      (((Work.ELPull.Cert.uChain 10).2 : ℚ) : ℝ) = Work.ELNest.armC2 0 := by
  constructor
  · rw [Work.ELPull.Cert.uChain_val_10, Work.ELNest.armC1_zero]
    norm_num [Work.ELPull.qq]
  · rw [Work.ELPull.Cert.uChain_val_10]
    norm_num [Work.ELPull.qq, Work.ELNest.armC2, Work.ELNest.contract, Work.ELNest.centred]


end Work.ELAssembly
