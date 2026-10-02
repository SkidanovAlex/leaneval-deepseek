/-
# `ELAssembly` — the pair data from the two certified chains, with the derived inputs

`Work.ELAssembly.NestPairs.ofChains` builds the seven pair sequences of the two nests from
`Work.ELAssembly.ChainInputs` (the `c`-side conditions of the three ELPull chains, C5, C6, C4),
using

* `Instantiate.lean` for the ELPull-side Böttcher data and the portrait count,
* `armChainInputs_of` for the three level-`0` arm bases and the angle non-degeneracy,
* `nestChainBase_of` for the level-`0` base of the `z₁`-chain,
* `coLand_Q` / `coLand_Z` for the transport of ELPull's chains to the `Work.EL` vocabulary.

This file is separate from `ELPullChains.lean` (which declares `ChainInputs`) because the two
lemmas above are proved in files that import it.
-/
import Mathlib
import Submission.Work.ELAssembly.ELPullChains
import Submission.Work.ELAssembly.armChainInputs_of
import Submission.Work.ELAssembly.nestChainBase_of

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

/-- **The pair data of the two nests from the two certified ELPull chains.**  All the data other
than the `c`-side conditions is derived: the ELPull-side Böttcher data by `Instantiate.lean`, the
level-`0` bases and the angle non-degeneracy by `armChainInputs_of`, and the level-`0` base of the
`z₁`-chain by `nestChainBase_of` (from the C5 side conditions and the deep pair `P₄`). -/
noncomputable def NestPairs.ofChains {c : ℂ} {d : Work.EL.RootParabolic c}
    (E : ChainInputs c d) : NestPairs d := by
  obtain ⟨⟨hA, hB, hC⟩, hndA, hndB, hndC⟩ := armChainInputs_of d
  -- the deep pair `P₄ = uChain 10` co-lands: it is the level-`0` arm-`C` pair
  have hP4 : ∃ y : ℂ,
      Work.ELPull.LandsN (hNcanOf d) (((Work.ELPull.Cert.uChain 10).1 : ℚ) : ℝ) y ∧
      Work.ELPull.LandsN (hNcanOf d) (((Work.ELPull.Cert.uChain 10).2 : ℚ) : ℝ) y := by
    obtain ⟨y, hy, hy'⟩ := hC
    rw [uChain10_eq_armC_zero.1, uChain10_eq_armC_zero.2]
    exact ⟨y, hy, hy'⟩
  have hbase := nestChainBase_of d E.hc hP4 E.hcv₀
  have hZ := coLand_Z E.hc d (hNcanOf d) (hφcanOf d) (hψOf d) (htopOf (hNcanOf d))
    hA hB hC hndA hndB hndC E.hcvA E.hcvB E.hcvC
  exact NestPairs.ofCoLanding d
    (coLand_Q E.hc d (hNcanOf d) (hφcanOf d) (hψOf d) (htopOf (hNcanOf d)) hbase E.hcv)
    (fun n => hZ.1 n) (fun n => hZ.2.1 n) (fun n => hZ.2.2 n)

end Work.ELAssembly
