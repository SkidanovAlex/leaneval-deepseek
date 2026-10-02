/-
# `ELAssembly` — the `IsUnwrappedArcOf` facts of the two certified chains

The side conditions `hcv` of the two ELPull chains are stated for a pair `Q` and an *unwrapped
arc* `I` of it (`Work.ELPull.IsUnwrappedArcOf Q I`).  For the arcs produced by the two chains the
fact is a case split: `Work.ELNest.nestArc j p` and `Work.ELNest.armArcOf near j p` are literally
one of the two unwrapped arcs of the pair `p`.  This file records the two transfers; the third
(the `u`-chain) is `Work.ELNest.isUnwrappedArcOf_of_isUnwrappedArcQ` applied to
`Work.ELNest.uChainArc_isUnwrappedQ`.
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELNest.uPair_lands

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

/-- The arcs of the `z₁`-chain are unwrapped arcs of the pair they are read against. -/
theorem isUnwrappedArcOf_nestArc {c : ℂ} {hN : Work.ELPull.DynB c}
    {Q : Work.ELPull.CoPair hN} {p : ℝ × ℝ} (ha : Q.a = p.1) (hb : Q.b = p.2) (j : ℕ) :
    Work.ELPull.IsUnwrappedArcOf Q (Work.ELNest.nestArc j p) := by
  unfold Work.ELNest.nestArc Work.ELPull.IsUnwrappedArcOf
  by_cases h : j % 5 = 3 ∨ j % 5 = 4
  · rw [if_pos h]
    exact Or.inr ⟨hb.symm, by rw [ha, hb, Work.EL.arcLen, Work.ELPull.arcLen]⟩
  · rw [if_neg h]
    exact Or.inl ⟨ha.symm, by rw [ha, hb, Work.EL.arcLen, Work.ELPull.arcLen]⟩

/-- The arcs of the three arm chains are unwrapped arcs of the pair they are read against. -/
theorem isUnwrappedArcOf_armArcOf {c : ℂ} {hN : Work.ELPull.DynB c}
    {Q : Work.ELPull.CoPair hN} {p : ℝ × ℝ} (ha : Q.a = p.1) (hb : Q.b = p.2)
    (near : ℕ → Bool) (j : ℕ) :
    Work.ELPull.IsUnwrappedArcOf Q (Work.ELNest.armArcOf near j p) := by
  unfold Work.ELNest.armArcOf Work.ELPull.IsUnwrappedArcOf
  by_cases h : near j
  · rw [if_pos h]
    exact Or.inr ⟨hb.symm, by rw [ha, hb, Work.EL.arcLen, Work.ELPull.arcLen]⟩
  · rw [if_neg h]
    exact Or.inl ⟨ha.symm, by rw [ha, hb, Work.EL.arcLen, Work.ELPull.arcLen]⟩

end Work.ELAssembly
