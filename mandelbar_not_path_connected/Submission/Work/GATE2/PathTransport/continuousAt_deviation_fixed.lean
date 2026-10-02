import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.deviation_continuousAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PathTransport

/-- **The deviation is continuous along the dynamical plane at a fixed parameter.**  For a fixed
parameter `c` and a point `z` of its critical domain whose `α`-relative Böttcher deviation is
smaller than `1/4` in absolute value, `Work.GATE.deviation (varphiCrit c) α` is continuous at `z`.

This is item (A2) of the design `NOTES_LEAD_mandelbar_gate2transport.md` §3; it is the
one-parameter specialisation of `Work.GATE2.deviation_continuousAt`. -/
theorem continuousAt_deviation_fixed {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) {α : ℝ}
    (h : |Work.GATE.deviation (Work.Bottcher.varphiCrit c) α z| < 1 / 4) :
    ContinuousAt (Work.GATE.deviation (Work.Bottcher.varphiCrit c) α) z := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hρ'⟩ := Work.GATE2.deviation_continuousAt hz h ε hε
  refine ⟨ρ, hρ, fun z' hz' => ?_⟩
  have hres := hρ' c (by simpa using hρ) z' (by simpa [dist_eq_norm] using hz')
  simpa [Real.dist_eq] using hres

end Work.GATE2.PathTransport
