/-
# GATE2 — the real Écalle height of the entry point is a *theorem*, not a hypothesis

PL's `PrincipalParam` needs the normalisation `hv`: some iterate of the critical value `c₀` under
`F = (T_{c₀})^10` lies in the petal and has Fatou coordinate exactly `v + N`, where
`v = (φa (entryPt P M.nIn c₀)).re − M.nIn`.  The earlier drives carried this as a hypothesis
(`Work.GATE2.twoSided_trans_of_lockstepAll`, `Work.GATE2.twoSided_of_leakOnRay`, …).

It is in fact a **theorem**: `entryPt P M.nIn c₀` *is* `F^[M.nIn] c₀` (definitionally, since
`entryPt P n c = (Ft c)^[n] c` and `Ft c = Work.EL.F c`), it lies in `Pa = fl.Pa` by `hentry₀`
and the identification `Pa = fl.Pa`, and the vanishing of the critical height `hcrit` says exactly
that its Fatou coordinate is the real number `v + M.nIn = (φa (entryPt)).re`.  So `N := M.nIn`
witnesses `hv`.
-/
import Submission.Work.PARIMPL.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **`hv` is a theorem.**  The entry time `M.nIn` is the witness: the entry point of the critical
orbit is `F^[M.nIn] c₀` by definition, it is in the petal `fl.Pa` (`hentry₀` + `Pa = fl.Pa`), and
its Fatou coordinate is real (`hcrit`), so it equals `(v + M.nIn : ℂ)`. -/
theorem hv_of_crit {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0) :
    ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) =
        ((((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) + N : ℝ) : ℂ) := by
  have hpt : (Work.EL.F c₀)^[M.nIn] c₀ = Work.PARIMPL.entryPt P M.nIn c₀ := rfl
  refine ⟨M.nIn, ?_, ?_⟩
  · show (Work.EL.F c₀)^[M.nIn] c₀ ∈ fl.Pa
    rw [hpt, ← hPaeq]
    exact hentry₀
  · show fl.φa ((Work.EL.F c₀)^[M.nIn] c₀) =
      ((((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ) + (M.nIn : ℝ)) : ℝ) : ℂ)
    rw [hpt, ← hφa_eq]
    have hcast : ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ) + (M.nIn : ℝ) : ℝ)
        = (φa (Work.PARIMPL.entryPt P M.nIn c₀)).re := by ring
    rw [hcast]
    refine Complex.ext (by simp) ?_
    simpa using hcrit

end Work.GATE2
