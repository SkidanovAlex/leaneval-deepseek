/-
# `Work.FTS.Top.Main` — the challenge statement from a `BlowupAt` at time `1`

This is the wiring point of node N0: from

* `hα : 0 < α` and
* `B : Work.FTS.Top.BlowupAt α 1` (the audit's interface: an Euler solution of the class of the
  paper's Theorem 1 on `ℝ³ × [0,1)`, whose vorticity blows up at least like `c/(1-t)`),

the *verbatim* conclusion of the challenge statement follows.  The whole proof is the
identification of the fields (`u₀ = B.u · 0`, `p = B.p`, `u = B.u`) and of the last clause with
`Work.FTS.Top.BlowupAt.bkm_divergence_one`, which is literally
`Work.StabilityFar.bkm_divergence_at_one` (fed by the `lower` field and by
`Work.FTS.Top.intervalIntegrable_vortLInf`), i.e. the route of audit §4 (N0).  `Check.lean`
verifies that the conclusion produced here is the challenge's conclusion up to definitional
equality.

The remaining mathematical content of the problem is therefore *exactly* the construction of an
inhabitant of `BlowupAt α 1` (nodes N1–N9 of the audit) together with the rescaling
`Work.FTS.Top.blowupAt_one_of_blowupAt` (node N0, proved).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Top.BKM
import Submission.Work.FTS.Top.Rescale.Blowup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-- **The challenge statement from a blow-up at time `1`.**

The conclusion is the challenge's existential, verbatim: some `β > 0`, a divergence-free odd
`C^{1,β}` datum with `‖ω₀(x)‖ ≤ C/(‖x‖^β + 1)`, and a local solution `(p,u)` on `[0,1)`, odd at
every time, jointly `C^{1,β}` on every strip `ℝ³ × [0,T]` with `T < 1`, whose BKM integral diverges
at `1`. -/
theorem theorem_1_of_blowupAt {α : ℝ≥0} (hα : 0 < (α : ℝ)) (B : BlowupAt α 1) :
    ∃ β > 0, ∃ u₀ : R3 → R3, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ β u₀ ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3,
            (∀ t ∈ Set.Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Set.Ioo 0 1,
                IsContDiffHolderOn ℝ β u.uncurry (Set.univ ×ˢ Set.Icc 0 T)) ∧
                Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖)
                  (𝓝[<] 1) Filter.atTop := by
  have hα' : (0 : ℝ≥0) < α := NNReal.coe_pos.mp hα
  exact ⟨α, hα', (B.u · 0), B.div0, B.odd 0 ⟨le_rfl, B.hT⟩, B.cdh0, B.decay0,
    B.p, B.u, B.odd, B.sol, B.strip, B.bkm_divergence_one⟩

/-- **The challenge statement from a blow-up at an arbitrary time `T > 0`.**  The time rescaling
`Work.FTS.Top.blowupAt_one_of_blowupAt` is applied first. -/
theorem theorem_1_of_blowupAt' {α : ℝ≥0} {T : ℝ} (hα : 0 < (α : ℝ)) (B : BlowupAt α T) :
    ∃ β > 0, ∃ u₀ : R3 → R3, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ β u₀ ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3,
            (∀ t ∈ Set.Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T' ∈ Set.Ioo 0 1,
                IsContDiffHolderOn ℝ β u.uncurry (Set.univ ×ˢ Set.Icc 0 T')) ∧
                Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖)
                  (𝓝[<] 1) Filter.atTop :=
  theorem_1_of_blowupAt hα (blowupAt_one_of_blowupAt B)

end Work.FTS.Top
