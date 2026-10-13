/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/MolClassC.lean` — the `ClassC` clauses provided by `J_ε`

The lead's request of 09:50: the elliptic layer's source class
`Work.FTS.EllSol.ClassC α g` now also requires `HkMem α 8 g` and `BdryTraces α 7 g`, and the
`E1` clause "the output lies in `ClassC`" must supply them.  This module assembles, in one place,
the clauses of `ClassC` that the *mollifier* provides for `J_ε f`:

* `norm` (`normTh` is a no-op on `J_ε f`, which already vanishes off the open quadrant),
* `reg` (`C^∞` on the open quadrant, from `Jeps_contDiffOn`),
* `mem` (`HkMem α 8`, from `HkMem_Jeps`),
* `tr` (`BdryTraces α 7`, from `BdryTraces_Jeps`),
* `axis` (`J_ε f = o(z)`, from `axis_Jeps`).

The two remaining clauses of `ClassC` — `fsm` (all-order smoothness of the angular moment
`F_* g`) and `l12` (the zero-mode normalisation `L₁₂ g 0 = 0`) — are *not* properties of `J_ε`
and must be supplied by the caller; `SoftClass` below records exactly the mollifier part, and
`softClass_Jeps` produces it.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.BdryTraces_Jeps
import Submission.Work.FTS.StrongEps.axis_Jeps
import Submission.Work.FTS.StrongEps.Mem10Obligations
import Submission.Work.FTS.StrongEps.thetaTraces_Jeps
import Submission.Work.FTS.EllSol.ClassC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The `ClassC` clauses provided by the mollifier.**  It is `Work.FTS.EllSol.ClassC` without the
two clauses that are not mollifier properties (`fsm`, `l12`), at the levels the elliptic layer
asked for (`HkMem α 8`, `BdryTraces α 7`). -/
structure SoftClass (α : ℝ) (g : Fn) : Prop where
  /-- the angular normalisation is a no-op. -/
  norm : Work.FTS.EllSol.normTh g = g
  /-- `C^∞` on the open quadrant. -/
  reg : Work.FTS.EllipticEst.SmoothOpen g
  /-- `ℋ⁸`-membership. -/
  mem8 : Work.Spaces.HkMem α 8 g
  /-- `ℋ¹⁰`-membership (lead install 2026-10-11: the `mem10` field of `ClassC`). -/
  mem10 : Work.Spaces.HkMem α 10 g
  /-- the boundary traces up to order `7`. -/
  tr7 : Work.FTS.Nonlin.BdryTraces α 7 g
  /-- the axis condition. -/
  axis : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Tendsto (fun z => g z θ / z) (𝓝[>] 0) (𝓝 0)
  /-- θ-traces up to order `10` (lead install R6, 2026-10-11: the `thTr` field of `ClassC`). -/
  thTr : Work.FTS.PhiStar.ThetaTraces α 10 g

/-- `normTh` is a no-op on a profile that already vanishes off the open quadrant. -/
theorem normTh_Jeps (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) :
    Work.FTS.EllSol.normTh (Jeps ρ ε f) = Jeps ρ ε f := by
  funext z θ
  by_cases h : θ ∈ Set.Ioo 0 (π / 2)
  · simp only [Work.FTS.EllSol.normTh, if_pos h]
  · rw [Work.FTS.EllSol.normTh, if_neg h, Jeps_eq_zero]
    exact fun hc => h hc.2

/-- **The mollifier part of `ClassC` for `J_ε f`.**  The hypotheses on `f` are exactly the ones
`J_ε` transfers: `ℋ⁸`-membership, the (uniform) boundary traces up to order `7`, the (uniform)
axis condition, and `C^∞` on the open quadrant. -/
theorem softClass_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hmem : Work.Spaces.HkMem α 8 f)
    (hbdd : ∀ a b : ℕ, a + b ≤ 7 → ∃ M : ℝ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed b a f z θ| ≤ M)
    (hz0 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
        z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε')
    (hzin : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ Z : ℝ, ∀ z : ℝ, Z < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
        z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε')
    (ht0 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (ht1 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < π / 2 → π / 2 - δ < θ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (hax : ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → |f z θ / z| ≤ ε')
    (hloc : LocallyIntegrable (logPull f) volume) :
    SoftClass α (Jeps ρ ε f) :=
  { norm := normTh_Jeps ρ ε f
    reg := Work.FTS.EllipticEst.smoothOpen_iff_forall _ |>.mpr
      (Jeps_contDiffOn ρ hρ hε hloc)
    mem8 := HkMem_Jeps hρ.moll hα hε hsm hmem
    mem10 := HkMem_Jeps_ten_of_eight hρ hα hε hsm hmem
    tr7 := BdryTraces_Jeps hρ hε hsm hbdd hz0 hzin ht0 ht1
    axis := axis_Jeps hρ.moll hε hsm hax
    thTr := thetaTraces_Jeps hρ hα hε hsm ht0 ht1 }

end Work.FTS.StrongEps
