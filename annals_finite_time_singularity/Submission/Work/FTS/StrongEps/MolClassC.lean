import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.thetaTraces_Jeps
import Submission.Work.FTS.StrongPersist.L3DataFinal
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_LocDatum3a.L12_Jeps_locG6
import Submission.Work.FTS_MuLamOK.Rows.Rl0Open
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLimDbdFixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option linter.unusedVariables false

/-! ## The mechanism at the right endpoint -/


/-! ## The core estimate

The whole analytic content of `EpsLimDbd` is here: it needs the equation *only* through the
identification `gdot g τ = rhsFun α Φs E g τ` on the open quadrant, at the fake times `τ` for
which the conclusion is asserted. -/


/-! ## Replacement 1 — honest derivative at every `τ > 0` (hypothesis within `Set.Ici 0`) -/


/-! ## Replacement 2 — the given hypothesis, conclusion for `τ < T` -/


/-! ## Replacement 3 — the given hypotheses plus the *missing* endpoint identity

This isolates exactly the ingredient that the requested statement is missing: the identification
`gdot g T = rhsFun α Φs E g T` on the open quadrant, at the single right endpoint `τ = T` (which
`heqT`'s within-`Set.Icc 0 T` derivative fails to provide — see
`deriv_eq_of_hasDerivWithinAt_rightEndpoint`).  If the caller obtains that identity from the
construction of the limit family (e.g. as the `τ → T⁻` limit of the equation along the pieces, or
from honest differentiability at `T`), the requested conclusion — including `τ = T` — follows. -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.MolClassC =====
section

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
end
end
