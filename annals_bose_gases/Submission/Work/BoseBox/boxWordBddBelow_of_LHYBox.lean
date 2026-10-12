import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.BoseBox.CNodeDefs
import Submission.Work.BoseBox.paramsOK_fsParams
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.boxWordBddBelow_of_LHYBox` — `BoxWordBddBelow` from the box theorem

`BoxWordBddBelow` (`CNodeDefs.lean`) is the guard that makes
`EBoxAt = ⨅ n, ⨅ Φ, boxWordU / ‖Φ‖²` a *genuine* infimum rather than the junk value
`0`: the box-word quotients are uniformly bounded below over the free particle
number and the trial states.

This file supplies it from FS `thm:LHY-Box` (`LHYBox`), and the argument is
exactly the observation that `LHYBox` *is* such a lower bound: for small `μ` (so
that the diluteness `μ(a v)³` is below the theorem's `ε₀` and FS's parameter
conditions `ParamsOK (paramsAt μ (a v)) (μ(a v)³)` hold — the latter for free by
`paramsOK_fsParams`), the box theorem reads

    sideAt³ · Λ(a v) C η₀ μ · ‖Φ‖² ≤ boxWordU n sideAt μ … Φ,

and dividing by the (strictly positive) norm² gives

    sideAt³ · Λ(a v) C η₀ μ ≤ boxWordU n sideAt μ … Φ / ‖Φ‖²

— a lower bound uniform in `n` and `Φ`, with no use of the *sign* of `Λ`
(any real number is a legitimate lower bound).

The two side conditions of `LHYBox` beyond `μ > 0` are *eventual in* `μ` at `0⁺`:
`μ(a v)³ ≤ ε₀` because `μ ↦ μ(a v)³ → 0` (`a v > 0`), and `ParamsOK` because
`paramsOK_fsParams` holds eventually, and `μ ↦ μ(a v)³` maps `𝓝[>] 0` into
`𝓝[>] 0` (again `a v > 0`).
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox

open Filter
open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option linter.unusedVariables false
set_option autoImplicit false

theorem boxWordBddBelow_of_LHYBox {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {η₀ C : ℝ} (hη₀ : 0 ≤ η₀) (hL : Work.BoseBox.LHYBox v h η₀ C)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseBox.BoxWordBddBelow v h := by
  rcases hL with ⟨ε₀, hε₀, hL⟩
  have hav3 : 0 < (_root_.BoseGases.a v) ^ 3 := pow_pos hav 3
  -- `μ ↦ μ (a v)³` tends to `0` inside `Ioi 0`
  have htend0 : Tendsto (fun μ : ℝ => μ * (_root_.BoseGases.a v) ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun μ : ℝ => μ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using hid.mul tendsto_const_nhds
  have htend : Tendsto (fun μ : ℝ => μ * (_root_.BoseGases.a v) ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend0, by
      filter_upwards [self_mem_nhdsWithin] with μ hμ
      exact mul_pos hμ hav3⟩
  -- the diluteness is small, and FS's parameter conditions hold, eventually
  have hsmall : ∀ᶠ μ in 𝓝[>] (0 : ℝ), μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ :=
    htend0.eventually (eventually_le_nhds hε₀)
  have hpar : ∀ᶠ μ in 𝓝[>] (0 : ℝ),
      ParamsOK (paramsAt μ (_root_.BoseGases.a v)) (μ * (_root_.BoseGases.a v) ^ 3) := by
    simpa [paramsAt] using htend.eventually paramsOK_fsParams
  rw [BoxWordBddBelow]
  filter_upwards [self_mem_nhdsWithin, hsmall, hpar] with μ hμ hsmallμ hparμ
  refine ⟨sideAt μ (_root_.BoseGases.a v) ^ 3 * Lambda (_root_.BoseGases.a v) C η₀ μ, ?_⟩
  intro n Φ
  have hnorm : (0 : ℝ) < norm2N n (sideAt μ (_root_.BoseGases.a v)) (Φ : X n → ℝ) := Φ.sq_pos
  refine (le_div_iff₀ hnorm).mpr ?_
  simpa only [norm2N] using hL μ hμ hsmallμ hparμ n Φ

end Work.BoseBox
