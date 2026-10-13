import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.EpsGdotThird
import Submission.Work.FTS.StrongEps.EpsZero.Bridge.tendsto_pz_zero_of_trace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsZero.Bridge

/-- **The boundary/trace facts for a `ClassC` datum that vanishes off the open quadrant.**

For `f` in the linear elliptic class `Work.FTS.ClassC.ClassC α` (`C^∞` on the open quadrant
`(0,∞) × (0,π/2)`, with the weighted boundary traces `BdryTraces` of all slots `a+b ≤ 6`, the
`ℋ⁷`/`ℋ⁸` integrability `HkMem`, the all-order smoothness of the angular moment, the axis
condition `f z θ / z → 0` at `z → 0⁺` and the vanishing `L₁₂` mode) which is supported in the open
quadrant, the radial slices and the radial derivative slices have the following regular behaviour,
for **every** angle `θ ∈ Iθ = [0, π/2]`, endpoints included:

* `s ↦ ∂_z f (s, θ)` extends continuously to `[0, ∞)` (the first conjunct);
* `s ↦ f (s, θ)` tends to `0` at `z → +∞` (the second conjunct);
* `s ↦ f (s, θ)` is differentiable on `(0,∞)` with derivative `Work.Spaces.pz f z θ`
  (the third conjunct).

The proof has two parts.

* The last two clauses, and the differentiability, are the sibling
  `Work.FTS.StrongEps.EpsZero.slice_facts_of_classC` (`SmoothOpen` + `BdryTraces α 6` +
  support), which produces them in the order
  `HasDerivAt, ContinuousOn f, Tendsto f atTop` — only the order of the conjuncts differs.

* The remaining clause (continuity of the *derivative* slice `∂_z f (·, θ)` on `[0,∞)`) is not
  part of that sibling: `f` itself vanishes on the outer radial half-line, so for
  `θ ∉ (0, π/2)` the slice `∂_z f (·, θ)` is identically zero, while for `θ ∈ (0, π/2)`
  * `SmoothOpen.pz` gives continuity on the open half-line `(0,∞)`;
  * the `BdryTraces` slot `(a,b) = (0,1)` — that is, the trace of `D_z f = z ∂_z f` — reads
    `z * (D_z f (z,θ) * w z)^2 → 0` as `z → 0⁺`, which for `z > 0` is
    `(∂_z f)^2 * (1+z)^4 / z → 0`; since `z ≤ (1+z)^4` it dominates `(∂_z f)^2`, so
    `∂_z f (z,θ) → 0` at `z → 0⁺`.  This is precisely the delegated lemma
    `Work.FTS.StrongEps.EpsZero.Bridge.tendsto_pz_zero_of_trace`;
  * the `ClassC` axis condition `f z θ / z → 0` (via `pz_zero_of_tendsto_div`) gives
    `∂_z f (0, θ) = 0`, the value at the endpoint, so the limit along `𝓝[>] 0` upgrades to a limit
    along `𝓝[≥] 0` and continuity on `[0,∞)` follows. -/
theorem BdryClassC {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0) :
    (∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s : ℝ => Work.Spaces.pz f s θ) (Set.Ici 0)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s : ℝ => f s θ) Filter.atTop (nhds 0)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s : ℝ => f s θ) (Work.Spaces.pz f z θ) z) := by
  -- the two decay clauses and differentiability come from the sibling slice fact
  obtain ⟨hdiff, -, hdec⟩ :=
    Work.FTS.StrongEps.EpsZero.slice_facts_of_classC hC.reg hC.tr hzero
  refine ⟨?_, hdec, hdiff⟩
  intro θ hθ
  by_cases hI : θ ∈ Set.Ioo 0 (π / 2)
  · -- interior angle: the boundary trace of `D_z f` at `z = 0` plus the axis condition
    have htr : Filter.Tendsto
        (fun z : ℝ => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
      ((hC.tr 0 1 (by norm_num)).1 θ hI).1
    have hlim : Filter.Tendsto (fun s : ℝ => Work.Spaces.pz f s θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
      tendsto_pz_zero_of_trace htr
    have h0 : Work.Spaces.pz f 0 θ = 0 :=
      Work.FTS.StrongEps.pz_zero_of_tendsto_div hI (fun z hz => hzero z θ hz) (hC.axis θ hI)
    exact Work.FTS.StrongEps.EpsZero.continuousOn_Ici_of_continuousOn_Ioi_of_tendsto
      (hC.reg.pz.curry_z hI).continuousOn h0
      (Work.FTS.StrongEps.EpsZero.tendsto_Ici_of_tendsto_Ioi hlim h0)
  · -- outside the open angle interval the whole slice vanishes identically, hence so does `∂_z f`
    have hslice : (fun s : ℝ => f s θ) = fun _ => (0 : ℝ) :=
      funext (fun s => hzero s θ (fun hc => hI hc.2))
    have hzero_pz : (fun s : ℝ => Work.Spaces.pz f s θ) = fun _ => (0 : ℝ) := by
      funext s
      show deriv (fun z : ℝ => f z θ) s = 0
      rw [hslice, deriv_const]
    rw [hzero_pz]
    exact continuousOn_const

end Work.FTS.StrongEps.EpsZero.Bridge
