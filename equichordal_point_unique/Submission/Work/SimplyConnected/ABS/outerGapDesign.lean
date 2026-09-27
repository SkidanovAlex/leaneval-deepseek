import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg

/-!
# Design note for `Work.SimplyConnected.ABS.envelopeOuterGap_dev`

No declaration here; this records the intended proof.

Setting: `c = chartAt ℂ x₀`, `a = c x₀`, `U'' = Ω ∖ chartClosedBall c a s`, `0 < s < ρ`,
`h = limEnvelope U'' f 1` with `0 ≤ f ≤ 1`, `f = 1` on the inner sphere `chartSphere c a s`,
`f = 0` on `frontier Ω`, and `hbar` the barrier hypothesis at `frontier Ω`.

Goal: there is `θ > 0` with `1 - θ ≥ 0` and `h x ≤ 1 - θ` for all `x ∈ U''` with `x ∈ c.source`
and `‖c x - a‖ = ρ`.

Ingredients (all available):
* `dirichletSphereEnvelope_facts` gives: `h` is harmonic on `U''` (hence continuous there),
  `0 ≤ h ≤ 1`, and `h < ε` near `frontier Ω`: for every `ε > 0` there is an open `N ⊇ frontier Ω`
  with `h < ε` on `N ∩ U''`.  (The latter is the only "global" input.)
* The sphere `S := {x ∈ U'' : x ∈ c.source ∧ ‖c x - a‖ = ρ}` is contained in `U''` and in the
  compact set `chartClosedBall c a ρ ⊆ Ω`, hence is compact; `h` is continuous there, so
  `sup_S h` is attained.

Argument: suppose `sup_S h = 1`, i.e. `h y = 1` for some `y ∈ S`.  By the strong maximum principle
for the subharmonic function `h` on the open set `U''` (`Submission.SubharmonicOnXAt.eqOn_of_le`),
`h ≡ 1` on a neighbourhood of `y`, so (as `{h = 1}` is open in `U''` and relatively closed by
continuity) `h ≡ 1` on the connected component `C` of `y` in `U''`.

Now `C` meets the neighbourhood `N` of `frontier Ω`: otherwise `C̄ ∩ frontier Ω = ∅`, and then
`C ∪ chartClosedBall c a s` is clopen in `Ω` (closed because `∂C ⊆ frontier U'' ⊆ frontier Ω ∪ S_s`
and `frontier Ω ⊆ C̄`; open because the punctured chart ball around any point of the sphere
`S_s = {r = s}` is locally a half-disc and hence connected, so it lies in a single component).  As
`Ω` is connected, `C ∪ chartClosedBall c a s = Ω`, so `C = U''` and `C̄ ⊇ frontier Ω`, contradicting
`C ∩ N = ∅` (with `N ⊇ frontier Ω` open, `N` meets the closure of any set whose closure meets
`frontier Ω`).

So `C ∩ N ≠ ∅` and hence `h = 1` on `C ∩ N`, contradicting `h < 1/2` on `N ∩ U''` (the decay
property with `ε = 1/2`).  Therefore `h < 1` on `S`, and by compactness of `S` and continuity of
`h` there is a uniform `θ > 0` with `h ≤ 1 - θ` on `S`; since `h ≤ 1` we may take `θ ≤ 1`.

Useful lemmas: `Submission.SubharmonicOnXAt.eqOn_of_le`, `isOpen_iff_mem_nhds`,
`frontier_subset_closure`, `IsCompact.exists_forall_le`/`IsCompact.exists_isMaxOn`,
`Metric.sphere`, `Submission.mem_chartSphere`, `Submission.isCompact_chartClosedBall`.
-/
