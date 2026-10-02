import Mathlib
import Submission.Work.ThomBordism.Grassmann.Probe2.p1RatNeZeroAssembly
import Submission.Work.ThomBordism.Grassmann.Probe2.probeP1Base

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# `Work.ThomBordism.Grassmann.p1RatNeZero`

`p1Rat k m = 1 ⊗ p₁(γ_{k,m}) ≠ 0` in `H⁴(G̃r_k(ℝ^{k+m}); ℚ)` for `k, m ≥ 4`.

The proof is assembled from three sorry-free inputs:

* `Work.ThomBordism.Grassmann.probeP1Base` — the geometric base case: the probe
  `σ : ℂP² → G̃r₂(ℝ⁶)`, `[v] ↦ ℝv + ℝiv`, whose pullback of the tautological bundle is isomorphic to
  `zStd`, the realification of the tautological line bundle of `ℂP²`
  (`p1Rat_ne_zero_of_probe 2 4` then rationalises, using `chernReducedRatNeZero`);
* `p1RatNeZero_of_base` — the stabilisation of the base case `p1Rat 2 4 ≠ 0` to every `k, m ≥ 4`
  along the one-step maps `CohMap_p1_addLine` / `CohMap_p1_incl` of the oriented Grassmannian;
* `pontryagin1_zStd` / `chernReducedRatNeZero` — `p₁(zStd) = -c₂(O(1) ⊕ O(-1)) ≠ 0` rationally.

(The design of the probe and of the gauge that identifies `σ*γ` with `zStd` is recorded in
`Submission/Work/ThomBordism/Grassmann/PROBE_GAUGE_NOTES.md`.)
-/

namespace Work.ThomBordism.Grassmann.Probe2

/-- **The base case `(k, m) = (2, 4)`**: the probe `ℂP² → G̃r₂(ℝ⁶)` pulls `p₁(γ)` back to `p₁(zStd)`,
so `p1Rat 2 4 ≠ 0`. -/
theorem p1Rat_two_four_ne_zero : Work.ThomBordism.Grassmann.p1Rat 2 4 ≠ 0 :=
  p1Rat_ne_zero_of_probe 2 4 probeP1Base

/-- **`p₁` of the tautological oriented bundle over `G̃r_k(ℝ^{k+m})` is non-zero rationally** for
`k, m ≥ 4`: the base case `(2,4)` stabilised along the Grassmannian. -/
theorem p1RatNeZero (k m : ℕ) (hk : 4 ≤ k) (hm : 4 ≤ m) :
    Work.ThomBordism.Grassmann.p1Rat k m ≠ 0 :=
  p1RatNeZero_of_base p1Rat_two_four_ne_zero k m hk hm

end Work.ThomBordism.Grassmann.Probe2
