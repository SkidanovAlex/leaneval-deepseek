import Mathlib
import Submission.Work.OddBound.PiExtChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Design: the index transfer — a negative-definite Dirichlet plane forces a negative-definite
plane for the polygon energy

Delegated as `Work.OddBound.indexTransfer.hasNegDefPlane_of_negativeDirichletIndex`.

## Context

`Work.OddBound.MinimaxExtraction` is assembled as follows.  The mountain pass
(`Work.OddBound.mountainPass.exists_critical_index_le_one_manifold`, the module
`design/MountainPassManifold2.lean`) produces a critical polygon `w ∈ Fin (N-1) → M` of the polygon
energy `gonEnergy p` at which there is **no** negative-definite 2-plane (`¬ HasNegDefPlane`); the
first variation (`Work.OddBound.polygon.isCritical_gonEnergy_geodesic`, PROVED) turns `w` into a
closed unit-speed geodesic `c : ℝ → M` of length `T = √(2 · gonEnergy p w)` with
`c (i*T/N) = gonVert p w i`.  The index transfer is the step that closes the loop: it shows that a
**negative-definite plane of Dirichlet fields along `c`** produces a negative-definite 2-plane for
`gonEnergy` at `w`.  Since the mountain pass says there is none, no such Dirichlet plane exists —
that is exactly the conclusion `DirichletIndexLeOne` of the minimax.

## The statement

```lean
theorem hasNegDefPlane_of_negativeDirichletIndex
    (hmet) (htor) {T} (hT : 0 < T) {p} {c}
    (hcsm : ContMDiff 𝓘(ℝ) I ∞ c) (hcgeo : ∀ t, IsGeodesicAt cov c t)
    (hcne : ∀ t, curveVelocity c t ≠ 0) (hcsp : ∀ t ∈ Icc 0 T, curveSpeed c t = 1)
    (hc0 : c 0 = p) (hcT : c T = p)
    {N} (hN : 3 ≤ N) {w} (hsample : ∀ i : Fin (N+1), c (i*T/N) = gonVert p w i)
    {x} (hwsrc : w ∈ (piExtChart x).source)
    [ChartedSpace ((Fin (N-1)) → E) ((Fin (N-1)) → M)]
    (he : piExtChart x ∈ atlas _ _)
    (hC2 : ContDiffAt ℝ 2 (fun u => gonEnergy p ((piExtChart x).symm u)) ((piExtChart x) w))
    (hF0 : fderiv ℝ (fun u => gonEnergy p ((piExtChart x).symm u)) ((piExtChart x) w) = 0)
    {V W} (smooth Dirichlet fields, vanishing at `0` and `T`, smooth on `Icc (-1) (T+1)`)
    (hneg : ∀ (a,b) ≠ 0, ∫₀^T idxAlong (c, a•V + b•W, ∇(a•V + b•W)) < 0) :
    HasNegDefPlane ((Fin (N-1)) → E) (gonEnergy p) w
```

## Proof plan

Write `H' := (Fin (N-1)) → E`, `q := (a,b) : ℝ × ℝ`, and put

* `z q : Fin (N-1) → M`,  `z q i := GExp (c (t (i+1))) (q.1 • V (t (i+1)) + q.2 • W (t (i+1)))`
  with `t m := m * T / N`;
* `Φ q : ℝ → M`,  `Φ q s := GExp (c s) (q.1 • V s + q.2 • W s)`.

Then `z q i = Φ q (t (i+1))`, `z 0 = w` (by `hsample` and `GExp x 0 = x`), `Φ q 0 = p = Φ q T`
(because `V, W` vanish at `0` and `T`).

**(1) The comparison `gonEnergy p (z q) ≤ (T/2) ∫₀^T |∂_s Φ q|²`.**  The `i`-th side of the polygon
`z q` is `d (Φ q (t i)) (Φ q (t (i+1)))`; `Φ q` is `C¹` on `[0,T]`, so
`d (Φ q (t i)) (Φ q (t (i+1))) ≤ ∫_{t i}^{t (i+1)} |∂_s Φ q|` (`riemannianDist_le_curveLength`), and
Cauchy–Schwarz on the single interval gives
`d (…)² ≤ (T/N) ∫_{t i}^{t (i+1)} |∂_s Φ q|²`.  Summing over `i : Fin N` and multiplying by `N/2`
yields the claim.  (For `i = 0` and `i = N-1` the endpoints are `p = Φ q 0` and `p = Φ q T`.)

**(2) The second variation of the comparison functional.**  Put
`G q := (T/2) ∫₀^T curveSpeed (Φ q) ² (equivalently (T/2) ∫ |∂_s Φ q|²)`.  Then `G 0 = E_N w`
(equality in the comparison at `q = 0`: `Φ 0 = c` is unit-speed).  For `X = (α,β) ≠ 0`,
`Submission.EnergyGeoGlobal.energy_second_deriv_geodesic'` applied to `γ := c` (globally smooth,
geodesic everywhere — this is where the *extension lemma*
`Work.OddBound.exists_global_geodesic_extension` is used upstream) and the field
`α • V + β • W` gives

  `HasDerivAt (deriv (fun σ ↦ ∫₀^T curveSpeed (σ ↦ GExp (c s) (σ • (α • V s + β • W s)))²))
     (2 ∫₀^T idxAlong (c, α•V+β•W, ∇(α•V+β•W))) 0`,

so `D²G (0) [X,X] = T · ∫₀^T idxAlong (c, α•V+β•W, ∇(α•V+β•W)) < 0` by `hneg`.

**(3) Conclusion of the analytic core.**  `(gonEnergy p ∘ z) (0) = G 0` and
`gonEnergy p ∘ z ≤ G` everywhere, so `((gonEnergy p ∘ z) - G)` has a maximum at `0` and hence
`D² (gonEnergy p ∘ z) (0) [X,X] ≤ D²G (0) [X,X] < 0` for every `X ≠ 0`.  In particular the second
derivative of `gonEnergy p ∘ z` at `0` is negative definite.

**NOTE (structure).**  The chart must be the *concrete* `piExtChart x` (the product of extended
charts), not an arbitrary atlas chart of an arbitrary smooth structure on `P`: with a wild
homeomorphism-transported structure the composite `e ∘ z` need not be differentiable, and the
transfer genuinely fails.  With `piExtChart x` the differentiability of `φ` is a theorem about
`extChartAt` (needs only `hwsrc`), so no `IsManifold` hypothesis is required.

**(4) The chart chain rule.**  Let `F := gonEnergy p ∘ (piExtChart x).symm` and
`φ := (piExtChart x) ∘ z`.  Then
`gonEnergy p ∘ z = F ∘ φ`, `F` is `C²` at `e w` (`hC2`), `φ` is differentiable at `0` — here the
`IsManifold (𝓘(ℝ,H')) ∞` hypothesis is used: the atlas chart `e` is `C^∞` as a map `P → H'`, and
`z` is `C^∞` as a map `ℝ² → P` (each coordinate is `(a,b) ↦ GExp (c t) (…)`, jointly smooth by
`Submission.GExpJoint`).  Put `L := fderiv ℝ φ 0 : ℝ² →L[ℝ] H'`, `v := L (1,0)`, `w' := L (0,1)`.
The chain rule (or the second-order Taylor expansion of `F` at `e w` along `φ (t X) = e w + t L X +
o(t)`) gives, since `D F (e w) = 0` (`hF0`),

  `D²(F ∘ φ) (0) [X,X] = D²F (e w) (L X) (L X)`,

and this is `< 0` for every `X ≠ 0` by (3).  Writing `X = (c,d)` gives, for every `(c,d) ≠ 0`,
`D²F (e w) (c • v + d • w') (c • v + d • w') < 0`, which is exactly `HasNegDefPlane H' (gonEnergy p) w`
witnessed by the chart `piExtChart x` (`hasNegDefPlane_of_chart`, `PolygonChart.lean`, with
`he`/`hwsrc`).
-/

namespace Work.OddBound

end Work.OddBound
