import Mathlib

/-!
# Design: the broken-geodesic family of `Work.OddBound.polygonValueBound`

This module has no content; it exists so that the delegated statement
`Work.OddBound.polygonValue.brokenGeodesicFamily` can `import` it and read the plan.

## The statement

`brokenGeodesicFamily`: given a continuous family of based closed `N`-gons
`w : ℝ → Fin (N-1) → M` (vertices `gonVert p (w τ) : ℕ → M`, `gonVert p (w τ) 0 = p`,
`gonVert p (w τ) i = w τ ⟨i-1⟩` for `1 ≤ i ≤ N-1`, `gonVert p (w τ) N = p`) going from the polygon
inscribed in the closed unit-speed geodesic `γ` of period `L` (at `τ = 0`) to the constant polygon
at `p` (at `τ = 1`), **assuming every slice has energy `< 2π²/K`**, produce a continuous family
`c : ℝ × ℝ → M` of 1-periodic based loops with `c (·,0) = γ (L ·)`, `c (·,1) = p`, whose slices are
piecewise `C¹` and whose two halves are both shorter than `π/√K`.  That is exactly the hypothesis
package of `Work.OddBound.liftPiecewise.long_homotopy_lower_bound_piecewise`, so the value bound
`Work.OddBound.polygonValueBound` is: assume all energies `< 2π²/K`, apply this lemma, apply the
piecewise long homotopy lemma, contradiction.

## Step 0: the sides are short

`Work.OddBound.gonSideLen_lt_of_energy_lt` (in `Submission/Work/OddBound/polygonValue/Basic.lean`)
gives, for `τ ∈ [0,1]` and `i : Fin N`, `gonSideLen p (w τ) i < ρ` from
`gonEnergy p (w τ) < 2π²/K`, `N ≥ 3` and `4π²/(Kρ²) < N`.  Also
`Work.OddBound.gonLength_lt_of_energy_lt` gives `gonLength p (w τ) < 2π/√K`.

## Step 1: the side curves

For `τ ∈ [0,1]` and `i : Fin N` put `x := gonVert p (w τ) i`, `y := gonVert p (w τ) (i+1)`.  Then
`d(x,y) = gonSideLen p (w τ) i < ρ ≤ inj(x)`, so `Submission.SegmentDomain.exists_unique_segmentDomain_vec`
(with `riemannianEDist I x y = ENNReal.ofReal (riemannianDist I x y)`, from
`Submission.Work.OddBound.polygon.riemannianDist_eq_toReal`) gives a **unique** vector
`W i τ ∈ T_{x}M` with `W i τ ∈ segmentDomain hmet x` and `GExp (cov := cov) hmet x (W i τ) = y`;
moreover `‖W i τ‖ = gonSideLen p (w τ) i` (from
`Submission.SegmentDomain.edist_GExp_eq_norm_of_mem_segmentDomain`).  Define the *side curve*

  `S i τ r := GExp (cov := cov) hmet x (r • W i τ)`   for `r : ℝ`,

so that `S i τ 0 = x`, `S i τ 1 = y`, the map `r ↦ S i τ r` is the minimising geodesic from `x` to
`y` at constant speed `‖W i τ‖ = d i τ`, and `S i τ` is `C^∞` in `r`.

**The work of this step is continuity**: `(τ, r) ↦ S i τ r` must be jointly continuous (the vector
`W i τ` lies in the *moving* fibre `T_{gonVert p (w τ) i}M`).  Available tools:

* `Submission.LiftUniform.exists_pos_joint_frameVector_edist_lt_imp_norm_sub_lt` — the **joint
  (moving base point) form of the inverse-continuity of `GExp`**: on a compact chart piece
  `Z ⊆ (chartAt H z₀).source` with `InjAtLeast hmet q ρ` for `q ∈ Z` and a chart-radius bound `η`,
  close *chart coordinates of the base points* plus close images force close *coordinate vectors*.
  Proof pattern: fix `τ₀`, put the base point `gonVert p (w τ₀) i` in the interior of a compact
  chart piece `Z` (a finite cover of the compact `M` by such pieces), write
  `W i τ = frameVector z₀ (gonVert p (w τ) i) (u τ)` for `τ` near `τ₀`, and use the lemma to
  conclude `u τ → u τ₀`; then `(τ, r) ↦ GExp (gonVert p (w τ) i) (r • frameVector z₀ (·) (u τ))`
  is jointly continuous near `τ₀` because `(q, u) ↦ GExp q (frameVector z₀ q u)` is jointly `C^∞` on
  `Z × closedBall 0 η` (`Submission.GExpJoint.contMDiffOn_GExp_frameVector`) and `r ↦ r • u` is
  smooth.  `Framevector` is `Submission.Geodesic.frameVector`, `GExpFlow.frameVector_clm` recovers
  the fibre vector from its chart coordinates.

## Step 2: concatenation and the arclength balancing

Let `ℓ τ := gonLength p (w τ) = ∑_i d i τ`, `C τ i := ∑_{j<i} d j τ` (`C τ 0 = 0`, `C τ N = ℓ τ`).
The polygon curve is

  `k τ u := S i τ (N u - i)`  for `u ∈ [i/N, (i+1)/N]  (i : Fin N)`,

jointly continuous in `(u,τ)` (the pieces agree at the junctions: `S i τ 1 = S (i+1) τ 0`), 1-periodic
in `u` (extend by `k τ (u+1) = k τ u`), and `k τ 0 = p`.  The reparametrisation proportional to
arclength is the piecewise affine increasing bijection `A τ : [0,1] → [0,1]` with
`A τ (i/N) = C τ i / ℓ τ`, i.e. piece `i` of `k` is traversed during the parameter interval
`[C τ i / ℓ τ, C τ (i+1) / ℓ τ]`; then `c τ s := k τ (A τ s)` has constant slice speed `ℓ τ`, hence

  `curveLength (c τ) 0 (1/2) = ℓ τ / 2 < π/√K`,  `curveLength (c τ) (1/2) 1 = ℓ τ / 2 < π/√K`.

`c τ` is piecewise `C¹` with the `τ`-dependent breakpoints `C τ i / ℓ τ` (the partition of the
`hpiece` clause; merge the pieces of zero length, where `d i τ = 0` — then the slice is constant
there, so `ContMDiffOn` still holds).  Use the additivity of `curveLength` over the partition
(`Submission.Length.curveLength_add`, or `curveLength_add_piecewise` in
`Submission/Work/OddBound/liftPiecewise/exists_lift_of_piecewise_short.lean`) and the change of
variables/affine reparametrisation `curveLength (fun s => S (a + b * s)) = ‖b‖ * curveLength S`.

**Degenerate slices.**  If `ℓ τ = 0` (the polygon at `τ` is constant at `p`) the slice is constant,
and `A τ` may be defined arbitrarily.  Also, the *affine* `A τ` need not converge as `τ → 1` (the
relative sizes of the `d i τ` may oscillate), but `c τ s = k τ (A τ s)` still converges to `p`
uniformly in `s` because every vertex of `k τ` tends to `p` and `∑_i d i τ → 0`.  Use that for the
continuity of `c` at `τ = 1` (`Manifold.riemannianEDist` between `p` and `k τ u` is bounded by
`∑_{j ≤ i} d j τ + d i τ`).

For the extension of `c` to all `τ ∈ ℝ` needed by the `Continuous` clause, clamp: the hypothesis is
only available on `τ ∈ [0,1]`, so set `c τ := c (clamp τ)` (or `w τ := w (clamp τ)`), which preserves
continuity, periodicity, the `τ = 0/1` slices and the length bounds.

## Step 3: the `τ = 0` slice is the geodesic

All sides of the `τ = 0` polygon have length `L/N < ρ` (`Work.OddBound.div_lt_of_lt_two_pi_div_sqrt`,
using `hLlt : L < 2π/√K`, `N ≥ 3` and `4π²/(Kρ²) < N`).  On the one hand, the sub-arc
`r ↦ γ (L * (i + r) / N)` of the geodesic has length `L/N` by `hunit` (it is arclength-parametrised,
`curveSpeed γ t = 1` for `t ∈ [0,L]`), and it is *minimising* because `L/N < ρ ≤ inj(γ (L i / N))`
(geodesic arcs shorter than the injectivity radius of their initial point are minimising); on the
other hand `S i 0` is the unique minimising geodesic from `γ (L i / N)` to `γ (L (i+1) / N)`.  Hence
`S i 0 r = γ (L * (i + r) / N)`, and since at `τ = 0` all the `d i 0 = L/N` are equal, the balancing
map `A 0` is the identity, so `c 0 s = γ (L s)`.  (Suitable lemmas: `InjAtLeast`, minimising sets in
`Submission.InjRadius`/`Submission.RayConj`/`Submission.InjBall`; search for
`isMinimising`/`minimisingSet`/`cutTime`.)

## Step 4: `τ = 1`

`hw1` says every interior vertex is `p`, and `gonVert p (w 1) 0 = gonVert p (w 1) N = p`, so the
polygon at `τ = 1` is constant `p` and `c 1 s = p`.
-/

namespace Work.OddBound.Design

end Work.OddBound.Design
