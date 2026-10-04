import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Design: the value bound of the odd-dimensional Klingenberg minimax (polygon model)

This module has no content; it exists so that the delegated statement
`Work.OddBound.polygonValueBound` (in `Submission/Work/OddBound/polygonValueBound.lean`) can
`import` it and read the design.

## What has to be proved

`Work.OddBound.polygonValueBound`: for a compact, connected Riemannian manifold `M` with
`sec ≤ K`, `0 < K`, a closed unit-speed geodesic `γ` of period `L < 2π/√K`, a radius `ρ > 0` with
`ρ < π/√K` and `InjAtLeast hmet x ρ` for every `x : M`, a natural number `N ≥ 3` with
`4π²/(K ρ²) < N`, and a **continuous** family `w : ℝ → Fin (N-1) → M` of polygons from the
geodesic polygon `w 0 = (i ↦ γ (L * (i+1) / N))` to the constant polygon `w 1 = p`:

> there is `τ ∈ [0,1]` with `gonEnergy p (w τ) ≥ 2π²/K`.

Equivalently: the **minimax value** (over paths of polygons) of the polygon energy is
`≥ 2π²/K`.  This is the "value bound" half of Klingenberg's loop-space minimax; the other half
(the existence of a long *critical* polygon) is the mountain-pass step
(`Work.OddBound.modelMountainPass`, to be built on top of this).

## The proof, in the order in which it should be done

Write `E τ := gonEnergy p (w τ)` and `ℓ τ := gonLength p (w τ) = Σ_{i<N} d(v_i, v_{i+1})`, where
`v_i := gonVert p (w τ) i` (so `v_0 = v_N = p`).  Recall the definitions in
`Submission/Work/OddBound/PolygonModel.lean`: `gonVert`, `gonSideLen`, `gonLength`, `gonEnergy`,
`GonSmall`, and the proved Cauchy–Schwarz bound `gonLength_sq_le_two_mul_gonEnergy`
(`ℓ² ≤ 2E`, i.e. `ℓ ≤ √(2E)`).

**Step 0 (the sides are short).**  Assume for contradiction that `E τ < 2π²/K` for every
`τ ∈ [0,1]`.  Then for every `i`
`gonSideLen p (w τ) i ≤ √(2 E τ / N) < 2π/√(K N)`,
and the hypothesis `4π²/(K ρ²) < N` gives `2π/√(K N) < ρ`.  Hence `GonSmall p ρ (w τ)` holds for
every `τ` (both on `[0,1]` and, after re-proving the estimate for the "trivial extension", on a
neighbourhood of `[0,1]`), and in particular every side is shorter than the injectivity radius:
between any two consecutive vertices there is a **unique minimising geodesic**.

**Step 1 (the broken-geodesic family).**  For `τ` in a neighbourhood of `[0,1]` and `i : Fin N`
let `s_i(τ) : ℝ → M` be the minimising geodesic from `v_i(τ)` to `v_{i+1}(τ)`, parametrised
proportionally to arclength: `s_i(τ) r = GExp_{v_i(τ)} (r • W_i(τ))` where
`W_i(τ) ∈ T_{v_i(τ)}M` is the (unique!) vector with `GExp (W_i τ) = v_{i+1} τ` and
`‖W_i τ‖ = d(v_i τ, v_{i+1} τ)`.  Uniqueness (`Submission.SegmentDomain.exists_unique_segmentDomain_vec`)
plus the continuity of `GExp` on the segment domain
(`Submission.XuMain.exists_pos_edist_lt_imp_norm_sub_lt`, as used in
`Submission/Work/OddBound/longHomotopy/exists_lift_of_short.lean`) give the **joint continuity** of
`(τ, r) ↦ s_i(τ) r` and of `τ ↦ W_i(τ)`.

The **polygon curve** is the concatenation
`k (s, τ) = s_i(τ) (N s - i)` for `s ∈ [i/N, (i+1)/N]`
(so that `k (i/N, τ) = v_i(τ)`); it is jointly continuous in `(s, τ)`, 1-periodic in `s`, and
`k (0, τ) = v_0(τ) = p`.  Its length over `[0,1]` is `ℓ τ` (additivity of `curveLength` over the
`N` pieces; `Submission.Length.curveLength` is the integral of the speed, so corners are harmless).

**Step 2 (the balanced reparametrisation).**  The slice `k (·, τ)` has constant speed `N · d_i(τ)`
on its `i`-th piece, so its corner parameters are the cumulative arclengths
`a_i(τ) := (Σ_{j<i} d_j(τ)) / ℓ(τ)` (when `ℓ τ > 0`).  Reparametrise affinely on each piece to
make the speed `ℓ τ` everywhere:
`c (s, τ) := k (A(s, τ), τ)`, where `A(·, τ)` is the piecewise affine increasing bijection of
`[0,1]` sending `i/N` to `a_i(τ)`.  Then

* `c` is jointly continuous and `c (s+1, τ) = c (s, τ)`, `c (0, τ) = p`;
* `curveLength (c (·,τ)) 0 s = s · ℓ τ`, so in particular **both halves of every slice have length
  `ℓ τ / 2`**;
* each slice is `C¹` (indeed `C^∞`) on each of the finitely many intervals
  `[a_i(τ), a_{i+1}(τ)]` — this is the `hpiece` hypothesis of
  `Work.OddBound.liftPiecewise.long_homotopy_lower_bound_piecewise`;
* `c (s, 0) = γ (L * s)`: at `τ = 0` all the sides have length `L/N`, so `a_i(0) = i/N` and each
  piece is the arclength-parametrised sub-arc of `γ` of length `L/N` (the side is the unique
  minimising geodesic between `γ (L i / N)` and `γ (L (i+1) / N)`, and the sub-arc of `γ` is one,
  because `L/N < ρ` by Step 0); hence `c (s,0) = γ (L s)`;
* `c (s, 1) = p` (all vertices are `p`, all sides have length `0`).

**Step 3 (apply the long homotopy lemma).**  Since `ℓ τ ≤ √(2 E τ) < 2π/√K` for every `τ`, both
halves of every slice are shorter than `π/√K`.  `γ` is a closed unit-speed geodesic with
nonvanishing velocity and period `L`, `hper`, `hγ0`, so the hypotheses of
`Work.OddBound.liftPiecewise.long_homotopy_lower_bound_piecewise` hold and give `False`.  This
contradicts the assumption of Step 0, which is the statement.

**Degenerate cases.**  If some `E τ = 0` the polygon is constant; the argument is unchanged
(the degenerate pieces of the reparametrisation contribute length `0`, so the affine
reparametrisation `A` in Step 2 can be defined by continuity, e.g. by using the *extended*
families on `[-ε, 1+ε]` and passing to the limit, or by first "thickening" `w`).

## Why the statement is the one needed

`Work.OddBound.MinimaxExtraction` requires that the minimax value over the competing families
exceeds `2π²/K`, so that the mountain pass applied to the polygon energy produces a critical
polygon of energy `≥ 2π²/K` (hence a closed geodesic of length `≥ √(2 · 2π²/K) = 2π/√K`), whose
index is then contradicted by the curvature bound.  This module supplies exactly that lower bound.
-/

namespace Work.OddBound.Design

end Work.OddBound.Design
