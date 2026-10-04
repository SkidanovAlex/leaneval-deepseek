import Mathlib
import Submission.Work.OddBound.PolygonModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Design: the two localisation lemmas the polynomial-energy mountain pass needs

While assembling `Work.OddBound.MinimaxExtraction` (session 8) it became clear that the mountain-pass
statement of session 7 (`design/MountainPassManifold2.lean`) is **not applicable as stated**, for a
reason that is intrinsic to the polygon model:

* `gonEnergy p w = (N/2) Σᵢ d(vᵢ,vᵢ₊₁)²` is only `C²` at polygons whose sides are shorter than a
  uniform injectivity radius `ρ` (`sqDist_contDiffAt_charts`); at a polygon with a long side the
  energy is not `C²` (and `fderiv` is then junk `0`).
* The mountain pass of session 7 asks, for **every** `z : P`, for a chart on whose **whole target**
  the chart expression is `C²` — impossible for `gonEnergy` on `Fin (N-1) → M`, whose chart targets
  contain polygons with arbitrarily long sides.
* What the minimax argument actually uses is `C²` only on a neighbourhood of the *sublevel set*
  `{f ≤ C}` for a level `C` slightly above the minimax value `Λ`.  The two lemmas below make that
  precise.

## (1) A bounded family of based polygons — `exists_gonEnergy_le_of_balanced_nullhomotopy`

**Corrected in session 8.**  The first attempt at this lemma asked for an `N`-independent bound `C`
from the explicit family `w(τ)_i = GExp p ((1-τ) • vᵢ)` (shrink each vertex along a minimising
geodesic to `p`).  Two reviewers refuted it:

* the statement itself is false without an extra hypothesis (a flat torus with a non-contractible
  closed geodesic `γ` admits no such `C`, because all sides `< inj` would assemble into a based
  null-homotopy of `γ`); and
* the *proof idea* is also wrong: along a closed geodesic the minimising vectors from `p` flip by
  `~π` at the antipodal point (where both halves minimise), so consecutive vertices of the family are
  `~L` apart, not `~L/N`, and that energy again grows like `N`.

The correct statement below takes the family from a **based null-homotopy** of `γ` whose slices are
**parametrised proportionally to arclength** ("balanced") and have **bounded length**:

`Hf s t` is 1-periodic in `s`, `Hf 0 t = p`, `Hf (·,0) = γ (L ·)`, `Hf (·,1)` constant, jointly
continuous, piecewise `C¹` in `s`, with `curveLength 0 s = s · curveLength 0 1` and
`curveLength 0 1 ≤ B`.  Then the polygons `w(τ)_i := Hf ((i+1)/N) τ` run from the inscribed polygon
at `τ = 0` to the constant polygon at `τ = 1`, and

`gonEnergy p (w τ) = (N/2) Σ d(vᵢ,vᵢ₊₁)² ≤ (N/2) Σ (arclength over the i-th subinterval)²`
`                   = (N/2) Σ (len/N)² = (N/2)(len²/N) = len²/2 ≤ B²/2`,

an **`N`-independent** bound.  (The periodicity of `Hf` in `s` is what makes the *closing* side
`v_N = p` equal the last arclength slice — this is exactly what the naive "shrink along `γ`" family
lacks, and it costs the factor `N` there.)

**What is still missing for the application**: the *existence* of such a balanced bounded
null-homotopy of `γ`.  `Work.OddBound.minimax.exists_based_null_homotopy` supplies a based
null-homotopy (from simple connectivity) but neither boundedness of the slice lengths nor the
balanced parametrisation; the balanced reparametrisation of a family is the object of session 5's
delegation `Work.OddBound.reparam.exists_balanced_reparam_family`.  Boundedness of the lengths is a
genuine topology question (contract `γ` through short loops) — the *free* loop space has the easy
bounded family `s ↦ γ(τ L s)` (all lengths `≤ L`), while a *based* one must force the loops through
`p`; the two are related by prepending/append the path from `p` to the moving base point, which
costs at most `2 · diam M`.

## (2) The localised mountain pass — `exists_critical_index_le_one_local`

The mountain pass of session 7 with the hypothesis

`hsm : ∀ z, f z ≤ C → ∃ e ∈ atlas H' P, z ∈ e.source ∧ ContDiffAt ℝ 2 (f ∘ e.symm) (e z)`

(for a fixed `C > Λ`) instead of "`ContDiffOn` on every chart target".  The proof is the same port of
the proved Euclidean theorem `Work.OddBound.mountainPass.exists_critical_index_le_one`: the local
lemmas `local_joinedIn_of_negDefPlane`, `local_joinedIn_of_fderiv_ne_zero` only ever need `C²` on a
neighbourhood of points of the competitor sets, and all of those lie in `{f ≤ Λ + 1/(n+1)} ⊆ {f ≤ C}`.

In the application (`P = Fin (N-1) → M`, `f = gonEnergy p`) the hypothesis is discharged by the chart
algebra: for `z` with `f z ≤ C` every side of `z` is `< √(2C/N) < ρ`, and
`Work.OddBound.chartAlgebra.contDiffAt_gonEnergy_piExtChart_gen` gives `C²` of the chart expression at
the corresponding point of the concrete chart `piExtChart z`.
-/

namespace Work.OddBound

end Work.OddBound
