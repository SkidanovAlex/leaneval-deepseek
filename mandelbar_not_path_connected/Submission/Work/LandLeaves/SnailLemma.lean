/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The Snail lemma (germ form) — first formulation, superseded

**Proved** (`Work.LandLeaves.snailLemma`), and **superseded as the route to ledger item 5** by
`Work.LandLeaves.SnailLemmaMilnor` (`SnailLemmaMilnor.lean`), which is Milnor's exact form
(Lemma 16.5) and is the one instantiated at periodic rays: a curve carried into itself with a
*strict norm decrease* is not supplied by a ray tail (the level dynamics moves the ray *away* from
the landing point), whereas Milnor's path form is.  The statement below is kept as a proved
by-product; its docstring records the counterexample that showed the necessity of the clause
`σ t ∈ (0,1]` in its hypothesis.

`Work.LANDCL.SnailDichotomy` (a periodic ray landing point is repelling or parabolic) decomposes
into an elementary half and one analytic statement (`Work.LandLeaves.NoNeutralLanding`); see
`Submission/Work/LandLeaves/snailDichotomy_of_noNeutral.lean`.  The analytic statement is the
classical **Snail lemma** (Pommerenke; Douady–Hubbard; Milnor, *Dynamics in one complex variable*,
Lemma 16.5; also Carleson–Gamelin), which is *germ-level*, not ray-level:

> a holomorphic germ at a fixed point of multiplier of modulus `1` cannot map a curve
> accumulating at that point into itself with the dynamics moving along the curve toward the
> point, unless the multiplier is exactly `1`.

`Work.LandLeaves.SnailLemma` below is this statement, with the curve and the dynamics along it
made explicit:

* `γ : ℝ → ℂ` is continuous on `(0,1]` and tends to the fixed point `z₀` as `t → 0⁺`;
* `σ : ℝ → ℝ` records the dynamics *on the curve*: `f (γ t) = γ (σ t)` for `t ∈ (0,1]`;
* **`σ` maps the parametrising interval into itself**, `σ t ∈ (0,1]`: this is the "the curve is
  carried into itself" clause.  It is essential and was missing in a first draft of this file: with
  only `σ : ℝ → ℝ` the statement is *false*, as the reviewers of the statement pointed out —
  `f z = -z + z²`, `γ t = t`, `σ t = t² - t` satisfies every clause (the orbit jumps onto the
  *other* branch of the curve) while `deriv f 0 = -1`;
* `‖γ (σ t) - z₀‖ < ‖γ t - z₀‖` says the dynamics moves the points of the curve strictly towards
  the fixed point.  (This is the hypothesis that rules out the "rotationally invariant spiral"
  curves that a rotation germ does admit: there the distance to `z₀` is preserved.  For the
  application to rays the direction of the dynamics is the opposite one — the ray tail is mapped
  *away* from the landing point — so one applies the lemma to the *local inverse germ*, whose
  multiplier is `λ⁻¹`, of modulus `1` as well.)

The two steps that turn this into ledger item 5 are delegated separately:

* `Work.LandLeaves.snailLemma` : `SnailLemma` (the germ statement above);
* `Work.LandLeaves.noNeutralLanding_of_snailLemma` : `SnailLemma → NoNeutralLanding`
  (instantiation at periodic rays: `f = (Tsq c)^[k]`, whose multiplier at the landing point is
  `multiplier2 c k z`; the invariant curve is the tail of the periodic ray, parametrised by its
  level, on which `f` acts by `r ↦ r ^ (4 ^ k)`).

With those two, `Work.LANDCL.SnailDichotomy` follows from
`Work.LandLeaves.snailDichotomy_of_noNeutralLanding`, and no further input is needed for the
general (even) period — in particular the even-period clause of the ledger's statement is
*exactly* `NoNeutralLanding` and is not a formalisation artefact: for even `k` one has
`multiplier2 c k z = ζ²` with `ζ = deriv ((T_c)^[k]) z`, so the "root of unity" form of the Snail
lemma (which allows `ζ` a primitive `q`-th root of unity, `q ∤ 2`) does *not* suffice, while the
form above (`‖λ‖ = 1 → λ = 1`, applied to the holomorphic map `(Tsq c)^[k]` itself) does.
-/
import Submission.Work.LandLeaves.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LandLeaves

/-- **The Snail lemma** (germ form): a holomorphic germ at a fixed point whose multiplier has
modulus `1`, carrying a curve accumulating at the fixed point into itself *and moving the points
of that curve strictly towards the fixed point*, has multiplier exactly `1`. -/
def SnailLemma : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (γ : ℝ → ℂ) (σ : ℝ → ℝ),
    AnalyticAt ℂ f z₀ → f z₀ = z₀ → ‖deriv f z₀‖ = 1 →
    ContinuousOn γ (Set.Ioc 0 1) →
    Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z₀) →
    ContinuousOn σ (Set.Ioc 0 1) →
    (∀ t ∈ Set.Ioc (0 : ℝ) 1, σ t ∈ Set.Ioc (0 : ℝ) 1) →
    (∀ t ∈ Set.Ioc (0 : ℝ) 1, f (γ t) = γ (σ t)) →
    (∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖γ (σ t) - z₀‖ < ‖γ t - z₀‖) →
    deriv f z₀ = 1

end Work.LandLeaves
