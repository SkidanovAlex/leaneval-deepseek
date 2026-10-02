/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The Snail lemma in Milnor's exact form (ledger item 5)

> **Source check (2024).**  Milnor's *Dynamics in one complex variable*, Lemma 13.2, reads
> verbatim (workspace copy of the text: `_snailsearch/milnor.txt`):
> *"Let `p : (0,∞) → U∖{0}` be a path which converges to the origin, and suppose that `f` maps `p`
> into itself so that `f (p(t)) = p(t+1)`.  Then … the multiplier `λ` satisfies either `|λ| < 1`
> or `λ = 1`."*  Corollary 13.3 is the inverse formulation: `f (p t) = p (t-1)` gives
> `|λ| > 1` or `λ = 1`.
>
> This is the statement used below (the `λ = 1` clause).  A suggestion that the source's conclusion
> is "`λ` is a root of unity" is **not** what the source says, and the attempted counterexample
> `g z = z² - z` (`λ = -1`) does not satisfy the lemma's hypothesis: by the lemma itself no path
> `p` with `g (p t) = p (t+1) → 0` exists there (`Submission/Work/LandLeaves/NOTES_snailLemma_source.md`).

This file states the Snail lemma in the form in which it is used in the landing theory, as
prescribed by the lead (Milnor, *Dynamics in one complex variable*, 3rd ed., Lemma 16.5):

> **Snail lemma.**  Let `g` be holomorphic near `z₀` with `g z₀ = z₀`, `g'(z₀) = λ`, and suppose
> that there is a continuous path `p : [0,∞) → U ∖ {z₀}` (`U` a neighbourhood of `z₀`) with
> `g (p t) = p (t + 1)` for all `t ≥ 0` and `p t → z₀` as `t → ∞`.  Then `‖λ‖ < 1` or `λ = 1`.

The content is the exclusion of the neutral non-parabolic case `‖λ‖ = 1`, `λ ≠ 1`: if `g` is
repelling at `z₀` the forward path `t ↦ g^⌊t⌋(p 0)` cannot converge to `z₀`, and if `‖λ‖ = 1`
with `λ ≠ 1` the rotation by `arg λ` per unit time contradicts the convergence of `p` to `z₀`.
Milnor's proof (both cases: `λ` an irrational rotation, and `λ` a primitive `q`-th root of unity,
where one passes to `g^q`, whose local form is tangent to the identity, and uses the cyclic
permutation of the attracting petals).

Why this form and not a "curve carried into itself with strict norm decrease": the earlier drafts
of this area (`SnailLemma.lean`) used the latter, and both the statement reviews and the prover of
the instantiation showed that (i) the clause `σ t ∈ (0,1]` is indispensable (otherwise
`g z = -z + z²`, `γ t = t`, `σ t = t² - t` is a counterexample) and (ii) the norm-decrease clause
is *not* satisfiable by a ray tail, whose forward dynamics moves the level *up*
(`r ↦ r ^ (4 ^ k)`).  Milnor's path formulation has neither defect: the path is parametrised by
"time" and the dynamics is the unit shift, which is exactly what the ray tail provides.

## The instance at periodic rays

Let `c ∈ Mandelbar` (so a Böttcher *homeomorphism* exists, `Work.SeedDyn.isDynBottcherHomeo`),
`θ` a periodic angle of period `k`, `z` the landing point of the ray `R_c(θ)`, and
`λ = multiplier2 c k z = deriv ((Tsq c)^[k]) z`, `‖λ‖ = 1`.  Put `F = (Tsq c)^[k]`, which is
holomorphic at `z` with `F z = z` (`Work.Landing.landsAt_periodic`) and multiplier `λ`.  Since
`λ ≠ 0`, `F` has a holomorphic local inverse `g` at `z` with `g z = z` and `g'(z) = λ⁻¹`; define
`p t :=` the point of the ray whose Böttcher level is `r ^ ((4 ^ k) ^ (-t))` for a fixed level
`r > 1`.  Then

* `F (p t) = p (t - 1)`, i.e. `g (p s) = p (s + 1)` (the Böttcher equation, and
  `angDouble^[2k] θ = θ` for a periodic angle);
* `p t → z` as `t → ∞` because the ray lands at `z` (`rayAccum c φ θ = {z}`);
* `p t ≠ z` and `p t` stays in a neighbourhood of `z` for large `t`.

Applying the Snail lemma to `g` and `p` gives `‖λ⁻¹‖ < 1` or `λ⁻¹ = 1`; with `‖λ‖ = 1` this
forces `λ = 1`, which is `Work.LandLeaves.NoNeutralLanding`, hence (with
`Work.LandLeaves.snailDichotomy_of_noNeutralLanding`) `Work.LANDCL.SnailDichotomy`.
-/
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.SnailLemma

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LandLeaves

/-- **The Snail lemma in Milnor's form** (Lemma 16.5 of *Dynamics in one complex variable*): a
holomorphic germ at a fixed point `z₀` which admits a continuous forward path in a punctured
neighbourhood of `z₀` converging to `z₀` and advancing by the germ (`g (p t) = p (t + 1)`) either
contracts (`‖g'(z₀)‖ < 1`) or is exactly parabolic (`g'(z₀) = 1`). -/
def SnailLemmaMilnor : Prop :=
  ∀ (g : ℂ → ℂ) (z₀ : ℂ) (U : Set ℂ) (p : ℝ → ℂ),
    AnalyticAt ℂ g z₀ → g z₀ = z₀ → IsOpen U → z₀ ∈ U →
    ContinuousOn p (Set.Ici 0) →
    (∀ t ∈ Set.Ici (0 : ℝ), p t ∈ U ∧ p t ≠ z₀) →
    (∀ t ∈ Set.Ici (0 : ℝ), g (p t) = p (t + 1)) →
    Tendsto p atTop (𝓝 z₀) →
    ‖deriv g z₀‖ < 1 ∨ deriv g z₀ = 1

end Work.LandLeaves
