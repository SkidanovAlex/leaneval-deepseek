import Submission.Lib.Unif2.Work.CriticalSet.Defs
import Submission.Lib.Unif2.Work.CriticalSet.Fundamentals
import Submission.Lib.Unif2.Work.CriticalSet.eventually_eq_of_mem_closure_locallyConstant
import Submission.Lib.Unif2.Work.CriticalSet.criticalPoint_iff_chartAt
import Submission.Lib.Unif2.Work.CriticalSet.criticalPoint_iff_companion
import Submission.Lib.Unif2.Work.CriticalSet.criticalSet_isDiscreteIn
import Submission.Lib.Unif2.Work.CriticalSet.criticalSet_isLocallyFinite
import Submission.Lib.Unif2.Work.CriticalSet.countable_criticalValues
import Submission.Lib.Unif2.Work.CriticalSet.levelSet_isLocalGraph
import Submission.Lib.Unif2.Work.CriticalSet.notLocallyConstantOn_of_hasGreenFunctionWeak
import Submission.Lib.Unif2.Work.CriticalSet.exists_regularLevel_isCompact_manifold
import Submission.Lib.Unif2.Work.CriticalSet.frontier_superlevel_subset_levelSet
import Submission.Lib.Unif2.Work.CriticalSet.frontier_superlevel_eq_levelSet_of_regularValue
import Submission.Lib.Unif2.Work.CriticalSet.analytic_exists_regularValue_near
import Submission.Lib.Unif2.Work.CriticalSet.analytic_finite_preimage_of_regularValue

/-!
# `Work.CriticalSet`: regular level sets of a harmonic function (a replacement for Sard's lemma)

Everything in this chapter is reachable through `import Submission.Work.CriticalSet.All`
(namespace `Work.CriticalSet`).  No Sard theorem is used anywhere: the critical points of a nonconstant
harmonic function are isolated (its local holomorphic companion has an analytic derivative with
isolated zeros), so its critical values are countable and regular values are plentiful.

## Importing

```lean
import Submission.Lib.Unif2.Work.CriticalSet.All
```

## Main definitions

* `Work.CriticalSet.IsCriticalPointAt u x` — `u : X → ℝ` has vanishing gradient at `x`.  Measured in
  the preferred chart at `x`: `fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0`.
* `Work.CriticalSet.criticalSet u U` — the critical points of `u` lying in `U`
  (`mem_criticalSet`).
* `Work.CriticalSet.IsRegularPointAt u U x`, `Work.CriticalSet.IsRegularValueOn u U c` — the
  negations (no critical point at `x`, respectively none on the level set `{u = c}` inside `U`).
* `Work.CriticalSet.NotLocallyConstantOn u U` — `u` is not eventually constant near any point of
  `U` (equivalently, for harmonic `u` on open `U`: `u` is nonconstant on every connected component
  of `U`).
* `Work.CriticalSet.IsLocallyFiniteIn S U`, `Work.CriticalSet.IsDiscreteIn S U` — local finiteness
  and discreteness of a set in `U`; `IsDiscreteIn.isLocallyFiniteIn` converts.
* `Work.CriticalSet.punctured z₀` — the punctured surface `X ∖ {z₀}` (`mem_punctured`,
  `isOpen_punctured`).
* `Work.CriticalSet.IsLocalLevelGraphAt u x` — the level set of `u` through `x` is, after a
  real-linear change of coordinates in the preferred chart at `x`, locally the graph of a `C¹`
  function of one real variable.
* `Work.CriticalSet.LevelSetIsLocallyGraphOn u U c` — the same at every point of the level set
  `{u = c}` inside `U`.
* `Work.CriticalSet.IsRegularLevel E z₀ ε` — the exhaustion bundle: `0 < ε`,
  `IsRegularValueOn E (punctured z₀) ε`, `LevelSetIsLocallyGraphOn E (punctured z₀) ε`, and
  `IsCompact {x | ε ≤ E x}`.

## Main results

Discreteness and local finiteness (deliverable 1):

* `Work.CriticalSet.criticalSet_isDiscreteIn` — the critical set of a nowhere-locally-constant
  harmonic function is discrete in `U`; every point of `U` has a neighbourhood meeting it at most in
  that point.
* `Work.CriticalSet.criticalSet_isLocallyFinite` — the same in locally finite form
  (`IsLocallyFiniteIn`).
* `Work.CriticalSet.finite_criticalSet_inter_isCompact` — a compact subset of `U` contains only
  finitely many critical points.

The level set at a regular point (deliverable 2):

* `Work.CriticalSet.levelSet_isLocalGraph` — if `u` is harmonic at `x₀` and `x₀` is not critical,
  then `IsLocalLevelGraphAt u x₀` (implicit function theorem in `ℝ²`).

Critical values and regular values (deliverable 3):

* `Work.CriticalSet.countable_criticalSet_of_hasGreenFunctionWeak`,
  `Work.CriticalSet.countable_criticalValues_of_hasGreenFunctionWeak` — for a weak Green function the
  critical points, hence the critical values, are countable (a discrete set in a second countable
  space is countable: `countable_of_isDiscreteIn`).
* `Work.CriticalSet.notLocallyConstantOn_of_hasGreenFunctionWeak` — a weak Green function on a
  non-compact surface is nowhere locally constant on `X ∖ {z₀}`.
* `Work.CriticalSet.isPreconnected_punctured` — `X ∖ {z₀}` is preconnected
  (from `Work.Modulus.puncturedConnected`).
* `Work.CriticalSet.exists_regularLevel_isCompact_manifold` — the headline: for `HasGreenFunctionWeak
  z₀ E` on a non-compact connected second countable Riemann surface and every `ε₀ > 0`, there is
  `ε < ε₀` with `IsRegularLevel E z₀ ε`.  `exists_regularLevel_of_nonconstant` is the same with the
  nonconstancy hypothesis instead of non-compactness.
* `Work.CriticalSet.exists_pos_le_on_isCompact` — every compact subset of `X ∖ {z₀}` is contained in
  some `{E ≥ ε}` with `ε > 0`, i.e. the superlevel sets exhaust the punctured surface.
* `Work.CriticalSet.frontier_superlevel_subset_levelSet` — the boundary of `{E ≥ ε}` (away from
  `z₀`) lies in the level set `{E = ε}`; at a *regular* value `ε` the two coincide (away from `z₀`),
  `Work.CriticalSet.frontier_superlevel_eq_levelSet_of_regularValue`.

Supporting calculus:

* `Work.CriticalSet.chart_transition_deriv_ne_zero` — chart transitions have non-vanishing complex
  derivative.
* `Work.CriticalSet.fderiv_re_eq_zero_iff` — for a complex analytic `F`, the real derivative of
  `w ↦ (F w).re` vanishes at `z` iff `deriv F z = 0`.
* `Work.CriticalSet.eventually_deriv_ne_zero_of_not_eventually_re_eq` — zeros of `F'` are isolated
  unless `Re F` is locally constant.
* `Work.CriticalSet.criticalPoint_iff_chartAt` — chart independence of criticality.
* `Work.CriticalSet.criticalPoint_iff_companion` — `x` is critical for `u` iff some local holomorphic
  companion of `u` has vanishing derivative at `x`.
* `Work.CriticalSet.eventually_eq_of_mem_closure_locallyConstant` — the locus where a harmonic
  function is locally constant is closed at every point of harmonicity (the identity theorem for
  harmonic functions behind the nonconstancy result below).

Holomorphic Sard substitute (for the disc-filling/period arguments, where the relevant maps are
holomorphic rather than merely continuous):

* `Work.CriticalSet.analytic_exists_regularValue_near` — for `f` analytic and nowhere locally
  constant on an open `U ⊆ ℂ`, regular values are dense in `ℂ`.
* `Work.CriticalSet.analytic_finite_preimage_of_regularValue` — a regular value of such an `f` has
  finitely many preimages in a compact disc on which `f` is analytic.

## Not provided

A Sard-type statement for merely `C¹` (or `C^∞`) maps `𝔻̄ → ℂ` which are not holomorphic is **not**
provided: that is a genuine theorem of real analysis which is absent from Mathlib.  The substitutes
above cover the holomorphic case; for the harmonic Green function itself the critical set is discrete
by the results of this chapter.
-/
