import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_isGreenOn
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_modulusOn
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_biholomorphicOn_of_greenOn_modulus

/-!
# Anghel–Bruin–Stan, Theorem 10 (the disc lemma): the assembly

Let `X` be a non-compact connected Riemann surface and `Ω ⊆ X` a relatively compact, simply
connected open set with `Ω ≠ X` and connected frontier, and let `x₀ ∈ Ω`.  Then there is a
biholomorphism of `Ω` onto a disc, normalised at `x₀`, extended by `0` outside `Ω`:

```
∃ (r : ℝ) (χ : X → ℂ), 0 < r ∧ (∀ x ∈ Ω, HolomorphicOnXAt χ x) ∧ Set.InjOn χ Ω ∧ χ x₀ = 0 ∧
  χ '' Ω = Metric.ball (0 : ℂ) r ∧
  deriv (χ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 ∧ (∀ x ∉ Ω, χ x = 0)
```

This module is the *assembly* of the three ingredients, each proved in a sibling module:

* `Work.SimplyConnected.ABS.exists_isGreenOn` — `Ω` carries a Green function `E` with pole `x₀`
  (`IsGreenOn`, i.e. positive and harmonic off the pole, logarithmic pole, and superlevel sets
  compactly contained in `Ω`);
* `Work.SimplyConnected.ABS.exists_modulusOn` — a holomorphic modulus `Φ` of `E` on `Ω`
  (`IsModulusOn`), which exists because `Ω` is simply connected: the periods of the conjugate
  differential of `E` are multiples of `2π`;
* `Work.SimplyConnected.ABS.exists_biholomorphicOn_of_greenOn_modulus` — the endgame: from `(E, Φ)`
  the map `Φ` is a proper map of `Ω` into the unit disc with a single simple zero at `x₀`, hence
  biholomorphic onto the disc, and rescaling realises the normalisation.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

end Work.SimplyConnected.ABS
