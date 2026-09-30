import Mathlib
import Submission.Work.BW.multiplicity_engine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A reduced data package for the transversal exclusion (`ε = true`)

`Work.BW.multiplicity_engine` proves the transversal exclusion `ze_bad_true` for the full
`ZEData` package, which carries the logarithmic-form data `B`, `ℓ`, `𝒮` and the exclusion
conditions (E0), (E2), (E3) — none of which is used by the argument.

Downstream (e.g. `Work.BW.transversal_true_gen`) one wants the same exclusion with the cyclic
point `exp ∘ ℓ` replaced by an *arbitrary* family `ℓ : Fin N → ℂ` (the point `θ`), and with only
the hypotheses the proof actually consumes. This file collects exactly those hypotheses in the
small structure `ZEDataG`, so that the cancellation/exclusion lemmas can be stated for it.
-/

namespace Work.BW

open scoped BigOperators

/-- The hypotheses consumed by the transversal exclusion in the `ε = true` case, in the
dimension `N` in which the zero estimate is applied, with an arbitrary cyclic family
`ℓ : Fin N → ℂ`:

* `hNr` — the ambient dimension dominates the zero-estimate dimension;
* `δ` — the degree bounds, with `hδnn`, `hδ1` (integrality: `⌊δ i⌋₊ ≥ 1`);
* `Sq`, `Tq` — the step sequences, nonincreasing along `m < N` (`hSa`, `hTa`);
* `hE1` — the exclusion condition (E1);
* `ℓ` — the coordinates of the point `θ` (no arithmetic hypothesis is needed). -/
structure ZEDataG (N r : ℕ) where
  hNr : N ≤ r
  δ : Fin (N + 1) → ℝ
  hδnn : ∀ i, 0 ≤ δ i
  hδ1 : ∀ i, 1 ≤ ⌊δ i⌋₊
  Sq : ℕ → ℕ
  Tq : ℕ → ℕ
  hSa : ∀ m, m < N → Sq (m + 1) ≤ Sq m
  hTa : ∀ m, m < N → Tq (m + 1) ≤ Tq m
  hE1 : ∀ m, m < r → ∀ e : Fin (N + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, δ i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ)
  ℓ : Fin N → ℂ

end Work.BW
