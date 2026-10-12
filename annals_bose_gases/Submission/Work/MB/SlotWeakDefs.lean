import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.FibreProjDefs
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.SlotWeakDefs` — the box support sets of the measurable/bounded slot calculus

The measurable/bounded ("weak") line of the box ↔ model bridge replaces the *continuous*,
*compactly supported* mode hypotheses of the strong chain by

* `Measurable (e l)`,
* `∃ C, ∀ x, ‖e l x‖ ≤ C` (everywhere bounded),
* `Function.support (e l) ⊆ boxL ℓ` (supported in the corpus box),

and the state hypotheses by measurability, everywhere boundedness, and support inside the
`n`-particle box.  The support sets occurring in the statements are

* `Work.BoseK15.corpusBox.boxL ℓ` — the one-particle box `Λ(ℓ) = ℓ • cell` (the corpus `boxL`);
* `boxPow n ℓ` — its `n`-fold product, the support of the `n`-particle box states.

For `0 < ℓ` one has `boxL ℓ = acube ℓ` (`Work.BoseBoxFock.boxL_eq_acube`), hence
`boxPow n ℓ = Submission.BoseGases.abox n ℓ` (`Submission.BoseGases.abox_eq_pi_acube`); the
statements below are nevertheless phrased with `boxPow` so that they hold for **every** `ℓ`
(the product of the boxes is the geometrically correct support set of the slot calculus).
-/

namespace Work.MB

open MeasureTheory

/-- `boxPow n ℓ` is the `n`-fold product of the one-particle box
`Work.BoseK15.corpusBox.boxL ℓ`: the support of the `n`-particle box states of the slot
calculus. -/
def boxPow (n : ℕ) (ℓ : ℝ) : Set (Fin n → EuclideanSpace ℝ (Fin 3)) :=
  Set.univ.pi (fun _ : Fin n => Work.BoseK15.corpusBox.boxL ℓ)

end Work.MB
