import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chanA_canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.PCFU.aPSlotFacts` — the continuity-free slot algebra of `aP`/`aQ`

The cubic dictionary's channel assembly needs the slot combinatorics of the condensate projectors
`Pᵢ = aP ℓ i`, `Qᵢ = 1 − Pᵢ` at the *box restriction* `Θ = boxRestrictC ℓ Φ` of a state — which is
**not** continuous, so the corpus's `aP_const_in_coord` / `aP_pair_const_in_j`
(`Submission/Q0Sector.lean`, stated for continuous `Φ`) do not apply.  Their proofs, however, only
use the algebraic identity `update (update x i z) i y = update x i y`, so they hold verbatim without
any continuity hypothesis.  This file records the four facts the channel matches consume:

* `aP_self_update` — `Pᵢ` is constant in its own slot;
* `aP_pair_update` — `PᵢPⱼ` is constant in slot `j` (`i ≠ j`);
* `aP_comp_update_eq` — `Pᵢ` commutes with an update *in another slot*;
* `aQ_slot_update` — `Qⱼψ(x[j↦u]) = ψ(x[j↦u]) − Pⱼψ(x)`.

Everything is `sorry`-free.
-/

/-- **`aP` is constant in its own slot** (no continuity hypothesis on `Φ`).  The two integrals
differ by the algebraic identity `update (update x i z) i y = update x i y`. -/
theorem aP_self_update {n : ℕ} {ℓ : ℝ} (i : Fin n) (Φ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) (z : E3) :
    Submission.BoseGases.aP ℓ i Φ (Function.update x i z) = Submission.BoseGases.aP ℓ i Φ x := by
  simp only [Submission.BoseGases.aP]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp only [Function.update_apply, if_neg hk]

/-- **`PᵢPⱼ` is constant in slot `j`** (`i ≠ j`), without any continuity hypothesis. -/
theorem aP_pair_update {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (z : E3) :
    Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) (Function.update x j z)
      = Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x := by
  have hpt : ∀ y : E3, (Submission.BoseGases.aP ℓ j Φ) (Function.update (Function.update x j z) i y)
      = (Submission.BoseGases.aP ℓ j Φ) (Function.update x i y) := by
    intro y
    rw [← Function.update_comm hij y z x]
    exact aP_self_update j Φ (Function.update x i y) z
  simp only [Submission.BoseGases.aP]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  exact hpt y

/-- **`Pᵢ` commutes with an update in another slot** (`i ≠ j`): averaging the slot-`i` variable of
`Θ ∘ (·[j↦u])` is the same as averaging `Θ` at the configuration whose slot `j` is already `u`. -/
theorem aP_comp_update_eq {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (Θ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (u : E3) :
    Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j u)) x
      = Submission.BoseGases.aP ℓ i Θ (Function.update x j u) := by
  simp only [Submission.BoseGases.aP]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Function.update_comm hij y u x]

/-- **`Qⱼ` at an updated slot**: `Qⱼψ(x[j↦u]) = ψ(x[j↦u]) − Pⱼψ(x)`. -/
theorem aQ_slot_update {n : ℕ} {ℓ : ℝ} (j : Fin n) (ψ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) (u : E3) :
    Submission.BoseGases.aQ ℓ j ψ (Function.update x j u)
      = ψ (Function.update x j u) - Submission.BoseGases.aP ℓ j ψ x := by
  simp only [Submission.BoseGases.aQ, aP_self_update j ψ x]

end Work.BoseBoxFock.PCFU
