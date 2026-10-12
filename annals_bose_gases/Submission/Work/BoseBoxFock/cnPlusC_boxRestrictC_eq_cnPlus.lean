import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotContactChemAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The excited count of the box restriction is the corpus's excited count

This is the `n₊`-row companion of `Work.BoseBoxFock.cS1C_boxRestrictC` /
`cS2C_boxRestrictC` (`PotContactChemAux.lean`): the complex slot count `cnPlusC` evaluated at the
complex box restriction `boxRestrictC ℓ Φ` of a **real** box state `Φ` is the corpus's real
excited count `cnPlus ℓ Φ`.

As for `cS1C`/`cS2C` the argument is purely pointwise and needs **no** measurability or
integrability hypothesis:

* `boxRestrictC ℓ Φ = (boxRestrictR ℓ Φ : ℂ)`, so `cnPlusC_ofReal` reduces the claim to the real
  box restriction `boxRestrictR ℓ Φ`;
* on the centred box the restriction is the identity (`boxRestrictR ℓ Φ x = Φ x` for
  `x ∈ abox n ℓ`), and the slot update `x[i ↦ y]` of a box configuration with a cube element is
  again a box configuration (`update_mem_abox`), so `aP` — an average over `acube ℓ` of the
  updated configuration — agrees for the restriction and for `Φ` (`aP_boxRestrictR`), hence so
  does the complementary slot `aQ = id − aP`;
* both counts integrate over `abox n ℓ`, and `setIntegral_congr_fun` turns pointwise agreement
  there into equality of the integrals.

Everything is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases

/-- **The complementary slot of the real box restriction is the corpus's `aQ`, on the box.** -/
lemma aQ_boxRestrictR {n : ℕ} {ℓ : ℝ} (i : Fin n) (Φ : X n → ℝ) {x : X n}
    (hx : x ∈ abox n ℓ) : aQ ℓ i (boxRestrictR ℓ Φ) x = aQ ℓ i Φ x := by
  have hval : boxRestrictR ℓ Φ x = Φ x := by
    unfold boxRestrictR
    rw [Set.indicator_of_mem hx, mul_one]
  unfold aQ
  rw [hval, aP_boxRestrictR i Φ hx]

/-- **The excited count of the box restriction of a real state.** -/
theorem cnPlusC_boxRestrictC_eq_cnPlus {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseBoxFock.cnPlusC ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ)
      = Submission.BoseGases.cnPlus ℓ Φ := by
  rw [boxRestrictC_eq_ofReal, cnPlusC_ofReal]
  unfold Submission.BoseGases.cnPlus
  refine Finset.sum_congr rfl fun i _ => ?_
  refine MeasureTheory.setIntegral_congr_fun (abox_measurable n ℓ) (fun x hx => ?_)
  rw [aQ_boxRestrictR i Φ hx]

end Work.BoseBoxFock
