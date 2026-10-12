import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.assembly_of_row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotContactChemAux` — the state transfer of the box counts

The box counts `cS1C`, `cS2C` (`slotCountsComplex`) are the slot-mean counts of a **complex** box
state; the corpus's `cS1`, `cS2` are those of a **real** box state.  The row table `FormW2Bpot`
evaluates its left-hand side at the *box restriction* `Θ = boxRestrictC ℓ Φ` of a real `BoxState
Φ`, so the transfer

    `cS1C ℓ (boxRestrictC ℓ Φ) = cS1 ℓ Φ`,  `cS2C ℓ (boxRestrictC ℓ Φ) = cS2 ℓ Φ`

is needed.  The restriction is a red herring: on the centred box `abox n ℓ` the indicator of
`boxRestrictR` is `1` (the slot update `x[i↦y]` of a box configuration and a cube element is again
in the box), so the slot means of `boxRestrictR ℓ Φ` and of `Φ` agree pointwise on `abox n ℓ`, and
the counts — which integrate over `abox n ℓ` — agree.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases

/-- The slot update of a box configuration with a cube element is a box configuration. -/
lemma update_mem_abox {n : ℕ} {ℓ : ℝ} {x : X n} (hx : x ∈ abox n ℓ) {i : Fin n} {y : Ω}
    (hy : y ∈ acube ℓ) : Function.update x i y ∈ abox n ℓ := by
  intro j
  by_cases hji : j = i
  · subst hji
    rwa [Function.update_self]
  · rw [Function.update_of_ne hji]
    exact hx j

/-- **The slot means of `boxRestrictR ℓ Φ` and of `Φ` agree on the box.** -/
lemma aP_boxRestrictR {n : ℕ} {ℓ : ℝ} (i : Fin n) (Φ : X n → ℝ) {x : X n}
    (hx : x ∈ abox n ℓ) :
    aP ℓ i (boxRestrictR ℓ Φ) x = aP ℓ i Φ x := by
  unfold aP boxRestrictR
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ) (fun y hy => ?_)
  have hupd : Function.update x i y ∈ abox n ℓ := update_mem_abox hx hy
  rw [Set.indicator_of_mem hupd, mul_one]

/-- The double slot mean of `boxRestrictR ℓ Φ` is that of `Φ`, pointwise on the box. -/
lemma aP_aP_boxRestrictR {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) (Φ : X n → ℝ) {x : X n}
    (hx : x ∈ abox n ℓ) :
    aP ℓ p.1 (aP ℓ p.2 (boxRestrictR ℓ Φ)) x = aP ℓ p.1 (aP ℓ p.2 Φ) x := by
  unfold aP
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ) (fun y hy => ?_)
  exact aP_boxRestrictR p.2 Φ (update_mem_abox hx hy)

/-- **The box restriction of a real state has the same condensate count.** -/
theorem cS1C_boxRestrictC {n : ℕ} {ℓ : ℝ} (Φ : X n → ℝ) :
    cS1C ℓ (boxRestrictC ℓ Φ) = cS1 ℓ Φ := by
  rw [boxRestrictC_eq_ofReal, cS1C_ofReal]
  unfold cS1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine MeasureTheory.setIntegral_congr_fun (abox_measurable n ℓ) (fun x hx => ?_)
  rw [aP_boxRestrictR i Φ hx]

/-- **The box restriction of a real state has the same pair-condensate count.** -/
theorem cS2C_boxRestrictC {n : ℕ} {ℓ : ℝ} (Φ : X n → ℝ) :
    cS2C ℓ (boxRestrictC ℓ Φ) = cS2 ℓ Φ := by
  rw [boxRestrictC_eq_ofReal, cS2C_ofReal]
  unfold cS2
  refine Finset.sum_congr rfl fun p _ => ?_
  refine MeasureTheory.setIntegral_congr_fun (abox_measurable n ℓ) (fun x hx => ?_)
  rw [aP_aP_boxRestrictR p Φ hx]

end Work.BoseBoxFock
