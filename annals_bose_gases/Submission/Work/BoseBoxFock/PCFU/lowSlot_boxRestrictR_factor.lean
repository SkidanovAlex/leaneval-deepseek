import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.dictBricks
import Submission.Work.BoseBoxFock.PotContactChemAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.lowSlot_boxRestrictR_factor`

The box restriction `boxRestrictR ℓ Φ = Φ · 1_{abox n ℓ}` is the identity on the centred box, and
the slot update of a box configuration with a cube element stays in the box.  Consequently the
slot-`j` low-momentum symbol of the pair operator `aQ ℓ j ∘ aP ℓ i` (for `i ≠ j`) cannot see the
difference between `boxRestrictR ℓ Φ` and `Φ`:

    lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i (boxRestrictR ℓ Φ))) x
      = lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Φ)) x      (x ∈ abox n ℓ) .

Since `lowSlot` only reads its state through `(acube ℓ).indicator ·` (the cut-off inside `lowMult`),
it suffices to compare the two functions on `acube ℓ`, where the slot-`j` update `x[j ↦ z]` is a box
configuration, and the two `aP`/`aQ` towers agree there (`aP_boxRestrictR`,
`aP_aP_boxRestrictR`).

The requested factorisation is then the pointwise case split on `x ∈ abox n ℓ`: on the box the
multiplier `boxRestrictR ℓ Φ x` is `Φ x` (and the indicator on the right is `1`), off the box both
sides vanish.

Everything below is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

open Submission.BoseGases

/-! ## 1. The low slot only depends on the state through the cube indicator -/

/-- `lowMult` reads its state only through `(acube ℓ).indicator ·`: the window is applied inside
`lowMult` (`kinFT (1_{acube ℓ} · ψ)`), so two states with the same cube restriction give the same
value. -/
lemma lowMult_indicator_congr (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) {ψ₁ ψ₂ : Ω → ℝ}
    (h : (acube ℓ).indicator ψ₁ = (acube ℓ).indicator ψ₂) (y : Ω) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ₁ y = Work.BoseBoxFix.lowMult fc κ ℓ ψ₂ y := by
  unfold Work.BoseBoxFix.lowMult
  rw [h]

/-- `lowSlot` reads its state only through `(acube ℓ).indicator (· ∘ (x[j ↦ ·]))`. -/
lemma lowSlot_indicator_congr (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) {n : ℕ} (j : Fin n)
    {Ψ₁ Ψ₂ : X n → ℝ} {x : X n}
    (h : (acube ℓ).indicator (fun z : Ω => Ψ₁ (Function.update x j z))
        = (acube ℓ).indicator (fun z : Ω => Ψ₂ (Function.update x j z))) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ₁ x = Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ₂ x := by
  simp only [Work.BoseBoxFix.lowSlot]
  exact lowMult_indicator_congr fc κ ℓ h (x j)

/-! ## 2. The pair operator `aQ ℓ j ∘ aP ℓ i` of the box restriction agrees with that of `Φ` -/

/-- **The nested slot mean of the box restriction, on the box.** -/
lemma aP_aP_boxRestrictR' {n : ℕ} {ℓ : ℝ} (i j : Fin n) (Φ : X n → ℝ) {y : X n}
    (hy : y ∈ abox n ℓ) :
    aP ℓ j (aP ℓ i (boxRestrictR ℓ Φ)) y = aP ℓ j (aP ℓ i Φ) y := by
  unfold aP
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ) (fun w hw => ?_)
  exact aP_boxRestrictR i Φ (update_mem_abox hy hw)

/-- **The pair operator `aQ ℓ j ∘ aP ℓ i` of the box restriction is that of `Φ`, on the box.** -/
lemma aQ_aP_boxRestrictR {n : ℕ} {ℓ : ℝ} (i j : Fin n) (Φ : X n → ℝ) {y : X n}
    (hy : y ∈ abox n ℓ) :
    aQ ℓ j (aP ℓ i (boxRestrictR ℓ Φ)) y = aQ ℓ j (aP ℓ i Φ) y := by
  have h2 := aP_aP_boxRestrictR' i j Φ hy
  unfold aQ
  rw [aP_boxRestrictR i Φ hy, h2]

/-! ## 3. The low slot of the pair operator of the box restriction -/

/-- **The `lowSlot` identity on the box**: for `x ∈ abox n ℓ` the slot-`j` low-momentum symbol of
`aQ ℓ j (aP ℓ i (boxRestrictR ℓ Φ))` is that of `aQ ℓ j (aP ℓ i Φ)`. -/
lemma lowSlot_boxRestrictR_agree {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    (i j : Fin n) (Φ : X n → ℝ) {x : X n} (hx : x ∈ abox n ℓ) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i (boxRestrictR ℓ Φ))) x
      = Work.BoseBoxFix.lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Φ)) x := by
  refine lowSlot_indicator_congr fc κ ℓ j ?_
  funext z
  by_cases hz : z ∈ acube ℓ
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    exact aQ_aP_boxRestrictR i j Φ (update_mem_abox hx hz)
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

/-! ## 4. The requested factorisation -/

theorem lowSlot_boxRestrictR_factor {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    (i j : Fin n) (hij : i ≠ j) (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    Work.BoseBoxFock.boxRestrictR ℓ Φ x
        * Work.BoseBoxFix.lowSlot fc κ ℓ j
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
              (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x
      = ((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x) * Φ x
          * Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ)) x := by
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · have hxr : Work.BoseBoxFock.boxRestrictR ℓ Φ x = Φ x := by
      have h : Work.BoseBoxFock.boxRestrictR ℓ Φ x
          = Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x := rfl
      rw [h, Set.indicator_of_mem hx, mul_one]
    rw [hxr, lowSlot_boxRestrictR_agree fc κ ℓ i j Φ hx]
    simp only [Set.indicator_of_mem hx, one_mul]
  · have hxr : Work.BoseBoxFock.boxRestrictR ℓ Φ x = 0 := by
      have h : Work.BoseBoxFock.boxRestrictR ℓ Φ x
          = Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x := rfl
      rw [h, Set.indicator_of_notMem hx, mul_zero]
    rw [hxr]
    simp only [Set.indicator_of_notMem hx, zero_mul]

end Work.BoseBoxFock.PCFU
