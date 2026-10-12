import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.n0SpectralAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The single-slot operator** of `n0Iter`: at slot `i` it is `P_{B,i}` when `b i = true` and
the pointwise complement `1 − P_{B,i}` when `b i = false`. -/
noncomputable def n0Slot {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) (i : Fin N)
    (Ψ : X N → ℝ) : X N → ℝ :=
  if b i then (fun x => UBBInputs8.boxPInd volA A i Ψ x)
  else (fun x => Ψ x - UBBInputs8.boxPInd volA A i Ψ x)

/-- **One-step unfolding** of `n0Iter` in terms of `n0Slot`. -/
theorem n0Iter_cons {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) (i : Fin N)
    (l : List (Fin N)) (Ψ : X N → ℝ) :
    n0Iter volA A b (i :: l) Ψ = n0Iter volA A b l (n0Slot volA A b i Ψ) := by
  rw [n0Iter]
  unfold n0Slot
  by_cases hb : b i = true
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb]

/-- The `true` branch of `n0Slot`. -/
theorem n0Slot_eq_true {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) (i : Fin N)
    (Ψ : X N → ℝ) (h : b i = true) :
    n0Slot volA A b i Ψ = UBBInputs8.boxPInd volA A i Ψ := by
  unfold n0Slot
  rw [if_pos h]

/-- The `false` branch of `n0Slot`. -/
theorem n0Slot_eq_false {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) (i : Fin N)
    (Ψ : X N → ℝ) (h : b i = false) :
    n0Slot volA A b i Ψ = Ψ - UBBInputs8.boxPInd volA A i Ψ := by
  unfold n0Slot
  rw [if_neg (by simp [h])]
  funext x
  rfl

/-- The `true` branch of `n0Slot`, pointwise. -/
theorem n0Slot_apply_true {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) (i : Fin N)
    (Ψ : X N → ℝ) (h : b i = true) (x : X N) :
    n0Slot volA A b i Ψ x = UBBInputs8.boxPInd volA A i Ψ x := by
  unfold n0Slot
  rw [if_pos h]

/-- The `false` branch of `n0Slot`, pointwise. -/
theorem n0Slot_apply_false {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) (i : Fin N)
    (Ψ : X N → ℝ) (h : b i = false) (x : X N) :
    n0Slot volA A b i Ψ x = Ψ x - UBBInputs8.boxPInd volA A i Ψ x := by
  unfold n0Slot
  rw [if_neg (by simp [h])]

/-- `GoodState` (measurable, bounded on the analysis box) is preserved by every slot operator. -/
theorem goodState_n0Slot {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (i : Fin N) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) : GoodState ℓ (n0Slot volA A b i Ψ) := by
  by_cases h : b i = true
  · rw [n0Slot_eq_true volA A b i Ψ h]
    exact goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
  · rw [show n0Slot volA A b i Ψ = Ψ - UBBInputs8.boxPInd volA A i Ψ from
      n0Slot_eq_false volA A b i Ψ (by simpa using h)]
    exact BoxNice.sub hΨ (BoxNice.boxPInd hℓ hvol hA hvolA hAc i hΨ)

/-- A `Bool` that is not `true` is `false` (case-split convenience for `n0Slot`). -/
theorem bool_eq_false_of_not_eq_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

/-- A `Bool` that is not `false` is `true` (case-split convenience for `n0Slot`). -/
theorem bool_eq_true_of_not_eq_false {b : Bool} (h : ¬ b = false) : b = true := by
  cases b <;> simp_all

/-- `GoodState` is preserved by the whole slot iteration. -/
theorem goodState_n0Iter {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (l : List (Fin N)) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) : GoodState ℓ (n0Iter volA A b l Ψ) :=
  BoxNice.iter hℓ hvol hA hvolA hAc b hΨ l

end Work.BoseFixB1S
