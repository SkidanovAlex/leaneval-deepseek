import Mathlib
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances

/-!
# `Work.EKLRelCross.flowerSet_borel` — the flower set is Borel

The flower set `flowerSet U δ B W` is, by `flowerSet_eq_image`, the image of
`(V δ ∩ U) ×ˢ (B ∩ W)` under the action map `(v, x) ↦ v • x`.  The action map is continuous
(`ContinuousSMul` on the quotient `X₃ = SL₃(ℝ)/Γ₃`), and it is *injective* on that set because
`B` is a `U`-cross-section: if `v • x = v' • x'` with `x, x' ∈ B` and `v, v' ∈ U`, then
`(v⁻¹v') • x' = x ∈ B`, so `v⁻¹v' = 1`.  The Lusin–Souslin theorem
(`MeasurableSet.image_of_continuousOn_injOn`) then gives that the image is Borel: the source is a
Borel subset of the Polish space `SL₃(ℝ) × X₃`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract
open Work.EKLContract.Lemmas

/-- **The flower set is Borel.**  For a closed subgroup `U ≤ SL₃(ℝ)`, a `U`-cross-section `B`
and a Borel set `W`, the "flower" `flowerSet U δ B W` — the `(V δ)⁻¹ ∩ U`-collar of `B ∩ W` —
is a Borel subset of `X₃`. -/
theorem flowerSet_borel (h2 : Work.EKLContract.P_X3) {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {B W : Set Work.EKLContract.X3} (hB : MeasurableSet B) (hW : MeasurableSet W)
    (hCS : ∀ x ∈ B, ∀ u ∈ U, u • x ∈ B → u = 1) (δ : ℝ) :
    MeasurableSet (Work.EKLRelCross.flowerSet U δ B W) := by
  rw [flowerSet_eq_image]
  have : PolishSpace SL3 := polishSpace_specialLinearGroup
  haveI : PolishSpace X3 := h2.2.1
  refine MeasurableSet.image_of_continuousOn_injOn ?_ continuous_smul.continuousOn ?_
  · -- the source is Borel
    have hVm : MeasurableSet (V δ ∩ (U : Set SL3)) :=
      (isOpen_V δ).measurableSet.inter hUcl.measurableSet
    exact hVm.prod (hB.inter hW)
  · -- the action map is injective on the source (cross-section property)
    rintro ⟨v, x⟩ ⟨hv, hx⟩ ⟨v', x'⟩ ⟨hv', hx'⟩ heq
    change v • x = v' • x' at heq
    obtain ⟨_, hvU⟩ := hv
    obtain ⟨_, hv'U⟩ := hv'
    obtain ⟨hxB, _⟩ := hx
    obtain ⟨hx'B, _⟩ := hx'
    have hmul : (v⁻¹ * v') • x' = x := by
      rw [mul_smul, ← heq, inv_smul_smul]
    have hmulU : v⁻¹ * v' ∈ U := U.mul_mem (U.inv_mem hvU) hv'U
    have hmemB : (v⁻¹ * v') • x' ∈ B := by rw [hmul]; exact hxB
    have hone : v⁻¹ * v' = 1 := hCS x' hx'B (v⁻¹ * v') hmulU hmemB
    have hvv : v = v' := inv_mul_eq_one.mp hone
    have hxx : x = x' := by
      rw [← hvv] at heq
      exact smul_left_cancel v heq
    rw [hvv, hxx]

end Work.EKLRelCross
