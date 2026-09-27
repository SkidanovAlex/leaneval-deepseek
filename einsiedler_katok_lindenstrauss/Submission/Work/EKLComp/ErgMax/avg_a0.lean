import Mathlib
import Submission.Work.EKLComp.ErgMax.Basic

open MeasureTheory Topology Filter
open scoped ENNReal

namespace Work.EKLComp.ErgMax

open Work.EKLContract

noncomputable section

/-!
# `avg_a0` — the `A⁺`-average is invariant under `a₀`

The averaged measure `avg ν N` is a convex combination of the push-forwards
`(aDiag (shift N i j))_* ν`.  Each such push-forward is invariant under `act a₀`
whenever `ν` is: the maps `aDiag (shift N i j)` and `a₀ = aDiag a0v` are both
diagonal, hence commute, so pushing forward by `a₀` and pulling back by the
`aDiag (shift N i j)`-action cancel against `ν`'s `a₀`-invariance.
-/

/-- Diagonal elements of `A` commute. -/
theorem aDiag_mul_comm (s t : Fin 3 → ℝ) : aDiag s * aDiag t = aDiag t * aDiag s := by
  rw [aDiag_add, aDiag_add, add_comm]

/-- If `ν` is `act a₀`-invariant and `act g` commutes with `act a₀`, then the push-forward
`(act g)_* ν` is also `act a₀`-invariant. -/
theorem map_act_a0_of_comm {ν : Measure X3} (hν : MeasurePreserving (act a0) ν ν)
    {g : SL3} (hcomm : act g ∘ act a0 = act a0 ∘ act g) :
    (ν.map (act g)).map (act a0) = ν.map (act g) := by
  rw [Measure.map_map (measurable_act a0) (measurable_act g), ← hcomm,
    ← Measure.map_map (measurable_act g) (measurable_act a0), hν.map_eq]

/-- `aDiag (shift N i j)` commutes with `a₀`. -/
theorem aDiag_shift_mul_a0 (N i j : ℕ) :
    aDiag (shift N i j) * a0 = a0 * aDiag (shift N i j) := by
  rw [← aDiag_a0v]
  exact aDiag_mul_comm (shift N i j) a0v

/-- The `act`-maps of `aDiag (shift N i j)` and `a₀` commute. -/
theorem act_aDiag_shift_comm_a0 (N i j : ℕ) :
    act (aDiag (shift N i j)) ∘ act a0 = act a0 ∘ act (aDiag (shift N i j)) := by
  rw [← act_mul, ← act_mul, aDiag_shift_mul_a0]

/-- A finite sum of `act a₀`-invariant measures is `act a₀`-invariant. -/
theorem map_finset_sum_of {ι : Type*} [Fintype ι] (m : ι → Measure X3)
    (hm : ∀ i, (m i).map (act a0) = m i) :
    (∑ i, m i).map (act a0) = ∑ i, m i := by
  rw [Measure.map_finset_sum' (measurable_act a0).aemeasurable]
  exact Finset.sum_congr rfl (fun i _ => hm i)

/-- A scalar multiple of an `act a₀`-invariant measure is `act a₀`-invariant. -/
theorem map_smul_of {c : ℝ≥0∞} {μ : Measure X3} (hm : μ.map (act a0) = μ) :
    (c • μ).map (act a0) = c • μ := by
  rw [Measure.map_smul _ (measurable_act a0).aemeasurable, hm]

theorem avg_a0 (ν : MeasureTheory.Measure Work.EKLContract.X3) {N : ℕ} (hN : 1 ≤ N)
    (hν : MeasureTheory.MeasurePreserving (Work.EKLComp.ErgMax.act Work.EKLContract.a0) ν ν) :
    MeasureTheory.MeasurePreserving (Work.EKLComp.ErgMax.act Work.EKLContract.a0)
      (Work.EKLComp.ErgMax.avg ν N) (Work.EKLComp.ErgMax.avg ν N) := by
  refine ⟨measurable_act a0, ?_⟩
  have hinner : ∀ i j : ℕ, (ν.map (act (aDiag (shift N i j)))).map (act a0)
      = ν.map (act (aDiag (shift N i j))) :=
    fun i j => map_act_a0_of_comm hν (act_aDiag_shift_comm_a0 N i j)
  have hF : Measure.map (act a0)
        (∑ i : Fin (n N), ∑ j : Fin (n N), ν.map (act (aDiag (shift N i j))))
      = ∑ i : Fin (n N), ∑ j : Fin (n N), ν.map (act (aDiag (shift N i j))) := by
    apply map_finset_sum_of
    intro i
    apply map_finset_sum_of
    intro j
    exact hinner i j
  rw [avg_def, Measure.map_smul _ (measurable_act a0).aemeasurable, hF]

end

end Work.EKLComp.ErgMax
