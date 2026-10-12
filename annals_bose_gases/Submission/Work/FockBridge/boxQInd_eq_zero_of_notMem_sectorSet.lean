import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FockBridge

open MeasureTheory

/-- **Locality of the fibre integral defining `P_{B,i}`.**  If `Φ` vanishes off the `A`-sector of
count `k` and `x` lies outside that sector, then FS's mean-free projection `Q_{B,i}Φ` also vanishes
at `x`: the box-indicator term is killed by `Φ x = 0` and the fibre integral
`∫_{A} Φ(x[i↦z])` vanishes pointwise because replacing slot `i` by a point `z ∈ A` — when the
original `x i` is already in `A` — keeps the occupancy, hence keeps `x[i↦z]` out of the sector. -/
theorem boxQInd_eq_zero_of_notMem_sectorSet {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) {volA : ℝ} (i : Fin N) {k : ℕ}
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hΦ : ∀ x : Fin N → EuclideanSpace ℝ (Fin 3),
      x ∉ Work.FockBridge.sectorSet A k → Φ x = 0)
    {x : Fin N → EuclideanSpace ℝ (Fin 3)} (hx : x ∉ Work.FockBridge.sectorSet A k) :
    Work.UBBInputs8.boxQInd volA A i Φ x = 0 := by
  have hP : Work.UBBInputs8.boxPInd volA A i Φ x = 0 := by
    rw [Work.UBBInputs8.boxPInd]
    by_cases hxi : x i ∈ A
    · have hzero : A.indicator (fun z => Φ (Function.update x i z)) = (fun _ => (0 : ℝ)) := by
        funext z
        by_cases hz : z ∈ A
        · rw [Set.indicator_of_mem hz]
          exact hΦ _ (fun hmem =>
            hx ((Work.FockBridge.mem_sectorSet_update_of_mem A hz hxi).mp hmem))
        · rw [Set.indicator_of_notMem hz]
      have hInt : (∫ z in A, Φ (Function.update x i z)) = 0 := by
        rw [← integral_indicator hA]
        rw [hzero]
        simp
      rw [hInt, Set.indicator_of_mem hxi]
      ring
    · rw [Set.indicator_of_notMem hxi]
      ring
  rw [Work.UBBInputs8.boxQInd, hP, hΦ x hx]
  ring

end Work.FockBridge
