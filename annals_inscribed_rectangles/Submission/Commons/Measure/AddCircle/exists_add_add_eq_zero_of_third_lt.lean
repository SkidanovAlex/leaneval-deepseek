import Mathlib
import Submission.Commons.Measure.AddCircle.kemperman_open

namespace Commons.Measure.AddCircle

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

/-- **Kemperman/Raikov for the circle, `1/3` form**: if `U` is a nonempty open subset of the
additive circle `ℝ/ℤ` whose normalised Haar measure exceeds `1/3`, then there are `a, b, c ∈ U`
with `a + b + c = 0`. -/
theorem exists_add_add_eq_zero_of_third_lt {U : Set UnitAddCircle} (hU : IsOpen U)
    (hUne : U.Nonempty) (h : (1 / 3 : ℝ) < volume.real U) :
    ∃ a ∈ U, ∃ b ∈ U, ∃ c ∈ U, a + b + c = 0 := by
  -- Real-valued Kemperman inequality, obtained from the `ℝ≥0∞`-valued commons lemma.
  have hkem_real : min 1 (volume.real U + volume.real U) ≤ volume.real (U + U) := by
    have hk := kemperman_open hU hU hUne hUne
    have hUfin : volume U ≠ ⊤ := measure_ne_top _ _
    have hUUfin : volume (U + U) ≠ ⊤ := measure_ne_top _ _
    have hsum_fin : volume U + volume U ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hUfin, hUfin⟩
    have hk' := ENNReal.toReal_mono hUUfin hk
    rw [ENNReal.toReal_min ENNReal.one_ne_top hsum_fin, ENNReal.toReal_one,
      ENNReal.toReal_add hUfin hUfin] at hk'
    exact hk'
  by_contra hcon
  have hdisj : Disjoint (U + U) (-U) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, b, hb, rfl⟩ hx
    rw [Set.mem_neg] at hx
    exact hcon ⟨a, ha, b, hb, -(a + b), hx, by abel⟩
  have hmeas_neg : MeasurableSet (-U) := hU.measurableSet.neg
  have h1 : volume.real (U + U) + volume.real (-U) ≤ 1 := by
    have hsub : (U + U) ∪ (-U) ⊆ (Set.univ : Set UnitAddCircle) := fun _ _ => trivial
    have h2 : volume.real ((U + U) ∪ (-U)) ≤ volume.real (Set.univ : Set UnitAddCircle) :=
      measureReal_mono hsub (by finiteness)
    rw [measureReal_union hdisj hmeas_neg (by finiteness) (by finiteness)] at h2
    have h3 : volume.real (Set.univ : Set UnitAddCircle) = 1 := by
      rw [measureReal_def, AddCircle.measure_univ]
      simp
    rw [h3] at h2
    exact h2
  have hneg : volume.real (-U) = volume.real U := by
    rw [measureReal_def, measureReal_def, Measure.measure_neg]
  rw [hneg] at h1
  have h2 : (2 / 3 : ℝ) < volume.real (U + U) := by
    have h3 : volume.real U + volume.real U = 2 * volume.real U := by ring
    rw [h3] at hkem_real
    rcases le_total (2 * volume.real U) 1 with hlt | hlt
    · rw [min_eq_right hlt] at hkem_real; linarith
    · rw [min_eq_left hlt] at hkem_real; linarith
  linarith

end

end Commons.Measure.AddCircle
