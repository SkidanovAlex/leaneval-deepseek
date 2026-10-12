import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.slITube_le_one`

For `0 < h`, the set of centres `u` whose sliding interval
`slI ℓ h u = Icc (max (-ℓ/2) (h*u - h/2)) (min (ℓ/2) (h*u + h/2))` contains a fixed
point `x` has Lebesgue measure at most `1`: membership forces
`h*u - h/2 ≤ x ≤ h*u + h/2`, i.e. `u ∈ Icc (x/h - 1/2) (x/h + 1/2)`, an interval of
length `1`.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1.Core

theorem slITube_le_one {ℓ h x : ℝ} (hh : 0 < h) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      {u : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h u} ≤ 1 := by
  have hsub : {u : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h u}
      ⊆ Set.Icc (x / h - 1 / 2) (x / h + 1 / 2) := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu
    rw [Work.BoseFixB1S.slI_eq] at hu
    simp only [Set.mem_inter_iff, Set.mem_Icc] at hu
    -- the ℓ-clipping is discarded, only the sliding window matters
    obtain ⟨⟨-, -⟩, ⟨h1, h2⟩⟩ := hu
    simp only [Set.mem_Icc]
    have hplus : (x + h / 2) / h = x / h + 1 / 2 := by field_simp
    have hminus : (x - h / 2) / h = x / h - 1 / 2 := by field_simp
    constructor
    · rw [← hminus]
      exact (div_le_iff₀ hh).mpr (by linarith)
    · rw [← hplus]
      exact (le_div_iff₀ hh).mpr (by linarith)
  calc (MeasureTheory.volume : MeasureTheory.Measure ℝ) {u : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h u}
      ≤ MeasureTheory.volume (Set.Icc (x / h - 1 / 2) (x / h + 1 / 2)) :=
        MeasureTheory.measure_mono hsub
    _ = ENNReal.ofReal ((x / h + 1 / 2) - (x / h - 1 / 2)) := Real.volume_Icc
    _ = 1 := by
        rw [show x / h + 1 / 2 - (x / h - 1 / 2) = 1 by ring]
        exact ENNReal.ofReal_one

end Work.BoseFixB1.Core
