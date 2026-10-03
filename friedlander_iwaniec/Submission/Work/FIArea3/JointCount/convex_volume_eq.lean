import Mathlib

namespace Work.FIArea3.JointCount

theorem convex_volume_eq (S : Set ℝ) (hS : Convex ℝ S) (hne : S.Nonempty) (hb : Bornology.IsBounded S) : MeasureTheory.volume S = ENNReal.ofReal (sSup S - sInf S) := by
  have hbb : BddBelow S := hb.bddBelow
  have hba : BddAbove S := hb.bddAbove
  have hsub : S ⊆ Set.Icc (sInf S) (sSup S) := subset_Icc_csInf_csSup hbb hba
  have hIoo : Set.Ioo (sInf S) (sSup S) ⊆ S := by
    intro x hx
    obtain ⟨y, hyS, hyx⟩ := exists_lt_of_csInf_lt hne hx.1
    obtain ⟨z, hzS, hxz⟩ := exists_lt_of_lt_csSup hne hx.2
    exact hS.ordConnected.out hyS hzS ⟨hyx.le, hxz.le⟩
  refine le_antisymm ?_ ?_
  · calc MeasureTheory.volume S
        ≤ MeasureTheory.volume (Set.Icc (sInf S) (sSup S)) := MeasureTheory.measure_mono hsub
      _ = ENNReal.ofReal (sSup S - sInf S) := Real.volume_Icc
  · calc ENNReal.ofReal (sSup S - sInf S)
        = MeasureTheory.volume (Set.Ioo (sInf S) (sSup S)) := Real.volume_Ioo.symm
      _ ≤ MeasureTheory.volume S := MeasureTheory.measure_mono hIoo

end Work.FIArea3.JointCount
