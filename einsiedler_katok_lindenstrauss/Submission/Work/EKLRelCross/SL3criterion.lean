import Mathlib
import Submission.Work.EKLRelCross.SL3famDefs

open MeasureTheory
open scoped ENNReal

namespace Work.EKLRelCross

theorem SL3criterion {m1 m2 : MeasureTheory.Measure Work.EKLContract.SL3}
    (h1 : MeasureTheory.IsFiniteMeasureOnCompacts m1)
    (h2 : MeasureTheory.IsFiniteMeasureOnCompacts m2)
    (h1nz : m1 ≠ 0) (h2nz : m2 ≠ 0) :
    (∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ m2 = c • m1) ↔ Work.EKLRelCross.SL3Criterion m1 m2 := by
  constructor
  · rintro ⟨c, hc0, hct, rfl⟩
    have hm1univ : m1 Set.univ ≠ 0 := by
      intro hzero
      apply h1nz
      refine Measure.ext fun s _ => ?_
      show m1 s = 0
      have h2' : m1 s ≤ m1 Set.univ := measure_mono (Set.subset_univ s)
      rw [hzero] at h2'
      exact nonpos_iff_eq_zero.1 h2'
    obtain ⟨n, hn⟩ :=
      exists_measure_pos_of_not_measure_iUnion_null (s := fun n => SL3fam (n, ∅))
        (by rwa [iUnion_SL3fam_empty])
    refine ⟨(n, ∅), hn, ?_, ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul]
      exact pos_iff_ne_zero.mpr (mul_ne_zero hc0 (ne_of_gt hn))
    · intro p
      rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
      ring
  · rintro ⟨p0, hp1, hp2, hprop⟩
    set c : ENNReal := m2 (SL3fam p0) * (m1 (SL3fam p0))⁻¹ with hcdef
    have hm1p0_ne0 : m1 (SL3fam p0) ≠ 0 := ne_of_gt hp1
    have hm2p0_ne0 : m2 (SL3fam p0) ≠ 0 := ne_of_gt hp2
    have hm1p0_ne_top : m1 (SL3fam p0) ≠ ⊤ := by
      have hlt := h1.lt_top_of_isCompact (isCompact_compactCovering Work.EKLContract.SL3 p0.1)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono (SL3fam_subset_compactCovering p0)) hlt)
    have hm2p0_ne_top : m2 (SL3fam p0) ≠ ⊤ := by
      have hlt := h2.lt_top_of_isCompact (isCompact_compactCovering Work.EKLContract.SL3 p0.1)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono (SL3fam_subset_compactCovering p0)) hlt)
    refine ⟨c, ?_, ?_, ?_⟩
    · rw [hcdef]
      exact mul_ne_zero hm2p0_ne0 (ENNReal.inv_ne_zero.mpr hm1p0_ne_top)
    · rw [hcdef]
      exact ENNReal.mul_ne_top hm2p0_ne_top (ENNReal.inv_ne_top.mpr hm1p0_ne0)
    · refine Measure.ext_of_generateFrom_of_iUnion (Set.range SL3fam) (fun n => SL3fam (n, ∅))
        generateFrom_SL3fam.symm isPiSystem_SL3fam iUnion_SL3fam_empty
        (fun i => ⟨(i, ∅), rfl⟩) ?_ ?_
      · intro i
        have hlt := h2.lt_top_of_isCompact (isCompact_compactCovering Work.EKLContract.SL3 i)
        exact ne_of_lt
          (lt_of_le_of_lt (measure_mono (SL3fam_subset_compactCovering (i, ∅))) hlt)
      · rintro s ⟨p, rfl⟩
        rw [Measure.smul_apply, smul_eq_mul, hcdef]
        have h1' := congrArg (fun x : ENNReal => x * (m1 (SL3fam p0))⁻¹) (hprop p)
        rw [mul_assoc, mul_assoc, ENNReal.mul_inv_cancel hm1p0_ne0 hm1p0_ne_top, mul_one] at h1'
        rw [h1']
        ring

end Work.EKLRelCross
