import Mathlib
import Submission.Work.EKLComp.C8Defs

namespace Work.EKLCompSetup

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract

/-- The decreasing family `ballU h01 r` has intersection over `r > R` equal to `ballU h01 R`:
`ballU h01 r = u_01([-r,r])` and `par` reads off the parameter on `U_01`. -/
lemma biInter_ballU_gt (R : ℝ) :
    (⋂ r, ⋂ (_ : r > R), ballU Work.EKLComp.h01 r) = ballU Work.EKLComp.h01 R := by
  apply Set.Subset.antisymm
  · intro g hg
    simp only [Set.mem_iInter] at hg
    rw [← Work.EKLComp.par_preimage_Icc R]
    have hmem1 : g ∈ ballU Work.EKLComp.h01 (R + 1) := hg (R + 1) (by linarith)
    have hU : g ∈ (Uij Work.EKLComp.h01 : Set SL3) := by
      obtain ⟨t, _, rfl⟩ := hmem1
      exact Subgroup.subset_closure ⟨t, rfl⟩
    refine ⟨hU, ?_⟩
    have hbound : ∀ r > R, |Work.EKLComp.par g| ≤ r := by
      intro r hr
      obtain ⟨t, ht, hte⟩ := hg r hr
      have hpar : Work.EKLComp.par g = t := by rw [← hte, Work.EKLComp.par_uij_h01]
      rw [hpar]
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hpR : |Work.EKLComp.par g| ≤ R :=
      le_of_forall_pos_le_add fun ε hε => hbound (R + ε) (by linarith)
    simp only [Set.mem_preimage, Set.mem_Icc]
    exact abs_le.mp hpR
  · intro g hg
    simp only [Set.mem_iInter]
    intro r hr
    obtain ⟨t, ht, rfl⟩ := hg
    exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩

theorem tendsto_measure_ballU_gt {ν : MeasureTheory.Measure Work.EKLContract.SL3}
    (hν : MeasureTheory.IsFiniteMeasureOnCompacts ν) (R : ℝ) :
    Filter.Tendsto (fun r : ℝ => ν (Work.EKLContract.ballU Work.EKLComp.h01 r))
      (nhdsWithin R (Set.Ioi R)) (nhds (ν (Work.EKLContract.ballU Work.EKLComp.h01 R))) := by
  have h := MeasureTheory.tendsto_measure_biInter_gt (μ := ν)
    (s := fun r : ℝ => ballU Work.EKLComp.h01 r) (a := R)
    (fun r _ => (Work.EKLComp.isCompact_ballU r).isClosed.measurableSet.nullMeasurableSet)
    (fun i j _ hij => Set.image_mono (Set.Icc_subset_Icc (neg_le_neg hij) hij))
    ⟨R + 1, by linarith, (hν.lt_top_of_isCompact (Work.EKLComp.isCompact_ballU (R + 1))).ne⟩
  rwa [biInter_ballU_gt R] at h

end Work.EKLCompSetup
