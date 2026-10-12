import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Rb5Lin.ps3Base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

open MeasureTheory

/-- `box3 = (0,1]³` is the cartesian product of the half-open unit intervals. -/
lemma box3_eq_univ_pi :
    box3 = Set.univ.pi (fun _ : Fin 3 => Set.Ioc (0 : ℝ) (0 + 1)) := by
  ext x
  simp only [mem_box3, Set.mem_pi, Set.mem_univ, forall_const]

/-- `box3` is measurable (it is a finite product of half-open intervals). -/
lemma measurableSet_box3 : MeasurableSet box3 := by
  rw [box3_eq_univ_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem ps3_fundamentalDomain :
    MeasureTheory.IsAddFundamentalDomain (Fin 3 → ℤ) Work.BoseFixR.Rb5Lin.box3
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) := by
  have h1 : (0 : ℝ) < 1 := by norm_num
  refine MeasureTheory.IsAddFundamentalDomain.mk' measurableSet_box3.nullMeasurableSet ?_
  intro x
  -- Coordinatewise: the unique integer `k` with `x i + k ∈ (0,1]`.
  have key : ∃! m : Fin 3 → ℤ, ∀ i, x i + (m i : ℝ) ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    refine ⟨fun i => (existsUnique_add_zsmul_mem_Ioc h1 (x i) 0).choose, ?_, ?_⟩
    · intro i
      simpa using (existsUnique_add_zsmul_mem_Ioc h1 (x i) 0).choose_spec.1
    · intro m hm
      funext i
      exact (existsUnique_add_zsmul_mem_Ioc h1 (x i) 0).unique (by simpa using hm i)
        (by simpa using (existsUnique_add_zsmul_mem_Ioc h1 (x i) 0).choose_spec.1)
  obtain ⟨m, hm, huniq⟩ := key
  refine ⟨m, ?_, ?_⟩
  · exact mem_box3.mpr hm
  · intro m' hm'
    exact huniq m' (mem_box3.mp hm')

end Work.BoseFixR.Rb5Lin
