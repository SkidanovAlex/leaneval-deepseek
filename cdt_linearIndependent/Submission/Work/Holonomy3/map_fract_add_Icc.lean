import Mathlib

open MeasureTheory Set

namespace Work.Holonomy3

theorem map_fract_add_Icc {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    MeasureTheory.Measure.map (fun x : ℝ => Int.fract (x + v))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      = MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hA : 0 ≤ 1 - v := by linarith
  have hA1 : 1 - v ≤ 1 := by linarith
  have hRmeas : Measurable fun x : ℝ => Int.fract (x + v) :=
    measurable_fract.comp (by fun_prop)
  rw [← MeasureTheory.restrict_Ico_eq_restrict_Icc (μ := (volume : Measure ℝ)) (a := 0) (b := 1)]
  have hν : volume.restrict (Ico (0:ℝ) 1)
      = volume.restrict (Ico 0 (1-v)) + volume.restrict (Ico (1-v) 1) := by
    rw [← Set.Ico_union_Ico_eq_Ico hA hA1]
    exact Measure.restrict_union (by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact absurd hx2.1 (not_le.mpr hx1.2)) measurableSet_Ico
  have hR1 : ∀ᵐ x ∂(volume.restrict (Ico (0:ℝ) (1-v))), Int.fract (x + v) = x + v :=
    ae_restrict_of_forall_mem measurableSet_Ico (fun x hx => by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith [hx.1, hv], by linarith [hx.2], 0, by simp⟩)
  have hR2 : ∀ᵐ x ∂(volume.restrict (Ico (1-v) 1)), Int.fract (x + v) = x + v - 1 :=
    ae_restrict_of_forall_mem measurableSet_Ico (fun x hx => by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [hx.1], by linarith [hx.2, hv1], 1, by push_cast; ring⟩)
  have hmap1 : Measure.map (fun x : ℝ => Int.fract (x + v)) (volume.restrict (Ico (0:ℝ) (1-v)))
      = Measure.map (fun x : ℝ => x + v) (volume.restrict (Ico 0 (1-v))) :=
    Measure.map_congr hR1
  have hmap2 : Measure.map (fun x : ℝ => Int.fract (x + v)) (volume.restrict (Ico (1-v) 1))
      = Measure.map (fun x : ℝ => x + v - 1) (volume.restrict (Ico (1-v) 1)) :=
    Measure.map_congr hR2
  have hpre1 : (fun x : ℝ => x + v) ⁻¹' (Ico v 1) = Ico (0:ℝ) (1-v) := by
    ext x; simp only [Set.mem_preimage, Set.mem_Ico]; constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hV1 : Measure.map (fun x : ℝ => x + v) (volume.restrict (Ico (0:ℝ) (1-v)))
      = volume.restrict (Ico v 1) := by
    have h := Measure.restrict_map (μ := (volume : Measure ℝ)) (f := fun x : ℝ => x + v)
      (by fun_prop) (s := Ico v 1) measurableSet_Ico
    rw [hpre1] at h
    rw [map_add_right_eq_self (volume : Measure ℝ) v] at h
    exact h.symm
  have hpre2 : (fun x : ℝ => x + v - 1) ⁻¹' (Ico (0:ℝ) v) = Ico (1-v) 1 := by
    ext x; simp only [Set.mem_preimage, Set.mem_Ico]; constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have ht : Measure.map (fun x : ℝ => x + v - 1) (volume : Measure ℝ) = volume := by
    have h1 : (fun x : ℝ => x + v - 1) = fun x : ℝ => x + (v - 1) := by funext x; ring
    rw [h1]; exact map_add_right_eq_self volume (v - 1)
  have hV2 : Measure.map (fun x : ℝ => x + v - 1) (volume.restrict (Ico (1-v) 1))
      = volume.restrict (Ico (0:ℝ) v) := by
    have h := Measure.restrict_map (μ := (volume : Measure ℝ)) (f := fun x : ℝ => x + v - 1)
      (by fun_prop) (s := Ico 0 v) measurableSet_Ico
    rw [hpre2] at h
    rw [ht] at h
    exact h.symm
  calc Measure.map (fun x : ℝ => Int.fract (x + v)) (volume.restrict (Ico (0:ℝ) 1))
      = Measure.map (fun x : ℝ => Int.fract (x + v))
          (volume.restrict (Ico 0 (1-v)) + volume.restrict (Ico (1-v) 1)) := by rw [hν]
    _ = Measure.map (fun x : ℝ => Int.fract (x + v)) (volume.restrict (Ico 0 (1-v)))
        + Measure.map (fun x : ℝ => Int.fract (x + v)) (volume.restrict (Ico (1-v) 1)) :=
          Measure.map_add _ _ hRmeas
    _ = Measure.map (fun x : ℝ => x + v) (volume.restrict (Ico 0 (1-v)))
        + Measure.map (fun x : ℝ => x + v - 1) (volume.restrict (Ico (1-v) 1)) := by
          rw [hmap1, hmap2]
    _ = volume.restrict (Ico v 1) + volume.restrict (Ico (0:ℝ) v) := by rw [hV1, hV2]
    _ = volume.restrict (Ico v 1 ∪ Ico (0:ℝ) v) :=
          (Measure.restrict_union (by
            rw [Set.disjoint_left]; intro x hx1 hx2
            exact absurd hx2.2 (not_lt.mpr hx1.1)) measurableSet_Ico).symm
    _ = volume.restrict (Ico (0:ℝ) 1) := by
          rw [Set.union_comm, Set.Ico_union_Ico_eq_Ico hv hv1]

end Work.Holonomy3
