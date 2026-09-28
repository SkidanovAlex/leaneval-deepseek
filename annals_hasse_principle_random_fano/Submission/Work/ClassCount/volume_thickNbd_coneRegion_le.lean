import Mathlib
import Submission.Work.HP.HP2.ClassCountPrelude
import Submission.Work.HP.HP2.grid_count_bounds
import Submission.Work.HP.HP2.isClosed_coneRegion
import Submission.Work.HP.HP2.isBounded_coneRegion
import Submission.Work.HP.PFCountDefs

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace Work.ClassCount

private theorem thickNbd_subset_union_frontier_tmp (m : ℕ) (r : ℝ) (S : Set (Fin m → ℝ)) :
    Work.HP.HP2.thickNbd m r S ⊆ S ∪ Work.HP.HP2.thickNbd m r (frontier S) := by
  intro x hx
  obtain ⟨p, hpS, hxp⟩ := hx
  by_cases hxS : x ∈ S
  · exact Or.inl hxS
  · right
    obtain ⟨t, ht, hc⟩ := Work.HP.HP2.segment_frontier (E := Fin m → ℝ) hpS hxS
    refine ⟨p + t • (x - p), hc, ?_⟩
    have hxeq : x - (p + t • (x - p)) = (1 - t) • (x - p) := by module
    rw [hxeq, Work.HP.rNorm_smul', abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
    have : (1 - t) * Work.HP.rNorm (x - p) ≤ Work.HP.rNorm (x - p) := by
      nlinarith [Work.HP.rNorm_nonneg (x - p), ht.1, ht.2]
    linarith

theorem volume_thickNbd_coneRegion_le (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α T Wr : ℝ)
    (hWr : 0 ≤ Wr) (hTube : Work.HP.TubeOk d n a α T Wr) :
    (MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) (8 * ((n : ℝ) + 1) * Wr)
        (Work.HP.coneRegion d n a α T))).toReal
      ≤ (3 / 2) * (MeasureTheory.volume (Work.HP.coneRegion d n a α T)).toReal := by
  set S : Set (Fin (n + 1) → ℝ) := Work.HP.coneRegion d n a α T with hS
  set r : ℝ := 8 * ((n : ℝ) + 1) * Wr with hr
  have hrnn : 0 ≤ r := by rw [hr]; positivity
  have hTube' : (MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r (frontier S))).toReal
      ≤ (1 / 2) * (MeasureTheory.volume S).toReal := by
    rw [hS, hr]
    simpa only [Work.HP.TubeOk, Work.HP.HP2.thickNbd] using hTube
  have hSbd : Bornology.IsBounded S := by
    rw [hS]; exact Work.HP.HP2.isBounded_coneRegion d n a α T
  have hfr : frontier S ⊆ S := by
    rw [hS]
    exact Set.Subset.trans frontier_subset_closure
      (le_of_eq (Work.HP.HP2.isClosed_coneRegion d n a α T).closure_eq)
  have hsub : Work.HP.HP2.thickNbd (n + 1) r S
      ⊆ S ∪ Work.HP.HP2.thickNbd (n + 1) r (frontier S) :=
    thickNbd_subset_union_frontier_tmp (n + 1) r S
  have hSfin : MeasureTheory.volume S < ⊤ :=
    Work.HP.HP2.volume_lt_top_of_isBounded (n + 1) hSbd
  have hTfin : MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r S) < ⊤ :=
    Work.HP.HP2.volume_thickNbd_lt_top (n + 1) hSbd hrnn
  have hfrfin : MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r (frontier S)) < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun x hx => by
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨y, hfr hy, hxy⟩)) hTfin
  have hmeas : MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r S)
      ≤ MeasureTheory.volume S
        + MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r (frontier S)) :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hsumfin : MeasureTheory.volume S
      + MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r (frontier S)) ≠ ⊤ :=
    (ENNReal.add_lt_top.mpr ⟨hSfin, hfrfin⟩).ne
  calc (MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r S)).toReal
      ≤ (MeasureTheory.volume S
          + MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r (frontier S))).toReal :=
        ENNReal.toReal_mono hsumfin hmeas
    _ = (MeasureTheory.volume S).toReal
          + (MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1) r (frontier S))).toReal :=
        ENNReal.toReal_add hSfin.ne hfrfin.ne
    _ ≤ (MeasureTheory.volume S).toReal + (1 / 2) * (MeasureTheory.volume S).toReal :=
        add_le_add le_rfl hTube'
    _ = (3 / 2) * (MeasureTheory.volume S).toReal := by ring

end Work.ClassCount
