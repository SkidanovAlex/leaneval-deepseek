import Mathlib
import Submission.Work.FIArea6b.Basic
import Submission.Work.FIArea6b.regionBetween_interp_convexHull

namespace Work.FIArea6b

open MeasureTheory Set

/-!
# The trapezoidal region of two consecutive columns lies in the convex hull

For a finite set `A` of lattice points and two distinct columns `t < t'` of `A`, the region
`trapRegion A t t'` is the planar region strictly between the two lines that interpolate,
over the interval `[t, t']`, the extrema `loOf`, `hiOf` of the columns `t` and `t'`.  Since the
four corner points `(t, loOf A t)`, `(t, hiOf A t)`, `(t', loOf A t')`, `(t', hiOf A t')` are
actual points of `A`, they lie in `Kset A`, and the region is contained in their convex hull by
the geometric lemma `regionBetween_interp_convexHull`.
-/

/-! ## Membership in a column -/

lemma mem_ys_of_mem {A : Finset (ℤ × ℤ)} {t y : ℤ} (hy : y ∈ ys A t) :
    (⟨t, y⟩ : ℤ × ℤ) ∈ A := by
  rw [ys, Finset.mem_image] at hy
  obtain ⟨q, hq, hqy⟩ := hy
  rw [Finset.mem_filter] at hq
  have hqe : q = (⟨t, y⟩ : ℤ × ℤ) := Prod.ext hq.2 hqy
  rw [hqe] at hq
  exact hq.1

lemma ys_nonempty_of_mem_cols {A : Finset (ℤ × ℤ)} {t : ℤ} (ht : t ∈ cols A) :
    (ys A t).Nonempty := by
  rw [cols, Finset.mem_image] at ht
  obtain ⟨q, hq, hq1⟩ := ht
  refine ⟨q.2, ?_⟩
  rw [ys, Finset.mem_image]
  exact ⟨q, by rw [Finset.mem_filter]; exact ⟨hq, hq1⟩, rfl⟩

lemma loOf_mem_ys {A : Finset (ℤ × ℤ)} {t : ℤ} (hne : (ys A t).Nonempty) :
    loOf A t ∈ ys A t := by
  rw [loOf, dif_pos hne]
  exact Finset.min'_mem _ hne

lemma hiOf_mem_ys {A : Finset (ℤ × ℤ)} {t : ℤ} (hne : (ys A t).Nonempty) :
    hiOf A t ∈ ys A t := by
  rw [hiOf, dif_pos hne]
  exact Finset.max'_mem _ hne

lemma loOf_point_mem (A : Finset (ℤ × ℤ)) {t : ℤ} (ht : t ∈ cols A) :
    (⟨t, loOf A t⟩ : ℤ × ℤ) ∈ A :=
  mem_ys_of_mem (loOf_mem_ys (ys_nonempty_of_mem_cols ht))

lemma hiOf_point_mem (A : Finset (ℤ × ℤ)) {t : ℤ} (ht : t ∈ cols A) :
    (⟨t, hiOf A t⟩ : ℤ × ℤ) ∈ A :=
  mem_ys_of_mem (hiOf_mem_ys (ys_nonempty_of_mem_cols ht))

lemma loOf_le_hiOf {A : Finset (ℤ × ℤ)} {t : ℤ} (hne : (ys A t).Nonempty) :
    loOf A t ≤ hiOf A t := by
  rw [loOf, hiOf, dif_pos hne, dif_pos hne]
  exact Finset.min'_le _ _ (Finset.max'_mem _ hne)

/-! ## The image of a point of `A` is in the convex hull -/

lemma phi_mem_image {A : Finset (ℤ × ℤ)} {q : ℤ × ℤ} (hq : q ∈ A) :
    phi q ∈ (A.image phi : Set (ℝ × ℝ)) := by
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨q, hq, rfl⟩

/-! ## Main lemma -/

theorem trapRegion_subset (A : Finset (ℤ × ℤ)) (t t' : ℤ)
    (ht : t ∈ cols A) (ht' : t' ∈ cols A) (htt' : t < t') :
    trapRegion A t t' ⊆ Kset A := by
  intro p hp
  have htt'R : (t : ℝ) < (t' : ℝ) := by exact_mod_cast htt'
  -- rewrite membership in `trapRegion` as membership in `regionBetween`
  have hpreg : p ∈ regionBetween
      (fun x : ℝ => ((↑t' - x) * ↑(loOf A t) + (x - ↑t) * ↑(loOf A t')) / (↑t' - ↑t))
      (fun x : ℝ => ((↑t' - x) * ↑(hiOf A t) + (x - ↑t) * ↑(hiOf A t')) / (↑t' - ↑t))
      (Set.Icc (↑t) (↑t')) := by
    simpa only [trapRegion] using hp
  -- the geometric lemma puts `p` in the convex hull of the four corner points
  have hp' : p ∈ convexHull ℝ
      ({(↑t, ↑(loOf A t)), (↑t, ↑(hiOf A t)), (↑t', ↑(loOf A t')), (↑t', ↑(hiOf A t'))} :
        Set (ℝ × ℝ)) :=
    (regionBetween_interp_convexHull (↑t) (↑t') (↑(loOf A t)) (↑(loOf A t'))
      (↑(hiOf A t)) (↑(hiOf A t')) htt'R) hpreg
  -- each corner point is the image of an actual point of `A`
  have hcorner : ({(↑t, ↑(loOf A t)), (↑t, ↑(hiOf A t)), (↑t', ↑(loOf A t')),
      (↑t', ↑(hiOf A t'))} : Set (ℝ × ℝ)) ⊆ (A.image phi : Set (ℝ × ℝ)) := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with h | h | h | h
    · rw [h]; exact phi_mem_image (loOf_point_mem A ht)
    · rw [h]; exact phi_mem_image (hiOf_point_mem A ht)
    · rw [h]; exact phi_mem_image (loOf_point_mem A ht')
    · rw [h]; exact phi_mem_image (hiOf_point_mem A ht')
  exact convexHull_mono hcorner hp'

end Work.FIArea6b
