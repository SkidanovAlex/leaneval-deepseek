import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators
open Set

namespace Commons.Geometry.Convex.Hadwiger

theorem polytope_exposedFace_conv_vertices (m : ℕ)
    (u : Finset (EuclideanSpace ℝ (Fin m)))
    (P : Set (EuclideanSpace ℝ (Fin m)))
    (hP : P = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m)))) {F : Set (EuclideanSpace ℝ (Fin m))}
    (hF : IsExposed ℝ P F) (hFne : F.Nonempty) :
    F = convexHull ℝ (F ∩ (u : Set (EuclideanSpace ℝ (Fin m)))) := by
  classical
  obtain ⟨l, hl⟩ := hF hFne
  have hPconv : Convex ℝ P := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m)))
  have hFconv : Convex ℝ F := hF.convex hPconv
  have huP : (u : Set (EuclideanSpace ℝ (Fin m))) ⊆ P := by
    rw [hP]
    exact subset_convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m)))
  apply Set.Subset.antisymm
  · intro x hxF
    have hxF' : x ∈ {x' ∈ P | ∀ y ∈ P, l y ≤ l x'} := by
      rw [hl] at hxF
      exact hxF
    have hxmax : ∀ y ∈ P, l y ≤ l x := hxF'.2
    have hxCH : x ∈ convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m))) := by
      simpa [hP] using hxF'.1
    rw [Finset.mem_convexHull'] at hxCH
    rcases hxCH with ⟨w, hw0, hw1, hwx⟩
    have hle : ∀ z ∈ u, l z ≤ l x := by
      intro z hz
      exact hxmax z (huP hz)
    have hsecond : (∑ z ∈ u, w z * l z) = l x := by
      calc
        (∑ z ∈ u, w z * l z) = (∑ z ∈ u, w z • l z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          simp
        _ = l (∑ z ∈ u, w z • z) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro z hz
          exact (map_smul l (w z) z).symm
        _ = l x := by rw [hwx]
    have hsum : (∑ z ∈ u, w z * (l x - l z)) = 0 := by
      calc
        (∑ z ∈ u, w z * (l x - l z)) = (∑ z ∈ u, (w z * l x - w z * l z)) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          ring
        _ = (∑ z ∈ u, w z * l x) - (∑ z ∈ u, w z * l z) := by
          rw [Finset.sum_sub_distrib]
        _ = l x - (∑ z ∈ u, w z * l z) := by
          rw [← Finset.sum_mul]
          rw [hw1]
          ring
        _ = l x - l x := by rw [hsecond]
        _ = 0 := by ring
    have hterm_nonneg : ∀ z ∈ u, 0 ≤ w z * (l x - l z) := by
      intro z hz
      exact mul_nonneg (hw0 z hz) (sub_nonneg.mpr (hle z hz))
    have hterm : ∀ z ∈ u, w z * (l x - l z) = 0 := by
      intro z hz
      exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hsum z hz
    have hmax_eq : ∀ z ∈ u, w z ≠ 0 → l z = l x := by
      intro z hz hwz
      have h : l x - l z = 0 := (mul_eq_zero.mp (hterm z hz)).resolve_left hwz
      exact (sub_eq_zero.mp h).symm
    have hw_of_out : ∀ z ∈ u, z ∉ F → w z = 0 := by
      intro z hz hzF
      by_contra hwz
      apply hzF
      rw [hl]
      have hlz : l z = l x := hmax_eq z hz hwz
      have hzP : z ∈ P := huP hz
      exact ⟨hzP, fun y hy => by simpa [hlz] using hxmax y hy⟩
    let v : Finset (EuclideanSpace ℝ (Fin m)) := u.filter (fun z => z ∈ F)
    have hvsub : v ⊆ u := Finset.filter_subset _ u
    have hw0v : ∀ z ∈ v, 0 ≤ w z := by
      intro z hz
      exact hw0 z (hvsub hz)
    have hw_out_v : ∀ z ∈ u, z ∉ v → w z = 0 := by
      intro z hz hzv
      exact hw_of_out z hz (by
        intro hzF
        apply hzv
        simpa [v] using ⟨hz, hzF⟩)
    have hsumv : (∑ z ∈ v, w z) = 1 := by
      calc
        (∑ z ∈ v, w z) = (∑ z ∈ u, w z) := Finset.sum_subset hvsub hw_out_v
        _ = 1 := hw1
    have hsumx : (∑ z ∈ v, w z • z) = x := by
      calc
        (∑ z ∈ v, w z • z) = (∑ z ∈ u, w z • z) := by
          refine Finset.sum_subset hvsub ?_
          intro z hz hzv
          simp [hw_out_v z hz hzv]
        _ = x := hwx
    have hxCHv : x ∈ convexHull ℝ (v : Set (EuclideanSpace ℝ (Fin m))) := by
      exact (Finset.mem_convexHull' (s := v) (x := x)).2 ⟨w, hw0v, hsumv, hsumx⟩
    have hv_eq : (v : Set (EuclideanSpace ℝ (Fin m))) = F ∩ (u : Set (EuclideanSpace ℝ (Fin m))) := by
      ext z
      simp [v]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hv_eq] at hxCHv
    exact hxCHv
  · exact convexHull_min (inter_subset_left : F ∩ (u : Set (EuclideanSpace ℝ (Fin m))) ⊆ F) hFconv

end Commons.Geometry.Convex.Hadwiger