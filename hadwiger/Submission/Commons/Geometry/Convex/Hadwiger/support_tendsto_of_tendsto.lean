import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.hausdorffDist_eq_sSup_support

namespace Commons.Geometry.Convex.Hadwiger

open Filter
open scoped Topology

/-- One-sided bound: enlarging the body can raise the support in direction `u` by
at most the Hausdorff distance times `‖u‖`. -/
private lemma support_le_support_add_mul_dist
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K L : ConvexBody V) (u : V) :
    HausdorffSupport.support K u ≤ HausdorffSupport.support L u + ‖u‖ * dist K L := by
  apply HausdorffSupport.support_le_of_forall_le K u (HausdorffSupport.support L u + ‖u‖ * dist K L)
  intro x hx
  obtain ⟨y, hyL, hyd⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
  have hinf : Metric.infDist x (L : Set V) ≤ dist K L := by
    have h := Metric.infDist_le_hausdorffDist_of_mem (s := (K : Set V)) (t := (L : Set V)) hx
      (ConvexBody.hausdorffEDist_ne_top (K := K) (L := L))
    simpa [ConvexBody.hausdorffDist_coe] using h
  have hdy : dist x y ≤ dist K L := by
    rw [← hyd]
    exact hinf
  calc
    inner ℝ u x ≤ inner ℝ u y + ‖u‖ * dist x y :=
      HausdorffSupport.inner_le_inner_add_norm_dist u x y
    _ ≤ inner ℝ u y + ‖u‖ * dist K L := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hdy (norm_nonneg u)) (inner ℝ u y)
    _ ≤ HausdorffSupport.support L u + ‖u‖ * dist K L := by
      exact add_le_add_left (HausdorffSupport.inner_le_support L hyL u) (‖u‖ * dist K L)

/-- The support difference in an arbitrary direction is bounded by `‖u‖` times the
Hausdorff distance of the two bodies. -/
private lemma support_dist_le_mul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K L : ConvexBody V) (u : V) :
    |HausdorffSupport.support K u - HausdorffSupport.support L u| ≤ ‖u‖ * dist K L := by
  rw [abs_sub_le_iff]
  constructor
  · have h := support_le_support_add_mul_dist K L u
    linarith
  · have h := support_le_support_add_mul_dist L K u
    rw [dist_comm] at h
    linarith

/-- If a sequence of convex bodies converges in the Hausdorff metric, then its
support functions converge pointwise to the support function of the limit. -/
theorem support_tendsto_of_tendsto
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] {Z : ℕ → ConvexBody V} {Y : ConvexBody V}
    (hZ : Tendsto Z atTop (𝓝 Y)) (u : V) :
    Tendsto (fun n : ℕ => sSup ((fun x : V => inner ℝ u x) '' (Z n : Set V))) atTop
      (𝓝 (sSup ((fun x : V => inner ℝ u x) '' (Y : Set V)))) := by
  change Tendsto (fun n : ℕ => HausdorffSupport.support (Z n) u) atTop
    (𝓝 (HausdorffSupport.support Y u))
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ => ‖u‖ * dist (Z n) Y) ?hf ?hft ?g0
  · intro n
    exact dist_nonneg
  · intro n
    rw [Real.dist_eq]
    exact support_dist_le_mul (Z n) Y u
  · simpa using (tendsto_iff_dist_tendsto_zero.mp hZ).const_mul ‖u‖

end Commons.Geometry.Convex.Hadwiger
