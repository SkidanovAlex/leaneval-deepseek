import Mathlib

namespace Work.Whitney

open scoped Topology ContDiff NNReal
open Metric

theorem taylor_second_order_ball {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)))
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (p : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ r →
      ‖G (p + h) - G p - fderiv ℝ G p h‖ ≤ C * ‖h‖ ^ 2 := by
  have hGdiff : Differentiable ℝ G := (contDiff_infty_iff_fderiv.1 hG).1
  have hG' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ G) :=
    (contDiff_infty_iff_fderiv.1 hG).2
  -- Lipschitz constant for `fderiv ℝ G` on the closed ball
  have h1 : ContDiffOn ℝ (1 : WithTop ℕ∞) (fderiv ℝ G) (closedBall p r) :=
    (hG'.of_le (m := 1) (by norm_num)).contDiffOn
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0, LipschitzOnWith L (fderiv ℝ G) (closedBall p r) :=
    ContDiffOn.exists_lipschitzOnWith h1 (by norm_num)
      (convex_closedBall p r) (isCompact_closedBall p r)
  refine ⟨(L : ℝ) + 1, by positivity, ?_⟩
  intro h hh
  have hconv : Convex ℝ (closedBall p ‖h‖) := convex_closedBall p ‖h‖
  have hmem_p : p ∈ closedBall p ‖h‖ := by
    simp [mem_closedBall]
  have hmem_ph : p + h ∈ closedBall p ‖h‖ := by
    rw [mem_closedBall, dist_eq_norm]
    simp
  have hder : ∀ x ∈ closedBall p ‖h‖,
      HasFDerivWithinAt G (fderiv ℝ G x) (closedBall p ‖h‖) x :=
    fun x _ => ((hGdiff x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ x ∈ closedBall p ‖h‖, ‖fderiv ℝ G x - fderiv ℝ G p‖ ≤ (L : ℝ) * ‖h‖ := by
    intro x hx
    have hxr : x ∈ closedBall p r := by
      rw [mem_closedBall] at hx ⊢
      exact le_trans hx hh
    have hp_r : p ∈ closedBall p r := by
      rw [mem_closedBall]
      simpa using hr.le
    have hd := hL.dist_le_mul x hxr p hp_r
    rw [dist_eq_norm, dist_eq_norm] at hd
    have hxp : ‖x - p‖ ≤ ‖h‖ := by
      rw [← dist_eq_norm]; exact hx
    calc ‖fderiv ℝ G x - fderiv ℝ G p‖ ≤ (L : ℝ) * ‖x - p‖ := hd
      _ ≤ (L : ℝ) * ‖h‖ := mul_le_mul_of_nonneg_left hxp (by positivity)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := G) (f' := fun x => fderiv ℝ G x) (φ := fderiv ℝ G p)
      hder hbound hconv hmem_p hmem_ph
  simp only [add_sub_cancel_left] at key
  calc ‖G (p + h) - G p - fderiv ℝ G p h‖ ≤ (L : ℝ) * ‖h‖ * ‖h‖ := key
    _ = (L : ℝ) * ‖h‖ ^ 2 := by ring
    _ ≤ ((L : ℝ) + 1) * ‖h‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖h‖)
        linarith

end Work.Whitney
