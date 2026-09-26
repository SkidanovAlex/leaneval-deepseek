/-
# Compactness of the three non-contour edges

`edgeC` is a finite union of closed bounded line segments in `ℂ`, hence compact; `edgeH` is its
image in `ℍ` under `ofComplex`, which is continuous on `{Im z > 0} ⊃ edgeC`.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangEdgeDefs
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip

open UpperHalfPlane

namespace Work.Asymptotics.HalfFunnel

noncomputable section

/-- The three non-contour edges, as a subset of `ℂ`, form a closed set. -/
lemma isClosed_edgeC : IsClosed edgeC := by
  have h1 : IsClosed {z : ℂ | z.re = 1 / 4 ∧ (1 : ℝ) / 2 ≤ z.im ∧ z.im ≤ 3 / 2} :=
    (isClosed_eq Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  have h2 : IsClosed {z : ℂ | z.im = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const))
  have h3 : IsClosed {z : ℂ | z.im = 3 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const))
  have h : edgeC = {z : ℂ | z.re = 1 / 4 ∧ (1 : ℝ) / 2 ≤ z.im ∧ z.im ≤ 3 / 2} ∪
      {z : ℂ | z.im = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4} ∪
      {z : ℂ | z.im = 3 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4} := by
    ext z
    simp only [edgeC, Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [h]
  exact (h1.union h2).union h3

/-- The three non-contour edges, as a subset of `ℂ`, are bounded. -/
lemma isBounded_edgeC : Bornology.IsBounded edgeC := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
  refine ⟨2, fun z hz => ?_⟩
  obtain ⟨hre1, hre2, him1, him2⟩ := edgeC_rect hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hre1, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z.im)] at h
  linarith

/-- The three non-contour edges, as a subset of `ℂ`, are compact. -/
lemma isCompact_edgeC : IsCompact edgeC :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_edgeC, isBounded_edgeC⟩

/-- **The three non-contour edges of the tangency rectangle are compact**: they are the image of
the compact set `edgeC ⊆ {Im > 0}` under `ofComplex`. -/
theorem isCompact_edgeH : IsCompact edgeH := by
  have hcont : ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z) edgeC :=
    Work.Asymptotics.continuousOn_ofComplex_im_pos.mono (fun z hz => edgeC_im_pos hz)
  exact isCompact_edgeC.image_of_continuousOn hcont

end

end Work.Asymptotics.HalfFunnel
