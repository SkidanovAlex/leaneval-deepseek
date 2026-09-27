import Mathlib
import Submission.Work.KT.D2.PAMDefs

/-!
# Positivity of the Hopf-vector coordinates on the punctured disc

The disc-model Hopf vector at `y ∈ D²` is `(1 + x₂(y), x₀(y) + i x₁(y))`, where
`(x₀, x₁, x₂) = qc 2 y ∈ S²` are the coordinates of the image of `y` under the quotient map
`D² → S²` which collapses the boundary to the north pole.

Because `qc 2 y = (sfun ‖y‖ • y, -cos (π ‖y‖))`, we have `x₂(y) = -cos (π ‖y‖)`, so
`hv1 y = 1 - cos (π ‖y‖) ≥ 0` with equality only for `‖y‖ = 0`, i.e. only at the centre of the
disc.  Hence off the centre both `hv1 y` and (since `hvN2 y = 2 * hv1 y`) `hvN2 y` are strictly
positive: the Hopf vector never vanishes on the punctured disc.

This is the ingredient which guarantees that the clutching family `Cm u` is invertible off the
centre, i.e. that the loop `loopC u r …` of `PAMDefs` is defined.
-/

namespace Work.KT.D2

noncomputable section

/-! ## The coordinates of `qc 2 y` -/

/-- The last coordinate of `qc 2 y` is `-cos (π ‖y‖)`. -/
lemma sphCoordR_eq_cos (y : Dc) : sphCoordR y = -Real.cos (Real.pi * ‖(y : E2)‖) := by
  show ((Work.KT.qc 2 y : Work.KT.ModelSphere 2).snd) = _
  rw [show (Work.KT.qc 2 y : Work.KT.ModelSphere 2) = Work.KT.qMapDisk 2 y from rfl]
  simp [Work.KT.qMapDisk]

/-- A point of the disc is the centre iff its norm vanishes. -/
lemma eq_dctr_iff_norm_eq_zero (y : Dc) : y = dctr ↔ ‖(y : E2)‖ = 0 := by
  constructor
  · intro h
    rw [h, dctr_coe, norm_zero]
  · intro h
    exact Subtype.ext (by rw [dctr_coe, norm_eq_zero.mp h])

/-- Points of the disc other than the centre have strictly positive norm. -/
lemma norm_pos_of_ne_dctr (y : Dc) (hy : y ≠ dctr) : 0 < ‖(y : E2)‖ := by
  rw [norm_pos_iff]
  intro h0
  exact hy ((eq_dctr_iff_norm_eq_zero y).mpr (by rw [h0, norm_zero]))

/-- Points of the disc have norm at most one. -/
lemma norm_le_one_of_dc (y : Dc) : ‖(y : E2)‖ ≤ 1 := by
  have h := Metric.mem_closedBall.mp y.2
  simpa [dist_eq_norm] using h

/-! ## A trigonometric inequality -/

/-- `cos (π r) < 1` for `0 < r ≤ 1`. -/
lemma cos_pi_mul_lt_one {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : Real.cos (Real.pi * r) < 1 := by
  refine lt_of_le_of_ne (Real.cos_le_one _) ?_
  intro h
  have hlt : Real.pi * r < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hgt : -(2 * Real.pi) < Real.pi * r := by nlinarith [Real.pi_pos]
  have hz := (Real.cos_eq_one_iff_of_lt_of_lt hgt hlt).mp h
  nlinarith [Real.pi_pos]

/-! ## Positivity of the Hopf-vector coordinates -/

/-- The first coordinate `1 + x₂` of the Hopf vector is positive off the centre. -/
lemma hv1_pos_of_ne_dctr (y : Dc) (hy : y ≠ dctr) : 0 < hv1 y := by
  rw [hv1, sphCoordR_eq_cos]
  have h := cos_pi_mul_lt_one (norm_pos_of_ne_dctr y hy) (norm_le_one_of_dc y)
  linarith

/-- The squared norm of the Hopf vector is positive off the centre. -/
lemma hvN2_pos_of_ne_dctr (y : Dc) (hy : y ≠ dctr) : 0 < hvN2 y := by
  rw [hvN2_eq]
  linarith [hv1_pos_of_ne_dctr y hy]

/-- Off the centre of the disc the Hopf vector `(1 + x₂, x₀ + i x₁)` is nonzero: both its first
coordinate and its squared norm are strictly positive. -/
theorem PAMSphCoordPos (y : Work.KT.D2.Dc) (hy : y ≠ Work.KT.D2.dctr) :
    0 < Work.KT.D2.hv1 y ∧ 0 < Work.KT.D2.hvN2 y :=
  ⟨hv1_pos_of_ne_dctr y hy, hvN2_pos_of_ne_dctr y hy⟩

end

end Work.KT.D2
