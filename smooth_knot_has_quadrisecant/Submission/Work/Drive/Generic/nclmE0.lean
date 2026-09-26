import Mathlib
import Submission.Work.Drive.Generic.nclmDefs

/-!
# The transverse frame at the collapsed end

The whole chart analysis of `Work.Drive.Generic.needleChartLoop_margin` is anchored at the
*transverse acceleration* of the collapsed end `ρ = taR D 0` of the band arc.  This module fixes the
orthonormal frame `(e₀, b₀, T₀)` and records its properties:

* `nclmT r D` — the unit tangent at `ρ`;
* `nclmE0 r D` — the *normalised transverse part* of the acceleration `r''(ρ)`: the direction the
  needle's chart turns out to be aligned with (the deviation of a short arc points *away* from the
  centre of curvature, so the chart direction is close to `-e₀`);
* `nclmB0 r D` — the cross product `T₀ ∧ e₀`, a unit vector orthogonal to both.

The two properties that genuinely need the construction (and are *not* implied by the bare data
`‖e₀‖ = 1`, `⟪e₀, r'⟫ = 0`, `⟪e₀, r''⟫ > 0`) are

* `nclm_inner_r''_E0` — `⟪e₀, r''(ρ)⟫ = ‖the transverse part‖ > 0`;
* `nclm_inner_r''_B0` — `⟪r''(ρ), b₀⟫ = 0`: the acceleration at the collapsed end lies in the plane
  of `e₀` and `T₀`, which is what makes the `b₀`-component of the deviation *third order*.
-/

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData}

/-- The unit tangent at the collapsed end. -/
noncomputable def nclmT (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Space :=
  (‖velocity r (nclmRho D)‖)⁻¹ • velocity r (nclmRho D)

/-- The transverse part of the acceleration at the collapsed end, measured against `nclmT`. -/
noncomputable def nclmW (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Space :=
  deriv (deriv r) (nclmRho D) - (inner ℝ (deriv (deriv r) (nclmRho D)) (nclmT r D)) • nclmT r D

/-- The normalised transverse acceleration direction at the collapsed end. -/
noncomputable def nclmE0 (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Space :=
  (‖nclmW r D‖)⁻¹ • nclmW r D

/-- The binormal direction `T₀ ∧ e₀` at the collapsed end. -/
noncomputable def nclmB0 (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Space :=
  Work.Drive.crossv (nclmT r D) (nclmE0 r D)

lemma nclmT_norm {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) : ‖nclmT r D‖ = 1 := by
  rw [nclmT]
  exact norm_smul_inv_norm (hr.regular (nclmRho D))

lemma nclmT_inner_self {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) : inner ℝ (nclmT r D) (nclmT r D) = 1 := by
  rw [real_inner_self_eq_norm_sq, nclmT_norm hr D]
  norm_num

/-- The transverse part of the acceleration at the collapsed end is non-zero (this is where the
absence of inflections enters). -/
lemma nclmW_ne_zero {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) : nclmW r D ≠ 0 := by
  intro h0
  obtain ⟨hT0, hdep⟩ := linearIndependent_fin2.mp (hinfl (nclmRho D))
  have hWz : deriv (deriv r) (nclmRho D)
      = (inner ℝ (deriv (deriv r) (nclmRho D)) (nclmT r D)) • nclmT r D :=
    sub_eq_zero.mp h0
  have hvne : velocity r (nclmRho D) ≠ 0 := hr.regular (nclmRho D)
  have hTn : nclmT r D
      = (‖velocity r (nclmRho D)‖)⁻¹ • velocity r (nclmRho D) := rfl
  obtain ⟨c, hc⟩ : ∃ c : ℝ, deriv (deriv r) (nclmRho D) = c • deriv r (nclmRho D) := by
    refine ⟨inner ℝ (deriv (deriv r) (nclmRho D)) (nclmT r D)
      * (‖velocity r (nclmRho D)‖)⁻¹, ?_⟩
    calc deriv (deriv r) (nclmRho D)
        = (inner ℝ (deriv (deriv r) (nclmRho D)) (nclmT r D)) • nclmT r D := hWz
      _ = (inner ℝ (deriv (deriv r) (nclmRho D)) (nclmT r D)) •
            ((‖velocity r (nclmRho D)‖)⁻¹ • velocity r (nclmRho D)) := by rw [hTn]
      _ = (inner ℝ (deriv (deriv r) (nclmRho D)) (nclmT r D)
            * (‖velocity r (nclmRho D)‖)⁻¹) • velocity r (nclmRho D) := by rw [smul_smul]
  by_cases hc0 : c = 0
  · rw [hc0, zero_smul] at hc
    exact hT0 hc
  · have : deriv r (nclmRho D) = c⁻¹ • deriv (deriv r) (nclmRho D) := by
      rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    exact hdep c⁻¹ this.symm

lemma nclmE0_norm {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) : ‖nclmE0 r D‖ = 1 := by
  rw [nclmE0]
  exact norm_smul_inv_norm (nclmW_ne_zero hr hinfl D)

lemma nclm_inner_E0_T {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) : inner ℝ (nclmE0 r D) (nclmT r D) = 0 := by
  have hWT : inner ℝ (nclmW r D) (nclmT r D) = 0 := by
    rw [nclmW, inner_sub_left, real_inner_smul_left, nclmT_inner_self hr D]
    ring
  rw [nclmE0, real_inner_smul_left, hWT, mul_zero]

lemma nclmW_eq_smul_E0 {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) : nclmW r D = ‖nclmW r D‖ • nclmE0 r D := by
  rw [nclmE0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (nclmW_ne_zero hr hinfl D)),
    one_smul]

lemma nclm_inner_r''_E0 {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) :
    inner ℝ (deriv (deriv r) (nclmRho D)) (nclmE0 r D) = ‖nclmW r D‖ := by
  have hsplit : deriv (deriv r) (nclmRho D)
      = nclmW r D + (inner ℝ (deriv (deriv r) (nclmRho D)) (nclmT r D)) • nclmT r D := by
    rw [nclmW]; abel
  have h2 : inner ℝ (nclmT r D) (nclmE0 r D) = 0 := by
    rw [real_inner_comm]; exact nclm_inner_E0_T hr hinfl D
  rw [hsplit, inner_add_left, real_inner_smul_left, h2, mul_zero, add_zero,
    nclmW_eq_smul_E0 hr hinfl D, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [norm_smul, Real.norm_of_nonneg (norm_nonneg (nclmW r D)), nclmE0_norm hr hinfl D]
  simp

lemma nclm_inner_r''_B0 {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) :
    inner ℝ (deriv (deriv r) (nclmRho D)) (nclmB0 r D) = 0 := by
  have hsplit : deriv (deriv r) (nclmRho D)
      = nclmW r D + (inner ℝ (deriv (deriv r) (nclmRho D)) (nclmT r D)) • nclmT r D := by
    rw [nclmW]; abel
  rw [hsplit, inner_add_left, real_inner_smul_left]
  have h1 : inner ℝ (nclmE0 r D) (nclmB0 r D) = 0 := by
    rw [nclmB0, real_inner_comm, Work.Drive.inner_crossv_right]
  have h2 : inner ℝ (nclmT r D) (nclmB0 r D) = 0 := by
    rw [nclmB0, Work.Drive.crossv_anticomm, inner_neg_right, real_inner_comm,
      Work.Drive.inner_crossv_right, neg_zero]
  rw [nclmW_eq_smul_E0 hr hinfl D, real_inner_smul_left, h1, mul_zero, h2, mul_zero, add_zero]

lemma nclm_inner_T_B0 {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) : inner ℝ (nclmB0 r D) (nclmT r D) = 0 := by
  rw [nclmB0, Work.Drive.crossv_anticomm, inner_neg_left, Work.Drive.inner_crossv_right, neg_zero]

lemma nclm_inner_E0_B0 {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) : inner ℝ (nclmB0 r D) (nclmE0 r D) = 0 := by
  rw [nclmB0, Work.Drive.inner_crossv_right]

lemma nclmB0_norm {r : ℝ → Space} (hr : IsSmoothKnot r) (hinfl : ∀ t : ℝ,
    LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {d : BandArcData}
    (D : Work.Drive.SweepData d) : ‖nclmB0 r D‖ = 1 := by
  have hsq : ‖nclmB0 r D‖ ^ 2 = 1 := by
    rw [nclmB0, Work.Drive.norm_sq_crossv, nclmT_norm hr D, nclmE0_norm hr hinfl D,
      real_inner_comm, nclm_inner_E0_T hr hinfl D]
    norm_num
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · exact absurd h (by linarith [norm_nonneg (nclmB0 r D)])

end Work.Drive.Generic
