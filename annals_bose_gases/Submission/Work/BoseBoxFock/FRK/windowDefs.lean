import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseBoxFock.chi_sq_bounds
import Submission.Work.BoseBoxFock.kinRow_lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.windowDefs` — the frequency cutoff and its smoothing kernel

This module holds the *vocabulary* of the proof of `Work.BoseBoxFock.FRK.windowHigh_le` (the S1
windowed high-momentum split of the FRK design, `LEAD_DESIGN_formrowkin_v2.md` §1):

* `freqProfile` — the fixed smooth radial profile used as a *frequency* cutoff: it equals `1` on
  the unit ball and vanishes outside the ball of radius `5/4`.  The deliberately narrow "collar"
  (`rOut/rIn = 5/4`) is what makes the cut `1_{(d²ℓ)⁻¹ < ‖p‖}` fit strictly inside the complement
  of the high-momentum region `{3κ/2 ≤ ‖p‖}` (the hypothesis `κ ≥ (d²ℓ)⁻¹` of the target),
  with a gap of size `κ/4` that is uniform in the parameters.
* `freqCut r p = freqProfile (r⁻¹ • p)` — the cutoff at scale `r`: `1` on the ball of radius `r`,
  supported in the ball of radius `5r/4`.
* `smearK r` — the smoothing kernel: the inverse `p`-convention Fourier transform of `freqCut r`.
  Its transform is `freqCut r` (proved in `Work.BoseBoxFock.FRK.smearK_kinFT`); since `freqCut r`
  is smooth with compact support, `smearK r` is Schwartz, hence in `L¹ ∩ L^∞`.

The state-level objects (`u = 1_Λ Qψ`, `χ = χ_Λ`, the convolution identities) live in the main
module `Work.BoseBoxFock.FRK.windowHigh_le`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The fixed radial profile -/

/-- The fixed smooth radial profile of the frequency cutoff: `1` on `closedBall 0 1`, supported
in `ball 0 (5/4)`. -/
noncomputable def freqProfile : ContDiffBump (0 : E3) where
  rIn := 1
  rOut := 5 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma freqProfile_nonneg (x : E3) : 0 ≤ freqProfile x := freqProfile.nonneg

lemma freqProfile_le_one (x : E3) : freqProfile x ≤ 1 := freqProfile.le_one

lemma freqProfile_eq_one {x : E3} (hx : ‖x‖ ≤ 1) : freqProfile x = 1 := by
  refine ContDiffBump.one_of_mem_closedBall (f := freqProfile) ?_
  simpa [Metric.mem_closedBall, dist_eq_norm, freqProfile] using hx

lemma freqProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) freqProfile := freqProfile.contDiff

lemma freqProfile_hasCompactSupport : HasCompactSupport freqProfile :=
  freqProfile.hasCompactSupport

lemma freqProfile_even (x : E3) : freqProfile (-x) = freqProfile x := freqProfile.neg x

lemma freqProfile_norm_lt {x : E3} (hx : freqProfile x ≠ 0) : ‖x‖ < 5 / 4 := by
  have hball : x ∈ Metric.ball (0 : E3) freqProfile.rOut := by
    rw [← ContDiffBump.support_eq freqProfile]
    exact hx
  simpa [Metric.mem_ball, dist_eq_norm, freqProfile] using hball

@[simp] lemma freqProfile_zero : freqProfile (0 : E3) = 1 :=
  freqProfile_eq_one (by simp)

/-! ## 2. The cutoff at scale `r` -/

/-- The frequency cutoff at scale `r`: `φ(p) = freqProfile (r⁻¹ • p)`. -/
noncomputable def freqCut (r : ℝ) : E3 → ℝ := fun p => freqProfile (r⁻¹ • p)

lemma freqCut_nonneg (r : ℝ) (p : E3) : 0 ≤ freqCut r p := by
  simpa [freqCut] using freqProfile.nonneg (x := r⁻¹ • p)

lemma freqCut_le_one (r : ℝ) (p : E3) : freqCut r p ≤ 1 := by
  simpa [freqCut] using freqProfile.le_one (x := r⁻¹ • p)

@[simp] lemma freqCut_zero (r : ℝ) : freqCut r 0 = 1 := by simp [freqCut]

/-- On the ball of radius `r` the cutoff is identically `1`. -/
lemma freqCut_eq_one {r : ℝ} (hr : 0 < r) {p : E3} (hp : ‖p‖ ≤ r) : freqCut r p = 1 := by
  refine freqProfile_eq_one ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [inv_mul_le_iff₀ hr]
  simpa using hp

/-- Off the ball of radius `5r/4` the cutoff vanishes. -/
lemma freqCut_ne_zero_le {r : ℝ} (hr : 0 < r) {p : E3} (hp : freqCut r p ≠ 0) :
    ‖p‖ ≤ 5 * r / 4 := by
  have h := freqProfile_norm_lt hp
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at h
  rw [inv_mul_lt_iff₀ hr] at h
  linarith

lemma freqCut_contDiff {r : ℝ} (hr : r ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (freqCut r) := by
  unfold freqCut
  exact freqProfile_contDiff.comp
    (ContinuousLinearMap.contDiff ((r⁻¹) • ContinuousLinearMap.id ℝ E3))

lemma freqCut_hasCompactSupport {r : ℝ} (hr : r ≠ 0) : HasCompactSupport (freqCut r) := by
  unfold freqCut
  let φ : E3 ≃ₜ E3 := Homeomorph.smulOfNeZero (r⁻¹) (inv_ne_zero hr)
  convert freqProfile_hasCompactSupport.comp_homeomorph φ using 1
  ext x
  simp [φ, Homeomorph.smulOfNeZero]

lemma freqCut_even (r : ℝ) (p : E3) : freqCut r (-p) = freqCut r p := by
  rw [freqCut, freqCut, smul_neg, freqProfile_even]

/-! ## 3. The smoothing kernel -/

/-- The smoothing kernel: the inverse `p`-convention Fourier transform of the cutoff `freqCut r`,
written in the (real, even) cosine form. -/
noncomputable def smearK (r : ℝ) : E3 → ℝ :=
  fun x => ((2 * Real.pi) ^ 3 : ℝ)⁻¹ *
    ∫ p : E3, freqCut r p * Real.cos (inner ℝ p x)

end Work.BoseBoxFock.FRK
