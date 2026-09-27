import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.isLevelIsotopy_squash

/-!
# The planar radial map of the star-shaped certificate

Tier `D2d.5` of `N2Lead/NOTES_LEAD_mobiusSaddle.md`.  Given a radius `r₀ > 0`, the **planar radial
map** of `E3 = ℝ³` is

  `radMap r₀ s v = ((1 - σ s) + σ s · r₀ / ‖proj2 v‖) • v`,   `σ = Real.smoothTransition`,

i.e. the straight-line family from the identity (`s ≤ 0`, where `σ = 0`) to the *radial projection*
`v ↦ (r₀ / ‖proj2 v‖) • v` onto the round circle of radius `r₀` about the origin in the plane
(`s ≥ 1`, where `σ = 1`).  Since `σ` is monotone from `0` to `1` and never leaves `[0,1]`, every
slice is a positive multiple of the identity plus a positive multiple of the radial projection.

This file holds the *definition* and the elementary value lemmas (positivity of the coefficient, the
value of the map at `s = 0` and at `s ≥ 1`, the planar projection of the image, the smoothness off
`{proj2 = 0}`).  The derivative/kernel analysis is in `starShaped/radMapCurveDeriv.lean`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

/-- The scaling coefficient of the radial map: `(1 - σ s) + σ s · r₀ / ‖proj2 v‖`. -/
noncomputable def radCoeff (r₀ s : ℝ) (v : E3) : ℝ :=
  (1 - Real.smoothTransition s) + Real.smoothTransition s * (r₀ / ‖proj2 v‖)

/-- **The planar radial map.**  Scale `v` by `(1 - σ s) + σ s · r₀ / ‖proj2 v‖`; at `s ≥ 1` this is
the radial projection onto the round circle of radius `r₀` about the origin. -/
noncomputable def radMap (r₀ s : ℝ) (v : E3) : E3 := radCoeff r₀ s v • v

lemma radMap_def (r₀ s : ℝ) (v : E3) : radMap r₀ s v = radCoeff r₀ s v • v := rfl

lemma radMap_apply (r₀ s : ℝ) (v : E3) :
    radMap r₀ s v = ((1 - Real.smoothTransition s)
      + Real.smoothTransition s * (r₀ / ‖proj2 v‖)) • v := rfl

lemma radCoeff_apply (r₀ s : ℝ) (v : E3) :
    radCoeff r₀ s v = (1 - Real.smoothTransition s)
      + Real.smoothTransition s * (r₀ / ‖proj2 v‖) := rfl

lemma radMap_eq_add (r₀ s : ℝ) (v : E3) :
    radMap r₀ s v = (1 - Real.smoothTransition s) • v
      + Real.smoothTransition s • ((r₀ / ‖proj2 v‖) • v) := by
  rw [radMap, radCoeff, add_smul, mul_smul]

/-- The planar projection is linear. -/
@[simp] lemma proj2_smul (c : ℝ) (v : E3) : proj2 (c • v) = c • proj2 v := by
  apply Complex.ext <;> simp [proj2]

@[simp] lemma proj2_add (v w : E3) : proj2 (v + w) = proj2 v + proj2 w := by
  apply Complex.ext <;> simp [proj2]

/-- At `s = 0` the radial map is the identity. -/
@[simp] lemma radMap_zero (r₀ : ℝ) (v : E3) : radMap r₀ 0 v = v := by
  simp [radMap, radCoeff]

/-- For `s ≥ 1` the radial map is the radial projection of radius `r₀`. -/
lemma radMap_one (r₀ : ℝ) (v : E3) : radMap r₀ 1 v = (r₀ / ‖proj2 v‖) • v := by
  simp [radMap, radCoeff]

lemma radMap_of_one_le (r₀ : ℝ) {s : ℝ} (hs : 1 ≤ s) (v : E3) :
    radMap r₀ s v = (r₀ / ‖proj2 v‖) • v := by
  rw [radMap, radCoeff, Real.smoothTransition.one_of_one_le hs]
  ring_nf

/-- The projection of the image is the coefficient times the projection. -/
lemma proj2_radMap (r₀ s : ℝ) (v : E3) : proj2 (radMap r₀ s v) = radCoeff r₀ s v • proj2 v := by
  rw [radMap, proj2_smul]

/-- **The coefficient is positive.**  Since `σ` stays in `[0,1]`, the coefficient is a convex
combination of `1` and `r₀ / ‖proj2 v‖ > 0`. -/
lemma radCoeff_pos {r₀ : ℝ} (hr₀ : 0 < r₀) (s : ℝ) {v : E3} (hv : proj2 v ≠ 0) :
    0 < radCoeff r₀ s v := by
  have hσ0 : 0 ≤ Real.smoothTransition s := Real.smoothTransition.nonneg s
  have hσ1 : Real.smoothTransition s ≤ 1 := Real.smoothTransition.le_one s
  have hc : 0 < r₀ / ‖proj2 v‖ := div_pos hr₀ (norm_pos_iff.mpr hv)
  rcases eq_or_lt_of_le hσ1 with h | h
  · rw [radCoeff, h]; simpa using hc
  · have h1 : 0 < 1 - Real.smoothTransition s := by linarith
    have h2 : 0 ≤ Real.smoothTransition s * (r₀ / ‖proj2 v‖) := mul_nonneg hσ0 (le_of_lt hc)
    rw [radCoeff]
    linarith

/-- The projection of the round picture. -/
lemma proj2_roundPic (t : ℝ) :
    proj2 (Work.Drive.N2.roundPic t) = (⟨Real.cos t, Real.sin t⟩ : ℂ) := by
  apply Complex.ext <;> simp [proj2, Work.Drive.N2.roundPic]

lemma proj2_smul_roundPic (r₀ t : ℝ) :
    proj2 (r₀ • Work.Drive.N2.roundPic t) = r₀ • (⟨Real.cos t, Real.sin t⟩ : ℂ) := by
  rw [proj2_smul, proj2_roundPic]

/-- The direction of the round picture as a complex number. -/
lemma smul_one_roundPic_eq (z : ℂ) (hz : z ≠ 0) :
    (‖z‖ : ℝ) • (⟨Real.cos (Complex.arg z), Real.sin (Complex.arg z)⟩ : ℂ) = z := by
  rw [Complex.cos_arg hz, Complex.sin_arg z]
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  apply Complex.ext
  · rw [Complex.smul_re, smul_eq_mul]; field_simp
  · rw [Complex.smul_im, smul_eq_mul]; field_simp

/-! ## Smoothness of the radial map off the singular set -/

/-- The scaled inverse norm `v ↦ ‖proj2 v‖⁻¹` is smooth at every point with `proj2 v ≠ 0`. -/
lemma contDiffAt_inv_norm_proj2 {v : E3} (hv : proj2 v ≠ 0) :
    ContDiffAt ℝ tpC (fun v : E3 => (‖proj2 v‖)⁻¹) v :=
  ((proj2CLM.contDiff.contDiffAt).norm ℂ hv).inv (norm_ne_zero_iff.mpr hv)

/-- The coefficient function of one slice `s` is smooth at every point with `proj2 v ≠ 0`. -/
lemma contDiffAt_radCoeff (r₀ s : ℝ) {v : E3} (hv : proj2 v ≠ 0) :
    ContDiffAt ℝ tpC (fun v : E3 => radCoeff r₀ s v) v := by
  have h1 : ContDiffAt ℝ tpC (fun v : E3 => (‖proj2 v‖)⁻¹) v := contDiffAt_inv_norm_proj2 hv
  have h3 : ContDiffAt ℝ tpC
      (fun v : E3 => r₀ * Real.smoothTransition s * (‖proj2 v‖)⁻¹) v :=
    (contDiffAt_const (c := r₀ * Real.smoothTransition s)).mul h1
  have h5 : ContDiffAt ℝ tpC
      (fun v : E3 => (1 - Real.smoothTransition s)
        + r₀ * Real.smoothTransition s * (‖proj2 v‖)⁻¹) v :=
    contDiffAt_const.add h3
  refine h5.congr_of_eventuallyEq ?_
  filter_upwards with w
  rw [radCoeff, div_eq_mul_inv]
  ring

/-- One slice of the radial map is smooth at every point with `proj2 v ≠ 0`. -/
lemma contDiffAt_radMap (r₀ s : ℝ) {v : E3} (hv : proj2 v ≠ 0) :
    ContDiffAt ℝ tpC (fun v : E3 => radMap r₀ s v) v := by
  have hfun : (fun v : E3 => radMap r₀ s v)
      = (fun v : E3 => radCoeff r₀ s v) • (id : E3 → E3) := by
    funext w
    rfl
  rw [hfun]
  exact (contDiffAt_radCoeff r₀ s hv).smul contDiffAt_id

/-- The uncurried radial map `(s, v) ↦ radMap r₀ s v` is smooth at `(s, v)` for `proj2 v ≠ 0`. -/
lemma contDiffAt_uncurry_radMap (r₀ : ℝ) {s : ℝ} {v : E3} (hv : proj2 v ≠ 0) :
    ContDiffAt ℝ tpC (Function.uncurry (radMap r₀)) (s, v) := by
  have hσ : ContDiffAt ℝ tpC (fun p : ℝ × E3 => Real.smoothTransition p.1) (s, v) :=
    Real.smoothTransition.contDiff.contDiffAt.comp (s, v) contDiffAt_fst
  have hproj : ContDiffAt ℝ tpC (fun p : ℝ × E3 => proj2 p.2) (s, v) :=
    proj2CLM.contDiff.contDiffAt.comp (s, v) contDiffAt_snd
  have hpn : ContDiffAt ℝ tpC (fun p : ℝ × E3 => ‖proj2 p.2‖) (s, v) := hproj.norm ℂ hv
  have hinv : ContDiffAt ℝ tpC (fun p : ℝ × E3 => (‖proj2 p.2‖)⁻¹) (s, v) :=
    hpn.inv (norm_ne_zero_iff.mpr hv)
  have hmain : ContDiffAt ℝ tpC
      (fun p : ℝ × E3 => ((1 - Real.smoothTransition p.1)
        + Real.smoothTransition p.1 * (r₀ * (‖proj2 p.2‖)⁻¹)) • p.2) (s, v) :=
    ((contDiffAt_const.sub hσ).add (hσ.mul ((contDiffAt_const (c := r₀)).mul hinv))).smul
      contDiffAt_snd
  have hfun : (fun p : ℝ × E3 => ((1 - Real.smoothTransition p.1)
        + Real.smoothTransition p.1 * (r₀ * (‖proj2 p.2‖)⁻¹)) • p.2)
      = Function.uncurry (radMap r₀) := by
    funext p
    rw [Function.uncurry_apply_pair, radMap, radCoeff, div_eq_mul_inv]
  rw [← hfun]
  exact hmain


/-! ## The value of the radial map at `s ≥ 1` and the algebra of the radial relation -/

/-- The two coordinates of the planar projection, as `simp` lemmas. -/
@[simp] lemma proj2_re (v : E3) : (proj2 v).re = v 0 := rfl
@[simp] lemma proj2_im (v : E3) : (proj2 v).im = v 1 := rfl

/-- A point of `E3` is determined by its planar projection and its third coordinate. -/
lemma eq_of_proj2_eq_of_third_eq {a b : E3} (h : proj2 a = proj2 b) (h3 : a 2 = b 2) : a = b := by
  ext i
  fin_cases i
  · have := congrArg Complex.re h; simpa using this
  · have := congrArg Complex.im h; simpa using this
  · exact h3

/-- At `s ≥ 1` the radial map sends the picture `sq 1 v` (which lies in the plane `{x₃ = 0}`) to
the point of the round circle of radius `r₀` of the same argument as `proj2 v`. -/
lemma radMap_one_sq_one (r₀ : ℝ) {v : E3} (hv : proj2 v ≠ 0) :
    radMap r₀ 1 (sq 1 v) = r₀ • Work.Drive.N2.roundPic (Complex.arg (proj2 v)) := by
  rw [radMap_one]
  refine eq_of_proj2_eq_of_third_eq ?_ ?_
  · simp only [proj2_smul, proj2_sq, proj2_roundPic]
    rw [Complex.cos_arg hv, Complex.sin_arg]
    apply Complex.ext <;>
      simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring_nf
  · simp [sq, Work.Drive.N2.roundPic]

/-- The radial map at `s = 0` composed with the squash at `s = 0` is the identity. -/
lemma radMap_zero_sq_zero (r₀ : ℝ) (v : E3) : radMap r₀ 0 (sq 0 v) = v := by
  rw [radMap_zero]
  ext i
  fin_cases i <;> simp [sq]

/-- **The algebra of the radial relation.**  If `(1-σ)•w + σ•(α•w - β•v) = 0` where `σ` is a value
of `Real.smoothTransition`, `α = r₀/‖proj2 v‖` and `β` is arbitrary, then `w` is a multiple of `v`
(the coefficient `(1-σ) + σ·α` of `w` is positive). -/
lemma eq_smul_of_radial_relation {r₀ s : ℝ} (hr₀ : 0 < r₀) {v w : E3} (hv : proj2 v ≠ 0)
    (h : (1 - Real.smoothTransition s) • w
        + Real.smoothTransition s • ((r₀ / ‖proj2 v‖) • w
          - (r₀ * inner ℝ (proj2 v) (proj2 w) / ‖proj2 v‖ ^ 3) • v) = 0) :
    ∃ t : ℝ, w = t • v := by
  have hCpos : 0 < 1 - Real.smoothTransition s + Real.smoothTransition s * (r₀ / ‖proj2 v‖) := by
    have hh := radCoeff_pos hr₀ s (v := v) hv
    rwa [radCoeff] at hh
  have hkey : (1 - Real.smoothTransition s + Real.smoothTransition s * (r₀ / ‖proj2 v‖)) • w
      = (Real.smoothTransition s
          * (r₀ * inner ℝ (proj2 v) (proj2 w) / ‖proj2 v‖ ^ 3)) • v := by
    have h1 : (1 - Real.smoothTransition s) • w
        + ((Real.smoothTransition s * (r₀ / ‖proj2 v‖)) • w
          - (Real.smoothTransition s
              * (r₀ * inner ℝ (proj2 v) (proj2 w) / ‖proj2 v‖ ^ 3)) • v) = 0 := by
      simpa only [smul_sub, smul_smul] using h
    have h2 : (1 - Real.smoothTransition s) • w
        + (Real.smoothTransition s * (r₀ / ‖proj2 v‖)) • w
        = (Real.smoothTransition s
            * (r₀ * inner ℝ (proj2 v) (proj2 w) / ‖proj2 v‖ ^ 3)) • v := by
      rw [← sub_eq_zero, add_sub_assoc]
      exact h1
    rwa [← add_smul] at h2
  refine ⟨(Real.smoothTransition s * (r₀ * inner ℝ (proj2 v) (proj2 w) / ‖proj2 v‖ ^ 3))
    / (1 - Real.smoothTransition s + Real.smoothTransition s * (r₀ / ‖proj2 v‖)), ?_⟩
  calc w = (1 - Real.smoothTransition s + Real.smoothTransition s * (r₀ / ‖proj2 v‖))⁻¹
        • ((1 - Real.smoothTransition s + Real.smoothTransition s * (r₀ / ‖proj2 v‖)) • w) :=
        (inv_smul_smul₀ hCpos.ne' w).symm
    _ = (1 - Real.smoothTransition s + Real.smoothTransition s * (r₀ / ‖proj2 v‖))⁻¹
        • ((Real.smoothTransition s
            * (r₀ * inner ℝ (proj2 v) (proj2 w) / ‖proj2 v‖ ^ 3)) • v) := by rw [hkey]
    _ = ((1 - Real.smoothTransition s + Real.smoothTransition s * (r₀ / ‖proj2 v‖))⁻¹
        * (Real.smoothTransition s
            * (r₀ * inner ℝ (proj2 v) (proj2 w) / ‖proj2 v‖ ^ 3))) • v := by rw [smul_smul]
    _ = ((Real.smoothTransition s
          * (r₀ * inner ℝ (proj2 v) (proj2 w) / ‖proj2 v‖ ^ 3))
        / (1 - Real.smoothTransition s + Real.smoothTransition s * (r₀ / ‖proj2 v‖))) • v := by
        rw [div_eq_inv_mul] <;> ring

/-- The `mfderiv` of the planar projection, applied to a tangent vector. -/
lemma mfderiv_proj2_apply_tangent {x : E3} (u : TangentSpace (𝓡 3) x) :
    (mfderiv (𝓡 3) 𝓘(ℝ, ℂ) proj2 x) u = proj2 u := by
  have h := mfderiv_proj2 x
  exact DFunLike.congr_fun h u

end

end Work.Drive.N2Lead
