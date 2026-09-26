import Mathlib
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective
import Submission.Work.Smooth.SphereJordan.no_retraction_disc

/-!
# Brouwer's fixed point theorem for the closed disc

Let `𝔻 = Metric.closedBall (0 : ℂ) 1` be the closed unit disc of the plane and let
`Φ : 𝔻 → 𝔻` be continuous.  Then `Φ` has a fixed point
(`Work.Smooth.SphereJordan.brouwer_disc`).

## The mathematics

The proof is the classical reduction of Brouwer's theorem to the non-existence of a retraction
of the disc onto its boundary circle (`Work.Smooth.SphereJordan.no_retraction_disc`, already in
the workspace):

* if `Φ` had no fixed point, then for every `x ∈ 𝔻` the point `Φ x` differs from `x`, so the
  ray starting at `Φ x` and passing through `x` is well defined; let `r x` be the point where
  this ray meets the unit circle.  Since `‖Φ x‖ ≤ 1`, the ray meets the circle exactly once in
  the direction of `x` and `r x` is given by the *radial projection* `radialProj (Φ x) x` of
  `discEmbedding_surjective.lean`;
* for `‖x‖ = 1` the ray leaves the disc through `x` itself, so `r x = x`: the boundary circle is
  fixed pointwise;
* `r` is continuous, because `x ↦ (Φ x, x)` is a continuous map of `𝔻` into the complement of
  the diagonal of `ℂ × ℂ`, on which `(y, x) ↦ radialProj y x` is continuous (the only
  discontinuity of `rayDir` is at `y = x`);
* hence `r` is a continuous retraction of `𝔻` onto its boundary circle, contradicting
  `no_retraction_disc`.

The two facts about the radial projection that are *not* in `discEmbedding_surjective.lean` are
proved here in the form needed, with the hypothesis `‖y‖ ≤ 1` rather than `‖y‖ < 1` (the base
point `Φ x` may very well lie on the boundary circle), together with the *joint* continuity of
`(y, x) ↦ radialProj y x` off the diagonal.

## Main result

* `Work.Smooth.SphereJordan.brouwer_disc` — every continuous self-map of the closed disc has a
  fixed point.
-/

open Set
open scoped InnerProductSpace

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Elementary facts about the closed disc -/

/-- Every point of the model disc has norm at most one. -/
theorem coreNormCoeLeOne (z : Disc) : ‖((z : Disc) : ℂ)‖ ≤ 1 := by
  have h := z.2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  exact h

/-- The boundary circle `θ ↦ e^{iθ}` has norm one. -/
theorem coreNormCirclePoint' (θ : ℝ) : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-! ## The radial projection away from a point of the closed disc

`discEmbedding_surjective.lean` proves, for a base point `y` *inside* the disc (`‖y‖ < 1`), that
the radial projection `radialProj y ·` lands on the unit circle and fixes it.  For Brouwer's
theorem the base point is `Φ x`, which is only known to lie in the *closed* disc; the two lemmas
below record that both facts continue to hold for `‖y‖ ≤ 1` (the strict inequality in the earlier
file was only used to know that the ray meets the circle, which is equally true when `y` is on the
circle). -/

/-- **The radial projection of the disc away from `y ∈ 𝔻` lands on the unit circle.** -/
theorem norm_radialProj_of_norm_le (y : ℂ) (hy : ‖y‖ ≤ 1) {x : ℂ} (hx : x ≠ y) :
    ‖radialProj y x‖ = 1 := by
  have hu : ‖rayDir y x‖ = 1 := norm_rayDir hx
  have hkey : ‖radialProj y x‖ ^ 2 = 1 := by
    have h := norm_add_smul_sq y (rayDir y x) hu (radialParam y (rayDir y x))
    have hs := radialParam_eq y (rayDir y x) hy hu
    show ‖y + radialParam y (rayDir y x) • rayDir y x‖ ^ 2 = 1
    linarith [h, hs]
  have hsq : (‖radialProj y x‖ - 1) * (‖radialProj y x‖ + 1) = 0 := by nlinarith [hkey]
  rcases mul_eq_zero.mp hsq with h | h
  · linarith
  · have : 0 ≤ ‖radialProj y x‖ := norm_nonneg _; linarith

/-- **The radial projection away from `y ∈ 𝔻` fixes the boundary circle.**  For `‖x‖ = 1` the ray
from `y` through `x` leaves the closed disc exactly at `x`. -/
theorem radialProj_eq_self_of_norm_le (y : ℂ) (hy : ‖y‖ ≤ 1) {x : ℂ} (hx : x ≠ y)
    (hx1 : ‖x‖ = 1) : radialProj y x = x := by
  have hu : ‖rayDir y x‖ = 1 := norm_rayDir hx
  have hdecomp : y + (‖x - y‖ : ℝ) • rayDir y x = x := by rw [rayDir_smul hx]; abel
  have ht : ‖x - y‖ ^ 2 + 2 * ⟪y, rayDir y x⟫_ℝ * ‖x - y‖ = 1 - ‖y‖ ^ 2 := by
    have h := norm_add_smul_sq y (rayDir y x) hu (‖x - y‖)
    rw [hdecomp, hx1] at h
    linarith
  have hs := radialParam_eq y (rayDir y x) hy hu
  have hfac : (‖x - y‖ - radialParam y (rayDir y x)) *
      (‖x - y‖ + radialParam y (rayDir y x) + 2 * ⟪y, rayDir y x⟫_ℝ) = 0 := by
    nlinarith [hs, ht]
  -- the square root dominates `-⟪y,u⟫` because `‖y‖ ≤ 1`, so the second root of the quadratic is
  -- nonpositive while `‖x - y‖ > 0`: the latter must be `radialParam`
  have hsqrt : |⟪y, rayDir y x⟫_ℝ| ≤
      Real.sqrt (⟪y, rayDir y x⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2) := by
    rw [Real.le_sqrt (abs_nonneg _) (sqrt_arg_nonneg y (rayDir y x) hy hu)]
    rw [sq_abs]
    nlinarith [norm_nonneg y]
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hfac2 : ‖x - y‖ + radialParam y (rayDir y x) + 2 * ⟪y, rayDir y x⟫_ℝ ≠ 0 := by
    intro h0
    have h1 : ‖x - y‖ = -(radialParam y (rayDir y x) + 2 * ⟪y, rayDir y x⟫_ℝ) := by linarith
    simp only [radialParam] at h1
    linarith [hsqrt, neg_le_abs ⟪y, rayDir y x⟫_ℝ]
  have h1 : ‖x - y‖ = radialParam y (rayDir y x) := by
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · exact absurd h hfac2
  rw [show radialProj y x = y + radialParam y (rayDir y x) • rayDir y x from rfl, ← h1]
  exact hdecomp

/-! ## Joint continuity of the radial projection off the diagonal -/

/-- The direction `rayDir` is continuous as a function of the pair `(y, x)`, away from the
diagonal `y = x`. -/
theorem continuousAt_rayDir_pair {y x : ℂ} (hxy : x ≠ y) :
    ContinuousAt (fun p : ℂ × ℂ => rayDir p.1 p.2) (y, x) := by
  have hnum : ContinuousAt (fun p : ℂ × ℂ => p.2 - p.1) (y, x) :=
    (continuous_snd.sub continuous_fst).continuousAt
  have hden : ContinuousAt (fun p : ℂ × ℂ => ((‖p.2 - p.1‖ : ℝ) : ℂ)) (y, x) :=
    Complex.continuous_ofReal.continuousAt.comp
      ((continuous_snd.sub continuous_fst).norm.continuousAt)
  have hne : ((‖x - y‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  exact hnum.div hden hne

/-- `radialParam` is continuous as a function of the pair `(y, u)`. -/
theorem continuous_radialParam_pair : Continuous fun q : ℂ × ℂ => radialParam q.1 q.2 := by
  simp only [radialParam]
  fun_prop

/-- **The radial projection is continuous as a function of the pair `(y, x)`, off the diagonal**
`y = x` (the only singularity of `rayDir`). -/
theorem continuousAt_radialProj_pair {y x : ℂ} (hxy : x ≠ y) :
    ContinuousAt (fun p : ℂ × ℂ => radialProj p.1 p.2) (y, x) := by
  have hdir : ContinuousAt (fun p : ℂ × ℂ => rayDir p.1 p.2) (y, x) :=
    continuousAt_rayDir_pair hxy
  have hkey : ContinuousAt (fun p : ℂ × ℂ => (p.1, rayDir p.1 p.2)) (y, x) :=
    continuousAt_fst.prodMk hdir
  have h1 : ContinuousAt (fun p : ℂ × ℂ => radialParam p.1 (rayDir p.1 p.2)) (y, x) :=
    ContinuousAt.comp (f := fun p : ℂ × ℂ => (p.1, rayDir p.1 p.2))
      continuous_radialParam_pair.continuousAt hkey
  have h2 : ContinuousAt
      (fun p : ℂ × ℂ => radialParam p.1 (rayDir p.1 p.2) • rayDir p.1 p.2) (y, x) :=
    h1.smul hdir
  have h3 : ContinuousAt (fun p : ℂ × ℂ => p.1) (y, x) := continuousAt_fst
  show ContinuousAt (fun p : ℂ × ℂ =>
    p.1 + radialParam p.1 (rayDir p.1 p.2) • rayDir p.1 p.2) (y, x)
  exact h3.add h2

/-! ## Brouwer's fixed point theorem -/

/-- **A fixed-point-free continuous self-map of the disc retracts the disc onto its boundary.**

If `Φ : 𝔻 → 𝔻` is continuous with no fixed point, then `x ↦ radialProj (Φ x) x` is a continuous
map of the disc into the unit circle which fixes the boundary circle pointwise. -/
theorem exists_retraction_of_no_fixed_point (Φ : C(Disc, Disc)) (h : ∀ x : Disc, Φ x ≠ x) :
    ∃ r : C(Disc, Disc), (∀ z : Disc, ‖((r z : Disc) : ℂ)‖ = 1) ∧
      (∀ θ : ℝ, r (circlePoint θ) = circlePoint θ) := by
  -- the pair `(Φ x, x)` never crosses the diagonal, so the radial projection is continuous
  have hne : ∀ z : Disc, ((z : Disc) : ℂ) ≠ ((Φ z : Disc) : ℂ) := by
    intro z heq
    exact h z (Subtype.ext heq).symm
  have hcont : Continuous fun z : Disc => radialProj ((Φ z : Disc) : ℂ) ((z : Disc) : ℂ) := by
    rw [continuous_iff_continuousAt]
    intro z
    have hpair : ContinuousAt (fun p : ℂ × ℂ => radialProj p.1 p.2)
        (((Φ z : Disc) : ℂ), ((z : Disc) : ℂ)) :=
      continuousAt_radialProj_pair (hne z)
    have hmap : ContinuousAt (fun w : Disc => (((Φ w : Disc) : ℂ), ((w : Disc) : ℂ))) z :=
      ((continuous_subtype_val.comp Φ.continuous).continuousAt).prodMk
        continuous_subtype_val.continuousAt
    exact ContinuousAt.comp (f := fun w : Disc => (((Φ w : Disc) : ℂ), ((w : Disc) : ℂ)))
      (g := fun p : ℂ × ℂ => radialProj p.1 p.2) hpair hmap
  have hmem : ∀ z : Disc,
      radialProj ((Φ z : Disc) : ℂ) ((z : Disc) : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (norm_radialProj_of_norm_le _ (coreNormCoeLeOne (Φ z)) (hne z))
  let r : C(Disc, Disc) :=
    ⟨fun z => ⟨radialProj ((Φ z : Disc) : ℂ) ((z : Disc) : ℂ), hmem z⟩,
      hcont.subtype_mk hmem⟩
  refine ⟨r, fun z => norm_radialProj_of_norm_le _ (coreNormCoeLeOne (Φ z)) (hne z), ?_⟩
  intro θ
  apply Subtype.ext
  show radialProj ((Φ (circlePoint θ) : Disc) : ℂ) ((circlePoint θ : Disc) : ℂ)
      = ((circlePoint θ : Disc) : ℂ)
  exact radialProj_eq_self_of_norm_le _ (coreNormCoeLeOne (Φ (circlePoint θ)))
    (hne (circlePoint θ)) (coreNormCirclePoint' θ)

/-- **Brouwer's fixed point theorem for the closed disc.**  Every continuous self-map of the closed
unit disc `𝔻 = Metric.closedBall (0 : ℂ) 1` has a fixed point.

If `Φ` had no fixed point, the radial projection of `𝔻` away from `Φ x` would be a continuous
retraction of `𝔻` onto its boundary circle, contradicting
`Work.Smooth.SphereJordan.no_retraction_disc`. -/
theorem brouwer_disc (Φ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)) :
    ∃ x : Work.Smooth.SphereJordan.Disc, Φ x = x := by
  by_contra h
  simp only [not_exists] at h
  obtain ⟨r, hr, hf⟩ := exists_retraction_of_no_fixed_point Φ h
  exact no_retraction_disc r hr hf

end

end Work.Smooth.SphereJordan
