import Mathlib
import Submission.Work.Drive.framedPolarDefs
import Submission.Work.Drive.contDiff_framedSliceFamily

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# The slices of the framed star-shaped interpolation are smooth knots

The `s`-th slice of the framed star-shaped interpolation is the curve

`t ↦ framedCurve lam psi c u v s t
      = (1 - s) • c + starRad lam s t • (cos (starAngle psi s t) • u
                                          + sin (starAngle psi s t) • v)`

where `(u, v)` is an orthonormal pair of vectors of `Space`, `lam > 0` is
`period`-periodic and analytic, and `psi` is analytic with
`psi (t + period) = psi t + period` and `deriv psi > 0`.

Because `(starRad lam s, starAngle psi s)` has exactly the same properties as
`(lam, psi)` for `s ∈ [0, 1]` (positive `period`-periodic radius, angle
increasing and shifting by `period`), the slice is a star-shaped polar graph of
the plane spanned by `u` and `v`: it is periodic, injective on one period and
nowhere singular.  The only new ingredient compared with the coordinate case
(`starSlice_injOn`, `starSlice_velocity_ne_zero`) is the orthonormal frame: the
direction map `θ ↦ cos θ • u + sin θ • v` is a unit vector (`frameDir_norm`) and
is read back by the scalar products with `u` and `v` (`frameDir_inner_u`,
`frameDir_inner_v`); its derivative is the orthogonal vector `frameTan`.
-/

/-- The direction of the framed polar graph at angle `θ`: `cos θ • u + sin θ • v`.
For an orthonormal pair `(u, v)` this is a unit vector. -/
noncomputable def frameDir (u v : Space) (θ : ℝ) : Space :=
  Real.cos θ • u + Real.sin θ • v

/-- The tangent direction of the framed polar graph at angle `θ`:
`-sin θ • u + cos θ • v`, the rotation of `frameDir u v θ` by `π / 2`. -/
noncomputable def frameTan (u v : Space) (θ : ℝ) : Space :=
  (-Real.sin θ) • u + Real.cos θ • v

/-- The slice of the framed interpolation written with the frame direction. -/
lemma framedCurve_eq (lam psi : ℝ → ℝ) (c u v : Space) (s t : ℝ) :
    framedCurve lam psi c u v s t
      = (1 - s) • c + starRad lam s t • frameDir u v (starAngle psi s t) := rfl

/-- The scalar product with `u` reads off the cosine of the frame direction. -/
lemma frameDir_inner_u {u v : Space} (hu : ‖u‖ = 1) (huv : inner ℝ u v = 0) (θ : ℝ) :
    inner ℝ u (frameDir u v θ) = Real.cos θ := by
  simp only [frameDir, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, huv,
    mul_zero, add_zero]
  rw [hu]
  norm_num

/-- The scalar product with `v` reads off the sine of the frame direction. -/
lemma frameDir_inner_v {u v : Space} (hv : ‖v‖ = 1) (hvu : inner ℝ v u = 0) (θ : ℝ) :
    inner ℝ v (frameDir u v θ) = Real.sin θ := by
  simp only [frameDir, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hvu,
    mul_zero]
  rw [hv]
  norm_num

/-- The frame direction is a unit vector when `(u, v)` is an orthonormal pair. -/
lemma frameDir_norm {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (θ : ℝ) : ‖frameDir u v θ‖ = 1 := by
  have hii : inner ℝ (frameDir u v θ) (frameDir u v θ) = 1 := by
    simp only [frameDir, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm, hu, hv, huv, mul_zero, add_zero,
      RCLike.conj_to_real]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h2 := real_inner_self_eq_norm_sq (frameDir u v θ)
  rw [hii] at h2
  nlinarith [norm_nonneg (frameDir u v θ)]

/-- The frame direction is `period`-periodic in the angle. -/
lemma frameDir_add_period (u v : Space) (θ : ℝ) :
    frameDir u v (θ + period) = frameDir u v θ := by
  simp only [frameDir, starCosAddPeriod θ, starSinAddPeriod θ]

/-- The frame tangent pairs with the frame direction through the sine of the
angle difference. -/
lemma frameTan_inner_frameDir {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (θt θ : ℝ) :
    inner ℝ (frameTan u v θt) (frameDir u v θ) = Real.sin (θ - θt) := by
  simp only [frameDir, frameTan, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm, hu, hv, huv, mul_zero,
    add_zero, RCLike.conj_to_real]
  rw [Real.sin_sub]
  ring

/-- The framed slice is analytic in the curve parameter. -/
lemma contDiff_framedCurve_time {lam psi : ℝ → ℝ} (c u v : Space) (s : ℝ)
    (hlam : ContDiff ℝ ⊤ lam) (hpsi : ContDiff ℝ ⊤ psi) :
    ContDiff ℝ ⊤ (fun t : ℝ => framedCurve lam psi c u v s t) := by
  have h := contDiff_framedSliceFamily c hlam hpsi (g := fun _ : ℝ => (u, v)) contDiff_const
  have h2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => framedCurve lam psi c u v p.2 p.1) := by
    simpa [framedSlice_eq_framedCurve] using h
  exact h2.comp (contDiff_id.prodMk contDiff_const)

/-- The framed slice is `period`-periodic. -/
lemma framedCurve_periodic {lam psi : ℝ → ℝ} (c u v : Space) (s : ℝ)
    (hper : Function.Periodic lam period)
    (hshift : ∀ t : ℝ, psi (t + period) = psi t + period) :
    Function.Periodic (fun t : ℝ => framedCurve lam psi c u v s t) period := by
  intro t
  have ha := starAngle_shift hshift s t
  have hr := starRad_periodic hper s t
  show (1 - s) • c + starRad lam s (t + period) • frameDir u v (starAngle psi s (t + period))
      = (1 - s) • c + starRad lam s t • frameDir u v (starAngle psi s t)
  rw [ha, hr, frameDir_add_period]

/-- **The framed slices are injective on one period.**  Equal values force equal
radii (by taking norms, `frameDir` being a unit vector) and equal directions;
the direction determines the angle through its scalar products with `u` and `v`,
two angles coming from `[0, period)` differ by less than `2π`, and the angle is
strictly increasing. -/
theorem framedCurve_injOn {lam psi : ℝ → ℝ} {c u v : Space}
    (h1 : ‖u‖ = 1) (h2 : ‖v‖ = 1) (hperp : inner ℝ u v = 0)
    (hψ : StrictMono psi) (hlampos : ∀ t : ℝ, 0 < lam t)
    (hpsishift : ∀ t : ℝ, psi (t + period) = psi t + period)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Set.InjOn (fun t : ℝ => framedCurve lam psi c u v s t) (Set.Ico (0 : ℝ) period) := by
  intro t ht t' ht' heq
  change framedCurve lam psi c u v s t = framedCurve lam psi c u v s t' at heq
  rw [framedCurve_eq, framedCurve_eq] at heq
  have hsplit : starRad lam s t • frameDir u v (starAngle psi s t)
      = starRad lam s t' • frameDir u v (starAngle psi s t') := add_left_cancel heq
  -- equal radii, by taking norms and using that the directions are unit vectors
  have hrad : starRad lam s t = starRad lam s t' := by
    have h := congrArg norm hsplit
    rw [norm_smul, norm_smul, frameDir_norm h1 h2 hperp, frameDir_norm h1 h2 hperp,
      mul_one, mul_one, Real.norm_of_nonneg (le_of_lt (starRad_pos hlampos hs0 hs1 t)),
      Real.norm_of_nonneg (le_of_lt (starRad_pos hlampos hs0 hs1 t'))] at h
    exact h
  -- equal directions
  have hdir : frameDir u v (starAngle psi s t) = frameDir u v (starAngle psi s t') := by
    rw [hrad] at hsplit
    exact smul_right_injective Space (ne_of_gt (starRad_pos hlampos hs0 hs1 t')) hsplit
  -- the direction determines the angle modulo `2π`; read off cosine and sine
  have hcos : Real.cos (starAngle psi s t) = Real.cos (starAngle psi s t') := by
    have h := congrArg (inner ℝ u) hdir
    rwa [frameDir_inner_u h1 hperp, frameDir_inner_u h1 hperp] at h
  have hsin : Real.sin (starAngle psi s t) = Real.sin (starAngle psi s t') := by
    have h := congrArg (inner ℝ v) hdir
    rwa [frameDir_inner_v h2 (by rw [real_inner_comm]; exact hperp),
      frameDir_inner_v h2 (by rw [real_inner_comm]; exact hperp)] at h
  have hsub := starAngle_sub_abs_lt hψ hpsishift hs0 hs1 ht ht'
  rw [show period = 2 * Real.pi from rfl] at hsub
  exact (starAngle_strictMono hψ hs0 hs1).injective (star_angle_eq_of_cos_sin_eq hsub hcos hsin)

/-- **The framed slices are everywhere regular.**  The velocity is
`ρ • (θ' • tangent) + ρ' • direction`, and pairing it with the unit tangent
`frameTan` at `t` gives the strictly positive number `ρ * θ'`. -/
theorem framedCurve_velocity_ne_zero {lam psi : ℝ → ℝ} {c u v : Space}
    (h1 : ‖u‖ = 1) (h2 : ‖v‖ = 1) (hperp : inner ℝ u v = 0)
    (hlam : ContDiff ℝ ⊤ lam) (hpsi : ContDiff ℝ ⊤ psi)
    (hlampos : ∀ t : ℝ, 0 < lam t) (hpsideriv : ∀ t : ℝ, 0 < deriv psi t)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) :
    velocity (fun x : ℝ => framedCurve lam psi c u v s x) t ≠ 0 := by
  set θt : ℝ := starAngle psi s t with hθt
  set w : Space := frameTan u v θt with hw
  have hg : DifferentiableAt ℝ (fun x : ℝ => framedCurve lam psi c u v s x) t :=
    ((contDiff_framedCurve_time c u v s hlam hpsi).differentiable (by simp)).differentiableAt
  -- `⟪w, ·⟫` along the slice is `const + ρ x * sin (θ x - θt)`
  have hin : ∀ x : ℝ, inner ℝ w (framedCurve lam psi c u v s x)
      = inner ℝ w ((1 - s) • c) + starRad lam s x * Real.sin (starAngle psi s x - θt) := by
    intro x
    rw [framedCurve_eq, hw]
    simp only [inner_add_right, inner_smul_right,
      frameTan_inner_frameDir (u := u) (v := v) (θt := θt) (θ := starAngle psi s x) h1 h2 hperp]
  -- whose derivative at `t` is `ρ t * θ' t`
  have hderiv : deriv (fun x : ℝ => inner ℝ w (framedCurve lam psi c u v s x)) t
      = starRad lam s t * ((1 - s) * deriv psi t + s) := by
    have hfun : (fun x : ℝ => inner ℝ w (framedCurve lam psi c u v s x))
        = fun x => inner ℝ w ((1 - s) • c)
            + starRad lam s x * Real.sin (starAngle psi s x - θt) := funext hin
    have hρ : HasDerivAt (starRad lam s) ((1 - s) * deriv lam t) t :=
      ((hlam.differentiable (by simp)).differentiableAt.hasDerivAt.const_mul (1 - s)).add_const s
    have hθ : HasDerivAt (starAngle psi s) ((1 - s) * deriv psi t + s) t := by
      change HasDerivAt (fun y : ℝ => (1 - s) * psi y + s * y) ((1 - s) * deriv psi t + s) t
      have h1' : HasDerivAt (fun y : ℝ => (1 - s) * psi y) ((1 - s) * deriv psi t) t :=
        (hpsi.differentiable (by simp)).differentiableAt.hasDerivAt.const_mul (1 - s)
      have h2' : HasDerivAt (fun y : ℝ => s * y) s t := by
        simpa using (hasDerivAt_id t).const_mul s
      exact h1'.add h2'
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (starAngle psi s y - θt))
        (Real.cos (starAngle psi s t - θt) * ((1 - s) * deriv psi t + s)) t :=
      (hθ.sub_const θt).sin
    have hd : HasDerivAt (fun x : ℝ => inner ℝ w ((1 - s) • c)
          + starRad lam s x * Real.sin (starAngle psi s x - θt))
        (starRad lam s t * ((1 - s) * deriv psi t + s)) t := by
      have hmul := hρ.mul hsin
      simpa [Pi.mul_apply, ← hθt] using hmul.const_add (inner ℝ w ((1 - s) • c))
    rw [hfun]
    exact hd.deriv
  -- chain rule: this is `⟪w, velocity⟫`
  have hchain : deriv (fun x : ℝ => inner ℝ w (framedCurve lam psi c u v s x)) t
      = inner ℝ w (deriv (fun x : ℝ => framedCurve lam psi c u v s x) t) := by
    have h := deriv_inner_apply ℝ (f := fun _ : ℝ => w)
      (g := fun x : ℝ => framedCurve lam psi c u v s x) (x := t) (differentiableAt_const w) hg
    simpa only [deriv_const, inner_zero_left, add_zero] using h
  -- positivity of `ρ t * θ' t`
  have hρpos : 0 < starRad lam s t := starRad_pos hlampos hs0 hs1 t
  have hθpos : 0 < (1 - s) * deriv psi t + s := by
    rcases lt_or_eq_of_le hs1 with hs | hs
    · have hlt : 0 < 1 - s := sub_pos.mpr hs
      have := mul_pos hlt (hpsideriv t)
      linarith
    · rw [hs]; norm_num
  intro hzero
  have hzero' : deriv (fun x : ℝ => framedCurve lam psi c u v s x) t = 0 := hzero
  have hval : deriv (fun x : ℝ => inner ℝ w (framedCurve lam psi c u v s x)) t = 0 := by
    rw [hchain, hzero']
    simp
  rw [hderiv] at hval
  exact absurd hval (ne_of_gt (mul_pos hρpos hθpos))

theorem isSmoothKnot_framedCurve {lam psi : ℝ → ℝ} {c u v : LeanEval.KnotTheory.Quadrisecant.Space}
    (h1 : ‖u‖ = 1) (h2 : ‖v‖ = 1) (hperp : inner ℝ u v = 0)
    (hlam : ContDiff ℝ ⊤ lam)
    (hlamper : Function.Periodic lam LeanEval.KnotTheory.Quadrisecant.period)
    (hlampos : ∀ t : ℝ, 0 < lam t) (hpsi : ContDiff ℝ ⊤ psi)
    (hpsishift : ∀ t : ℝ, psi (t + LeanEval.KnotTheory.Quadrisecant.period)
      = psi t + LeanEval.KnotTheory.Quadrisecant.period)
    (hpsideriv : ∀ t : ℝ, 0 < deriv psi t)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot
      (fun t : ℝ => Work.Drive.framedCurve lam psi c u v s t) :=
  { smooth := contDiff_framedCurve_time c u v s hlam hpsi
    periodic := framedCurve_periodic c u v s hlamper hpsishift
    injective_on_period :=
      framedCurve_injOn h1 h2 hperp (strictMono_of_deriv_pos hpsideriv) hlampos hpsishift hs.1 hs.2
    regular := fun t =>
      framedCurve_velocity_ne_zero h1 h2 hperp hlam hpsi hlampos hpsideriv hs.1 hs.2 t }

end Work.Drive
