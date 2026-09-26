import Mathlib
import Submission.Work.Drive.isUnknotted_of_polarGraph

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# Star-shaped polar graphs are unknotted

A *star-shaped polar graph* is a curve
`t ↦ c + lam t • !₂[cos (psi t), sin (psi t), 0]`
where `lam : ℝ → ℝ` is analytic, `period`-periodic and positive and
`psi : ℝ → ℝ` is analytic with `psi (t + period) = psi t + period` and
`0 < deriv psi t` everywhere.  Thus `psi` is an orientation-preserving
diffeomorphism of the parameter circle and the curve is the graph of a
star-shaped plane region: in polar coordinates the radius `lam` is a positive
function of the angle `psi`, and `psi` sweeps the circle exactly once per
period.

The explicit analytic unknotting is obtained by interpolating both polar
coordinates to those of the round circle: with
`ρ s t = (1 - s) * lam t + s` (radius `lam` → `1`) and
`θ s t = (1 - s) * psi t + s * t` (angle `psi` → identity), the single formula
`R t s = !₂[ρ s t * cos (θ s t), ρ s t * sin (θ s t), 0]`
is analytic in `(t, s)`, equals the given curve at `s = 0`, equals
`standardCircle` at `s = 1`, and every slice is a smooth knot: a convex
combination of two orientation-preserving circle diffeomorphisms is again one
(`starAngle_strictMono`), the radius stays positive (`starRad_pos`), so the
slice is injective on one period (`injOn_starSlice`) and everywhere regular
(`velocity_starSlice_ne_zero`).  The translation by `c` is then removed with
`isUnknotted_constAdd`.

Everything is elementary: no knot theory, no compactness, no Dehn lemma.
-/

/-- The interpolated polar angle `θ s t = (1 - s) * psi t + s * t`. -/
def starAngle (psi : ℝ → ℝ) (s t : ℝ) : ℝ := (1 - s) * psi t + s * t

/-- The interpolated radius `ρ s t = (1 - s) * lam t + s`. -/
def starRad (lam : ℝ → ℝ) (s t : ℝ) : ℝ := (1 - s) * lam t + s

/-- The `s`-th slice of the star-shaped unknotting family. -/
noncomputable def starSlice (lam psi : ℝ → ℝ) (s t : ℝ) : Space :=
  !₂[starRad lam s t * Real.cos (starAngle psi s t),
     starRad lam s t * Real.sin (starAngle psi s t), (0 : ℝ)]

@[simp] lemma starAngle_zero (psi : ℝ → ℝ) (t : ℝ) : starAngle psi 0 t = psi t := by
  simp [starAngle]

@[simp] lemma starAngle_one (psi : ℝ → ℝ) (t : ℝ) : starAngle psi 1 t = t := by
  simp [starAngle]

@[simp] lemma starRad_zero (lam : ℝ → ℝ) (t : ℝ) : starRad lam 0 t = lam t := by
  simp [starRad]

@[simp] lemma starRad_one (lam : ℝ → ℝ) (t : ℝ) : starRad lam 1 t = 1 := by
  simp [starRad]

@[simp] lemma starSlice_zero (lam psi : ℝ → ℝ) (t : ℝ) :
    starSlice lam psi 0 t = !₂[lam t * Real.cos (psi t), lam t * Real.sin (psi t), (0 : ℝ)] := by
  simp [starSlice, starRad, starAngle]

@[simp] lemma starSlice_one (lam psi : ℝ → ℝ) (t : ℝ) :
    starSlice lam psi 1 t = standardCircle t := by
  simp [starSlice, starRad, starAngle, standardCircle]

/-- The slice as a radius times the unit circle point. -/
lemma starSlice_eq_smul (lam psi : ℝ → ℝ) (s t : ℝ) :
    starSlice lam psi s t =
      starRad lam s t • (!₂[Real.cos (starAngle psi s t), Real.sin (starAngle psi s t),
        (0 : ℝ)] : Space) := by
  ext i
  fin_cases i <;> simp [starSlice, PiLp.smul_apply]

/-- The slice written with the two coordinate vectors of the plane (the form in
which the scalar product/chain rules apply). -/
lemma starSlice_eq_vec (lam psi : ℝ → ℝ) (s t : ℝ) :
    starSlice lam psi s t = starRad lam s t •
      (Real.cos (starAngle psi s t) • e1 + Real.sin (starAngle psi s t) • e2) := by
  ext i
  fin_cases i <;> simp [starSlice, e1, e2, PiLp.smul_apply]

/-- Shifting the parameter by `period` shifts the angle by `period`. -/
lemma starAngle_shift {psi : ℝ → ℝ}
    (hshift : ∀ t : ℝ, psi (t + period) = psi t + period) (s t : ℝ) :
    starAngle psi s (t + period) = starAngle psi s t + period := by
  simp only [starAngle]
  rw [hshift t]
  ring

/-- The interpolated angle is strictly increasing for `0 ≤ s ≤ 1` when `psi` is. -/
lemma starAngle_strictMono {psi : ℝ → ℝ} (hψ : StrictMono psi) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : StrictMono (starAngle psi s) := by
  intro t t' htt'
  have h1 : 0 < psi t' - psi t := sub_pos.mpr (hψ htt')
  have h2 : 0 < t' - t := sub_pos.mpr htt'
  rcases lt_or_eq_of_le hs1 with hs | hs
  · have h3 : 0 < 1 - s := sub_pos.mpr hs
    simp only [starAngle]
    nlinarith [mul_pos h3 h1, mul_nonneg hs0 (le_of_lt h2)]
  · subst hs
    simp [starAngle]
    exact htt'

/-- The interpolated radius stays positive for `0 ≤ s ≤ 1`. -/
lemma starRad_pos {lam : ℝ → ℝ} (hpos : ∀ t : ℝ, 0 < lam t) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) : 0 < starRad lam s t := by
  simp only [starRad]
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; simpa using hpos t
  · have : 0 ≤ (1 - s) * lam t := mul_nonneg (by linarith) (le_of_lt (hpos t))
    linarith

/-- The interpolated radius is `period`-periodic. -/
lemma starRad_periodic {lam : ℝ → ℝ} (hper : Function.Periodic lam period) (s : ℝ) :
    Function.Periodic (starRad lam s) period := by
  intro t
  simp only [starRad]
  rw [hper t]

lemma starCosAddPeriod (x : ℝ) : Real.cos (x + period) = Real.cos x := by
  rw [show period = 2 * Real.pi from rfl, Real.cos_add_two_pi]

lemma starSinAddPeriod (x : ℝ) : Real.sin (x + period) = Real.sin x := by
  rw [show period = 2 * Real.pi from rfl, Real.sin_add_two_pi]

/-- Every slice of the family is `period`-periodic. -/
lemma starSlice_periodic {lam psi : ℝ → ℝ} (hper : Function.Periodic lam period)
    (hshift : ∀ t : ℝ, psi (t + period) = psi t + period) (s : ℝ) :
    Function.Periodic (fun t : ℝ => starSlice lam psi s t) period := by
  intro t
  have ha := starAngle_shift hshift s t
  have hr := starRad_periodic hper s t
  show starSlice lam psi s (t + period) = starSlice lam psi s t
  simp only [starSlice]
  rw [ha, hr, starCosAddPeriod, starSinAddPeriod]

/-- Two angles with equal cosine and sine, differing by less than `2π` in
absolute value, are equal. -/
lemma star_angle_eq_of_cos_sin_eq {a b : ℝ} (h : |b - a| < 2 * Real.pi)
    (hc : Real.cos a = Real.cos b) (hs : Real.sin a = Real.sin b) : a = b := by
  have hcos1 : Real.cos (b - a) = 1 := by
    rw [Real.cos_sub, ← hc, ← hs]
    nlinarith [Real.sin_sq_add_cos_sq a]
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hcos1
  linarith

/-- Two angles attached to parameters in `[0, period)` differ by less than the
period in absolute value. -/
lemma starAngle_sub_abs_lt {psi : ℝ → ℝ} (hψ : StrictMono psi)
    (hshift : ∀ t : ℝ, psi (t + period) = psi t + period) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {t t' : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) period) (ht' : t' ∈ Set.Ico (0 : ℝ) period) :
    |starAngle psi s t' - starAngle psi s t| < period := by
  have hmono := starAngle_strictMono hψ hs0 hs1
  rcases le_total t t' with h | h
  · have h1 : starAngle psi s t ≤ starAngle psi s t' := hmono.monotone h
    have h2 : t' < t + period := by linarith [ht.1, ht'.2]
    have h3 := hmono h2
    rw [starAngle_shift hshift s t] at h3
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have h1 : starAngle psi s t' ≤ starAngle psi s t := hmono.monotone h
    have h2 : t < t' + period := by linarith [ht'.1, ht.2]
    have h3 := hmono h2
    rw [starAngle_shift hshift s t'] at h3
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The star-shaped slices are injective on one period**: equal slice values
force equal positive radii and equal angles modulo `2π`; two angles coming from
`[0, period)` differ by strictly less than `2π`, hence are equal. -/
theorem injOn_starSlice {lam psi : ℝ → ℝ}
    (hlampos : ∀ t : ℝ, 0 < lam t) (hψ : StrictMono psi)
    (hshift : ∀ t : ℝ, psi (t + period) = psi t + period) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Set.InjOn (fun t : ℝ => starSlice lam psi s t) (Set.Ico (0 : ℝ) period) := by
  intro t ht t' ht' heq
  have hpos : ∀ u : ℝ, 0 < starRad lam s u := fun u => starRad_pos hlampos hs0 hs1 u
  have hx : starRad lam s t * Real.cos (starAngle psi s t)
      = starRad lam s t' * Real.cos (starAngle psi s t') := by
    have := congrArg (fun v : Space => v.ofLp 0) heq
    simpa [starSlice] using this
  have hy : starRad lam s t * Real.sin (starAngle psi s t)
      = starRad lam s t' * Real.sin (starAngle psi s t') := by
    have := congrArg (fun v : Space => v.ofLp 1) heq
    simpa [starSlice] using this
  have hx2 : (starRad lam s t * Real.cos (starAngle psi s t)) ^ 2
      = (starRad lam s t' * Real.cos (starAngle psi s t')) ^ 2 := by rw [hx]
  have hy2 : (starRad lam s t * Real.sin (starAngle psi s t)) ^ 2
      = (starRad lam s t' * Real.sin (starAngle psi s t')) ^ 2 := by rw [hy]
  have hsq : (starRad lam s t) ^ 2 = (starRad lam s t') ^ 2 := by
    nlinarith [hx2, hy2, Real.sin_sq_add_cos_sq (starAngle psi s t),
      Real.sin_sq_add_cos_sq (starAngle psi s t')]
  have hr : starRad lam s t = starRad lam s t' := by
    nlinarith [hpos t, hpos t', hsq]
  have hc : Real.cos (starAngle psi s t) = Real.cos (starAngle psi s t') := by
    rw [hr] at hx
    exact mul_left_cancel₀ (ne_of_gt (hpos t')) hx
  have hsn : Real.sin (starAngle psi s t) = Real.sin (starAngle psi s t') := by
    rw [hr] at hy
    exact mul_left_cancel₀ (ne_of_gt (hpos t')) hy
  have hb := starAngle_sub_abs_lt hψ hshift hs0 hs1 ht ht'
  rw [show period = 2 * Real.pi from rfl] at hb
  exact (starAngle_strictMono hψ hs0 hs1).injective (star_angle_eq_of_cos_sin_eq hb hc hsn)

/-- **The star-shaped slices are everywhere regular**: the derivative of the
slice at `t` is `ρ • (θ' • v) + ρ' • u` where `u` and `v` are the unit circle
point and its unit tangent at the angle `θ t`; pairing with `u` resp. `v` gives
`ρ'` resp. `ρ * θ'`, and `ρ * θ' > 0` because both factors are positive. -/
theorem velocity_starSlice_ne_zero {lam psi : ℝ → ℝ} {s t : ℝ}
    (hlam : DifferentiableAt ℝ lam t) (hpsi : DifferentiableAt ℝ psi t)
    (hlampos : 0 < lam t) (hpsid : 0 < deriv psi t) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    velocity (fun u : ℝ => starSlice lam psi s u) t ≠ 0 := by
  have hρpos : 0 < starRad lam s t := by
    simp only [starRad]
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; simpa using hlampos
    · have : 0 ≤ (1 - s) * lam t := mul_nonneg (by linarith) (le_of_lt hlampos)
      linarith
  have hdθpos : 0 < (1 - s) * deriv psi t + s := by
    rcases lt_or_eq_of_le hs1 with h | h
    · have h3 : 0 < 1 - s := sub_pos.mpr h
      have := mul_pos h3 hpsid
      linarith
    · subst h; ring_nf; norm_num
  have hρ : HasDerivAt (starRad lam s) ((1 - s) * deriv lam t) t :=
    (hlam.hasDerivAt.const_mul (1 - s)).add_const s
  have hθ : HasDerivAt (starAngle psi s) ((1 - s) * deriv psi t + s) t := by
    change HasDerivAt (fun u : ℝ => (1 - s) * psi u + s * u) ((1 - s) * deriv psi t + s) t
    have h1 : HasDerivAt (fun u : ℝ => (1 - s) * psi u) ((1 - s) * deriv psi t) t :=
      hpsi.hasDerivAt.const_mul (1 - s)
    have h2 : HasDerivAt (fun u : ℝ => s * u) s t := by
      simpa using (hasDerivAt_id t).const_mul s
    exact h1.add h2
  have hcc : HasDerivAt (fun u : ℝ => Real.cos (starAngle psi s u))
      (-Real.sin (starAngle psi s t) * ((1 - s) * deriv psi t + s)) t :=
    (Real.hasDerivAt_cos _).comp t hθ
  have hcs : HasDerivAt (fun u : ℝ => Real.sin (starAngle psi s u))
      (Real.cos (starAngle psi s t) * ((1 - s) * deriv psi t + s)) t :=
    (Real.hasDerivAt_sin _).comp t hθ
  have hv : HasDerivAt
      (fun u : ℝ => Real.cos (starAngle psi s u) • e1 + Real.sin (starAngle psi s u) • e2)
      ((-Real.sin (starAngle psi s t) * ((1 - s) * deriv psi t + s)) • e1
        + (Real.cos (starAngle psi s t) * ((1 - s) * deriv psi t + s)) • e2) t :=
    (hcc.smul_const e1).add (hcs.smul_const e2)
  have hV : HasDerivAt
      (fun u : ℝ => starRad lam s u •
        (Real.cos (starAngle psi s u) • e1 + Real.sin (starAngle psi s u) • e2))
      (starRad lam s t •
        ((-Real.sin (starAngle psi s t) * ((1 - s) * deriv psi t + s)) • e1
          + (Real.cos (starAngle psi s t) * ((1 - s) * deriv psi t + s)) • e2)
        + ((1 - s) * deriv lam t) •
          (Real.cos (starAngle psi s t) • e1 + Real.sin (starAngle psi s t) • e2)) t :=
    hρ.smul hv
  have hfun : (fun u : ℝ => starSlice lam psi s u)
      = (fun u : ℝ => starRad lam s u •
          (Real.cos (starAngle psi s u) • e1 + Real.sin (starAngle psi s u) • e2)) := by
    funext u
    exact starSlice_eq_vec lam psi s u
  rw [hfun, velocity, hV.deriv]
  intro hzero
  have h0 : starRad lam s t * (-Real.sin (starAngle psi s t) * ((1 - s) * deriv psi t + s))
      + ((1 - s) * deriv lam t) * Real.cos (starAngle psi s t) = 0 := by
    have := congrArg (fun v : Space => v.ofLp 0) hzero
    simpa [e1, e2, PiLp.add_apply, PiLp.smul_apply] using this
  have h1 : starRad lam s t * (Real.cos (starAngle psi s t) * ((1 - s) * deriv psi t + s))
      + ((1 - s) * deriv lam t) * Real.sin (starAngle psi s t) = 0 := by
    have := congrArg (fun v : Space => v.ofLp 1) hzero
    simpa [e1, e2, PiLp.add_apply, PiLp.smul_apply] using this
  have hkey : starRad lam s t * ((1 - s) * deriv psi t + s) *
      (Real.sin (starAngle psi s t) ^ 2 + Real.cos (starAngle psi s t) ^ 2) = 0 := by
    linear_combination (-Real.sin (starAngle psi s t)) * h0 + Real.cos (starAngle psi s t) * h1
  have hρdθ0 : starRad lam s t * ((1 - s) * deriv psi t + s) = 0 := by
    rw [Real.sin_sq_add_cos_sq] at hkey
    simpa using hkey
  have : 0 < starRad lam s t * ((1 - s) * deriv psi t + s) := mul_pos hρpos hdθpos
  linarith [hρdθ0, this]

/-- **The star-shaped family is jointly analytic** in `(t, s)`. -/
theorem contDiff_starSliceFamily {lam psi : ℝ → ℝ} (hlam : ContDiff ℝ ⊤ lam)
    (hpsi : ContDiff ℝ ⊤ psi) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => starSlice lam psi p.2 p.1) := by
  have hr : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => starRad lam p.2 p.1) :=
    ((contDiff_const.sub contDiff_snd).mul (hlam.comp contDiff_fst)).add contDiff_snd
  have ha : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => starAngle psi p.2 p.1) :=
    ((contDiff_const.sub contDiff_snd).mul (hpsi.comp contDiff_fst)).add
      (contDiff_snd.mul contDiff_fst)
  have hcos : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => starRad lam p.2 p.1 * Real.cos (starAngle psi p.2 p.1)) :=
    hr.mul (Real.contDiff_cos.comp ha)
  have hsin : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => starRad lam p.2 p.1 * Real.sin (starAngle psi p.2 p.1)) :=
    hr.mul (Real.contDiff_sin.comp ha)
  have h := contDiff_vec3 hcos hsin
    (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℝ)))
  have hfun : (fun p : ℝ × ℝ => (!₂[starRad lam p.2 p.1 * Real.cos (starAngle psi p.2 p.1),
      starRad lam p.2 p.1 * Real.sin (starAngle psi p.2 p.1), (0 : ℝ)] : Space))
      = (fun p : ℝ × ℝ => starSlice lam psi p.2 p.1) := by
    funext p
    rfl
  rwa [hfun] at h

theorem isUnknotted_of_starShapedPolarGraph {lam psi : ℝ → ℝ}
    (c : LeanEval.KnotTheory.Quadrisecant.Space)
    (hlam : ContDiff ℝ ⊤ lam)
    (hlamper : Function.Periodic lam LeanEval.KnotTheory.Quadrisecant.period)
    (hlampos : ∀ t : ℝ, 0 < lam t)
    (hpsi : ContDiff ℝ ⊤ psi)
    (hpsishift : ∀ t : ℝ, psi (t + LeanEval.KnotTheory.Quadrisecant.period)
      = psi t + LeanEval.KnotTheory.Quadrisecant.period)
    (hpsideriv : ∀ t : ℝ, 0 < deriv psi t) :
    LeanEval.KnotTheory.Quadrisecant.IsUnknotted
      (fun t : ℝ => c + lam t • (!₂[Real.cos (psi t), Real.sin (psi t), (0 : ℝ)])) := by
  have hψmono : StrictMono psi := strictMono_of_deriv_pos hpsideriv
  have hmain : IsUnknotted
      (fun t : ℝ => !₂[lam t * Real.cos (psi t), lam t * Real.sin (psi t), (0 : ℝ)]) := by
    refine ⟨fun t s => starSlice lam psi s t, contDiff_starSliceFamily hlam hpsi, ?_, ?_, ?_⟩
    · intro t
      exact starSlice_zero lam psi t
    · intro t
      exact starSlice_one lam psi t
    · intro s hs
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (contDiff_starSliceFamily hlam hpsi).comp (contDiff_id.prodMk contDiff_const)
      · exact starSlice_periodic hlamper hpsishift s
      · exact injOn_starSlice hlampos hψmono hpsishift hs.1 hs.2
      · intro t
        exact velocity_starSlice_ne_zero (hlam.differentiable (by simp)).differentiableAt
          (hpsi.differentiable (by simp)).differentiableAt (hlampos t) (hpsideriv t) hs.1 hs.2
  have htr : IsUnknotted
      (fun t : ℝ => c + !₂[lam t * Real.cos (psi t), lam t * Real.sin (psi t), (0 : ℝ)]) :=
    isUnknotted_constAdd c hmain
  have hfun : (fun t : ℝ => c + lam t • (!₂[Real.cos (psi t), Real.sin (psi t), (0 : ℝ)]))
      = (fun t : ℝ => c + !₂[lam t * Real.cos (psi t), lam t * Real.sin (psi t), (0 : ℝ)]) := by
    funext t
    congr 1
    ext i
    fin_cases i <;> simp [PiLp.smul_apply]
  rw [hfun]
  exact htr

end Work.Drive
