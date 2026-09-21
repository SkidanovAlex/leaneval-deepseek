import Mathlib
import Submission.Work.OddVolterra.Free.free_slope_api

namespace Work.OddVolterra.Free

open Set Filter
open scoped Topology ContDiff

noncomputable section

variable {h x y : ℝ → ℝ}

/-! ## The two curve maps of a free-tip envelope curve

The free-tip analogue of `Work.OddEnvelope.IsEnvelopeBranch.strictMonoOn_curve`: the two curve
maps `σ ↦ σ * y σ + h σ` and `σ ↦ σ * x σ - h σ` are strictly increasing on `(0,∞)` (from the
`mono_*` fields of `IsEnvelopeCurveFree`) and strictly positive there (comparing with a small
slope below `1 - 2τ`, where the bump vanishes and the curve is positive). -/

/-- The right-branch curve map `σ ↦ σ * y σ + h σ` is strictly increasing on `(0,∞)`. -/
theorem envCurveRight_strictMonoOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    StrictMonoOn (fun σ : ℝ => σ * y σ + h σ) (Set.Ioi 0) := by
  have hderiv : ∀ s : ℝ, 0 < s →
      deriv (fun σ : ℝ => σ * y σ + h σ) s = y s + s * deriv y s + deriv h s := by
    intro s hs
    have hys := H.smooth_y.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hhs := H.smooth_h.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hd : HasDerivAt (fun σ : ℝ => σ * y σ + h σ)
        (1 * y s + s * deriv y s + deriv h s) s :=
      ((hasDerivAt_id s).mul (hys.differentiableAt (by simp)).hasDerivAt).add
        (hhs.differentiableAt (by simp)).hasDerivAt
    simpa [one_mul] using hd.deriv
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact (continuousOn_id.mul H.smooth_y.continuousOn).add H.smooth_h.continuousOn
  · intro s hs
    rw [interior_Ioi] at hs
    rw [hderiv s hs]
    exact H.mono_y s hs

/-- The left-branch curve map `σ ↦ σ * x σ - h σ` is strictly increasing on `(0,∞)`. -/
theorem envCurveLeft_strictMonoOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    StrictMonoOn (fun σ : ℝ => σ * x σ - h σ) (Set.Ioi 0) := by
  have hderiv : ∀ s : ℝ, 0 < s →
      deriv (fun σ : ℝ => σ * x σ - h σ) s = x s + s * deriv x s - deriv h s := by
    intro s hs
    have hxs := H.smooth_x.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hhs := H.smooth_h.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hd : HasDerivAt (fun σ : ℝ => σ * x σ - h σ)
        (1 * x s + s * deriv x s - deriv h s) s :=
      ((hasDerivAt_id s).mul (hxs.differentiableAt (by simp)).hasDerivAt).sub
        (hhs.differentiableAt (by simp)).hasDerivAt
    simpa [one_mul] using hd.deriv
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact (continuousOn_id.mul H.smooth_x.continuousOn).sub H.smooth_h.continuousOn
  · intro s hs
    rw [interior_Ioi] at hs
    rw [hderiv s hs]
    exact H.mono_x s hs

/-- The right-branch curve map is strictly positive on `(0,∞)`: below `1 - 2τ` the bump vanishes,
so there it equals `σ * y σ > 0`, and it is increasing. -/
theorem envCurveRight_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {σ : ℝ}
    (hσ : 0 < σ) : 0 < σ * y σ + h σ := by
  have h2τ : (0 : ℝ) < 1 - 2 * Work.OddCurve.tau := by
    rw [Work.OddCurve.one_sub_two_tau_eq]; norm_num
  have hmin : (0 : ℝ) < min σ (1 - 2 * Work.OddCurve.tau) := lt_min hσ h2τ
  obtain ⟨σ', hσ'pos, hσ'lt⟩ :
      ∃ σ' : ℝ, 0 < σ' ∧ σ' < min σ (1 - 2 * Work.OddCurve.tau) :=
    ⟨min σ (1 - 2 * Work.OddCurve.tau) / 2, by linarith, by linarith⟩
  have hle : σ' < σ := lt_of_lt_of_le hσ'lt (min_le_left _ _)
  have hle2 : σ' < 1 - 2 * Work.OddCurve.tau := lt_of_lt_of_le hσ'lt (min_le_right _ _)
  have hzero : h σ' = 0 := by
    by_contra hne
    have hmem := H.h_support (Function.mem_support.mpr hne)
    linarith [hmem.1, hle2]
  have hpos' : 0 < σ' * y σ' := mul_pos hσ'pos (H.pos_y hσ'pos)
  have hmono : σ' * y σ' + h σ' < σ * y σ + h σ := envCurveRight_strictMonoOn H hσ'pos hσ hle
  rw [hzero, add_zero] at hmono
  linarith

/-- The left-branch curve map is strictly positive on `(0,∞)`. -/
theorem envCurveLeft_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {σ : ℝ}
    (hσ : 0 < σ) : 0 < σ * x σ - h σ := by
  have h2τ : (0 : ℝ) < 1 - 2 * Work.OddCurve.tau := by
    rw [Work.OddCurve.one_sub_two_tau_eq]; norm_num
  have hmin : (0 : ℝ) < min σ (1 - 2 * Work.OddCurve.tau) := lt_min hσ h2τ
  obtain ⟨σ', hσ'pos, hσ'lt⟩ :
      ∃ σ' : ℝ, 0 < σ' ∧ σ' < min σ (1 - 2 * Work.OddCurve.tau) :=
    ⟨min σ (1 - 2 * Work.OddCurve.tau) / 2, by linarith, by linarith⟩
  have hle : σ' < σ := lt_of_lt_of_le hσ'lt (min_le_left _ _)
  have hle2 : σ' < 1 - 2 * Work.OddCurve.tau := lt_of_lt_of_le hσ'lt (min_le_right _ _)
  have hzero : h σ' = 0 := by
    by_contra hne
    have hmem := H.h_support (Function.mem_support.mpr hne)
    linarith [hmem.1, hle2]
  have hpos' : 0 < σ' * x σ' := mul_pos hσ'pos (H.pos_x hσ'pos)
  have hmono : σ' * x σ' - h σ' < σ * x σ - h σ := envCurveLeft_strictMonoOn H hσ'pos hσ hle
  rw [hzero, sub_zero] at hmono
  linarith

/-- **`rad ≤ 0` outside the cut section, free tips.**  Free-tip analogue of
`Work.OddCurve.rad_nonpos_outside`.  For a free-tip envelope curve and slopes `0 < c ≤ u`, the
radicand `rad h (envProfileFree h x y) u t` is non-positive on the two pieces of the fixed
interval `[-(x c), y c]` lying outside the cut section `[-(x u), y u]`.

Ingredients (all from `Work.OddVolterra.Free.free_slope_api`, `Submission.Work.OddCurve.Free`
and `Submission.Work.OddVolterra.Free.Defs`): `Work.OddCurve.Free.IsEnvelopeCurveFree.exists_slope_y`,
`...slopeRight_eq_of`, `...pos_y` (and the `x` analogues) give, for `t ∈ (0, y c]`, the unique
slope `σ ≥ c` with `y σ = t`; then `envProfileFree h x y t = envelopeRight h y t = σ * y σ + h σ`
and the map `σ ↦ σ * y σ + h σ` is strictly increasing on `(0,∞)` by `H.mono_y` (after showing it
is continuous there), and strictly positive on `(0,∞)` (`H.mono_y` compared at a small slope where
`h = 0` by `H.h_support` and `y > 0` by `pos_y`; the limit `y σ → b > 0` at `0⁺` makes the base
point positive).  Hence on `[y u, y c]` the profile lies between `0` and `u * y u + h u ≤ u * t + h u`.
The left band is the same with `x`, `H.mono_x` and the identities `envelopeLeft h x t =
envelopeRight (negH h) x (-t)`, `envProfileFree h x y t = envelopeLeft h x t` for `t < 0`.

State it inside `namespace Work.OddVolterra.Free`. -/
theorem rad_nonpos_outside_free {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c u : ℝ} (hc : 0 < c) (hcu : c ≤ u) :
    (∀ t : ℝ, y u ≤ t → t ≤ y c →
      Work.OddCurve.rad h (Work.OddVolterra.Free.envProfileFree h x y) u t ≤ 0) ∧
    (∀ t : ℝ, -(x c) ≤ t → t ≤ -(x u) →
      Work.OddCurve.rad h (Work.OddVolterra.Free.envProfileFree h x y) u t ≤ 0) := by
  have hu : 0 < u := lt_of_lt_of_le hc hcu
  constructor
  · -- the right band `[y u, y c]`
    intro t htu htc
    have ht : 0 < t := lt_of_lt_of_le (H.pos_y hu) htu
    -- the realising slope `σ ∈ [c, u]` of `t`
    obtain ⟨σ, _hcσ, hσpos, hyσ⟩ := H.exists_slope_y hc ht htc
    have hslope : Work.OddEnvelope.slopeRight y t = σ := H.slopeRight_eq_of hσpos hyσ
    have hσu : σ ≤ u := by
      by_contra hcon
      have hlt : u < σ := lt_of_not_ge hcon
      have h' := H.strictAntiOn_y hu hσpos hlt
      rw [hyσ] at h'
      linarith
    have hval : envProfileFree h x y t = σ * y σ + h σ := by
      rw [envProfileFree, if_pos ht, Work.OddEnvelope.envelopeRight, hslope, hyσ]
    have hchain : σ * y σ + h σ ≤ u * t + h u := by
      have h1 := (envCurveRight_strictMonoOn H).monotoneOn hσpos hu hσu
      have h2 : u * y u ≤ u * t := mul_le_mul_of_nonneg_left htu hu.le
      linarith
    have hnn : 0 ≤ σ * y σ + h σ := (envCurveRight_pos H hσpos).le
    rw [Work.OddCurve.rad_def, hval]
    have hsq : (σ * y σ + h σ) ^ 2 ≤ (u * t + h u) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hnn hchain
    linarith
  · -- the left band `[-(x c), -(x u)]`
    intro t htc' htu'
    have hxu : 0 < x u := H.pos_x hu
    have htneg : t < 0 := by linarith
    have hnegt : 0 < -t := by linarith
    have htlec : -t ≤ x c := by linarith
    obtain ⟨σ, _hcσ, hσpos, hxσ⟩ := H.exists_slope_x hc hnegt htlec
    have hslope : Work.OddEnvelope.slopeLeft x t = σ := H.slopeLeft_eq_of hσpos hxσ
    have hσu : σ ≤ u := by
      by_contra hcon
      have hlt : u < σ := lt_of_not_ge hcon
      have h' := H.strictAntiOn_x hu hσpos hlt
      rw [hxσ] at h'
      linarith
    have hval : envProfileFree h x y t = σ * x σ - h σ := by
      rw [envProfileFree, if_neg (not_lt.mpr htneg.le), if_pos htneg,
        Work.OddEnvelope.envelopeLeft, hslope]
      have ht_eq : t = -x σ := by linarith
      rw [ht_eq]; ring
    have hGpos : 0 < σ * x σ - h σ := envCurveLeft_pos H hσpos
    have hGle : σ * x σ - h σ ≤ u * x u - h u :=
      (envCurveLeft_strictMonoOn H).monotoneOn hσpos hu hσu
    have hB : u * t + h u ≤ -(u * x u - h u) := by
      have h1 : u * t ≤ u * (-(x u)) := mul_le_mul_of_nonneg_left htu' hu.le
      linarith
    have hA : σ * x σ - h σ ≤ -(u * t + h u) := by linarith
    rw [Work.OddCurve.rad_def, hval]
    have hsq : (σ * x σ - h σ) ^ 2 ≤ (u * t + h u) ^ 2 := by
      have he : (u * t + h u) ^ 2 = (-(u * t + h u)) ^ 2 := by ring
      rw [he]
      exact pow_le_pow_left₀ hGpos.le hA 2
    linarith

end

end Work.OddVolterra.Free
