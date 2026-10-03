import Mathlib

/-!
# Exponential decay of a `1`-periodic holomorphic function on a half-plane

Let `ψ : ℂ → ℂ` be holomorphic on the half-plane `{w | y < im w}`, `1`-periodic there, bounded
by `M` there, and tending to `0` as `im w → +∞`.  Then `ψ` decays at least as fast as the
`q`-parameter: `‖ψ z‖ ≤ M · exp (-2π (im z - y))` for every `z` in the half-plane.

The proof is the classical one.  Push `ψ` to the punctured disc `{q | 0 < ‖q‖ < exp (-2πy)}`
by the `q`-parameter `q = exp (2πi w)`: because `ψ` is `1`-periodic, it descends to a function
`φ` (Mathlib's `Function.Periodic.cuspFunction`).  `φ` is holomorphic on the punctured disc
(`cusp_diff`, proved here by pushing the local periodicity up to a *global* periodicity with
`pushU` and applying Mathlib's `differentiableAt_cuspFunction`), bounded by `M` there, and
`lim_{q→0} φ q = 0` because `ψ → 0` at `+i∞`.  Riemann's removable singularity theorem then
makes `φ` holomorphic at `0` with `φ 0 = 0`, so the Schwarz lemma on the disc of radius `ρ`
gives `‖φ q‖ ≤ M/ρ · ‖q‖`, which is the claim.
-/

namespace Work.L62

open Complex Filter
open scoped Topology

/-! ## Pushing a half-plane function up to a globally periodic one -/

/-- `pushU Y` replaces the imaginary part of `w` by `max Y (im w)`; it keeps the real part.
It is *not* holomorphic, but it is `1`-periodic and agrees with the identity above height `Y`. -/
private def pushU (Y : ℝ) (w : ℂ) : ℂ := w.re + (max Y w.im) * Complex.I

private lemma pushU_im (Y : ℝ) (w : ℂ) : (pushU Y w).im = max Y w.im := by
  simp [pushU]

private lemma pushU_eq_self (Y : ℝ) {w : ℂ} (h : Y ≤ w.im) : pushU Y w = w := by
  simp only [pushU, max_eq_right h, Complex.re_add_im]

private lemma pushU_add_one (Y : ℝ) (w : ℂ) : pushU Y (w + 1) = pushU Y w + 1 := by
  simp only [pushU, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  apply Complex.ext <;> simp

/-- The `q`-parameter inverse of a point of the disc of radius `exp (-2πy)` lies in the
half-plane `{im > y}`. -/
private lemma im_invQParam_gt {q : ℂ} {y : ℝ} (hq0 : 0 < ‖q‖)
    (hqρ : ‖q‖ < Real.exp (-2 * Real.pi * y)) :
    y < (Function.Periodic.invQParam 1 q).im := by
  have hlog : Real.log ‖q‖ < -2 * Real.pi * y := by
    have h := Real.log_lt_log hq0 hqρ
    rwa [Real.log_exp] at h
  have h2 : (0:ℝ) < 2 * Real.pi := by positivity
  have hmul : y < -(Real.log ‖q‖) / (2 * Real.pi) := by
    rw [lt_div_iff₀ h2]; nlinarith [hlog]
  rw [Function.Periodic.im_invQParam]
  calc y < -(Real.log ‖q‖) / (2 * Real.pi) := hmul
    _ = -1 / (2 * Real.pi) * Real.log ‖q‖ := by ring

/-! ## Holomorphy of the `q`-expansion on the punctured disc -/

/-- The `q`-expansion (cusp function) of a `1`-periodic function holomorphic on the half-plane
`{w | y < im w}` is holomorphic on the punctured disc `{q | 0 < ‖q‖ < exp (-2πy)}`. -/
private theorem cusp_diff {ψ : ℂ → ℂ} {y : ℝ}
    (hhol : DifferentiableOn ℂ ψ {w : ℂ | y < Complex.im w})
    (hper : ∀ w : ℂ, y < Complex.im w → ψ (w + 1) = ψ w) :
    ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < Real.exp (-2 * Real.pi * y) →
      DifferentiableAt ℂ (Function.Periodic.cuspFunction (1 : ℝ) ψ) q := by
  intro q hq0 hqρ
  have hqne : q ≠ 0 := norm_pos_iff.mp hq0
  set z : ℂ := Function.Periodic.invQParam 1 q with hzdef
  have hzim : y < z.im := im_invQParam_gt hq0 hqρ
  -- a level strictly between `y` and `im z`, used to make `ψ` globally periodic
  obtain ⟨Y, hYy, hYz⟩ := exists_between hzim
  set Ψ : ℂ → ℂ := fun w => ψ (pushU Y w) with hΨdef
  have hΨper : Function.Periodic Ψ (1 : ℝ) := by
    intro w
    show ψ (pushU Y (w + ((1:ℝ):ℂ))) = ψ (pushU Y w)
    rw [show w + ((1:ℝ):ℂ) = w + 1 by norm_num, pushU_add_one]
    exact hper _ (by rw [pushU_im]; exact lt_of_lt_of_le hYy (le_max_left Y w.im))
  have hΨhol : DifferentiableAt ℂ Ψ z := by
    have hψz : DifferentiableAt ℂ ψ z :=
      hhol.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzim)
    refine hψz.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hYz] with w hw
    simp only [hΨdef]
    rw [pushU_eq_self Y (le_of_lt hw)]
  have key := Function.Periodic.differentiableAt_cuspFunction (h := (1:ℝ)) (f := Ψ)
    one_ne_zero hΨper hΨhol
  rw [Function.Periodic.qParam_right_inv one_ne_zero hqne] at key
  refine key.congr_of_eventuallyEq ?_
  -- `cuspFunction 1 Ψ` and `cuspFunction 1 ψ` agree near `q`
  have hcontim : ContinuousAt (fun q' : ℂ => (Function.Periodic.invQParam 1 q').im) q := by
    have h1 : (fun q' : ℂ => (Function.Periodic.invQParam 1 q').im)
        = fun q' : ℂ => -1 / (2*Real.pi) * Real.log ‖q'‖ := by
      funext q'; rw [Function.Periodic.im_invQParam]
    rw [h1]
    exact ((continuous_norm.continuousAt.log hq0.ne').const_mul _)
  have hEv : ∀ᶠ q' in 𝓝 q, Y < (Function.Periodic.invQParam 1 q').im :=
    hcontim.preimage_mem_nhds ((isOpen_lt continuous_const continuous_id).mem_nhds hYz)
  filter_upwards [hEv, isOpen_ne.mem_nhds hqne] with q' hq'im hq'ne
  rw [Function.Periodic.cuspFunction_eq_of_nonzero 1 ψ hq'ne,
      Function.Periodic.cuspFunction_eq_of_nonzero 1 Ψ hq'ne]
  simp only [hΨdef]
  rw [pushU_eq_self Y (le_of_lt hq'im)]

/-! ## Periodicity extends to all integer multiples -/

private lemma psi_int_period {ψ : ℂ → ℂ} {y : ℝ}
    (hper : ∀ w : ℂ, y < Complex.im w → ψ (w + 1) = ψ w) :
    ∀ m : ℤ, ∀ w : ℂ, y < Complex.im w → ψ (w + m) = ψ w := by
  have hnat : ∀ k : ℕ, ∀ v : ℂ, y < v.im → ψ (v + k) = ψ v := by
    intro k
    induction k with
    | zero => intro v hv; simp
    | succ k ih =>
        intro v hv
        have hk : y < (v + k).im := by rw [Complex.add_im, Complex.natCast_im, add_zero]; exact hv
        rw [Nat.cast_succ, ← add_assoc, hper (v + k) hk]
        exact ih v hv
  intro m w hw
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
  · subst hk; exact hnat k w hw
  · subst hk
    have h := hnat k (w + ((-(k:ℤ) : ℤ) : ℂ))
      (by rw [Complex.add_im, Complex.intCast_im, add_zero]; exact hw)
    rw [show (w + ((-(k:ℤ) : ℤ) : ℂ)) + (k:ℂ) = w by push_cast; ring] at h
    exact h.symm

/-! ## The main estimate -/

theorem periodic_decay_up {ψ : ℂ → ℂ} {y M : ℝ} (hM : 0 ≤ M)
    (hhol : DifferentiableOn ℂ ψ {w : ℂ | y < Complex.im w})
    (hper : ∀ w : ℂ, y < Complex.im w → ψ (w + 1) = ψ w)
    (hbd : ∀ w : ℂ, y < Complex.im w → ‖ψ w‖ ≤ M)
    (hlim : Filter.Tendsto ψ (Filter.comap Complex.im Filter.atTop) (nhds 0)) :
    ∀ z : ℂ, y < Complex.im z → ‖ψ z‖ ≤ M * Real.exp (-2 * Real.pi * (Complex.im z - y)) := by
  set ρ : ℝ := Real.exp (-2 * Real.pi * y) with hρdef
  have hρpos : 0 < ρ := Real.exp_pos _
  set φ : ℂ → ℂ := Function.Periodic.cuspFunction (1:ℝ) ψ with hφdef
  -- `φ` is bounded by `M` on the punctured disc
  have hφbd : ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → ‖φ q‖ ≤ M := by
    intro q hq hqρ
    rw [hφdef, Function.Periodic.cuspFunction_eq_of_nonzero 1 ψ hq]
    exact hbd _ (im_invQParam_gt (norm_pos_iff.mpr hq) hqρ)
  -- `φ 0 = 0`, because `ψ → 0` at `+i∞`
  have hφ0 : φ 0 = 0 := by
    have htend : Filter.Tendsto (fun q : ℂ => ψ (Function.Periodic.invQParam 1 q))
        (𝓝[≠] (0:ℂ)) (𝓝 0) :=
      hlim.comp (Function.Periodic.invQParam_tendsto (h := (1:ℝ)) one_pos)
    have h_eq : φ 0 = limUnder (𝓝[≠] (0:ℂ))
        (fun q : ℂ => ψ (Function.Periodic.invQParam 1 q)) := by
      simp only [hφdef, Function.Periodic.cuspFunction, Function.update_self, Function.comp_def]
    rw [h_eq, htend.limUnder_eq]
  -- `φ` is continuous at `0`
  have hφcont : ContinuousAt φ 0 := by
    rw [continuousAt_iff_punctured_nhds, hφ0]
    have h1 : Filter.Tendsto (fun q : ℂ => ψ (Function.Periodic.invQParam 1 q))
        (𝓝[≠] (0:ℂ)) (𝓝 0) :=
      hlim.comp (Function.Periodic.invQParam_tendsto (h := (1:ℝ)) one_pos)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [hφdef, Function.Periodic.cuspFunction_eq_of_nonzero 1 ψ hq]
  -- `φ` is holomorphic on the punctured disc, hence (Riemann) on the whole disc
  have hφdiff : ∀ᶠ q : ℂ in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ φ q := by
    have hball : ∀ᶠ q : ℂ in 𝓝[≠] (0:ℂ), ‖q‖ < ρ := by
      refine Filter.Eventually.filter_mono inf_le_left ?_
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) hρpos] with q hq
      rwa [Metric.mem_ball, dist_zero_right] at hq
    filter_upwards [self_mem_nhdsWithin, hball] with q hq hqρ
    rw [hφdef]
    exact cusp_diff hhol hper q (norm_pos_iff.mpr hq) hqρ
  have hφana : AnalyticAt ℂ φ 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hφdiff hφcont
  have hφdiff0 : DifferentiableAt ℂ φ 0 := hφana.differentiableAt
  have hφDiffOn : DifferentiableOn ℂ φ (Metric.ball 0 ρ) := by
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    rcases eq_or_ne q 0 with rfl | hne
    · exact hφdiff0.differentiableWithinAt
    · rw [hφdef]
      exact (cusp_diff hhol hper q (norm_pos_iff.mpr hne) hq).differentiableWithinAt
  have hφmap : Set.MapsTo φ (Metric.ball 0 ρ) (Metric.closedBall (φ 0) M) := by
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    rw [Metric.mem_closedBall, dist_eq_norm]
    rcases eq_or_ne q 0 with rfl | hne
    · rw [hφ0, sub_zero, norm_zero]; exact hM
    · rw [hφ0, sub_zero]; exact hφbd q hne hq
  intro z hz
  set q : ℂ := Function.Periodic.qParam 1 z with hqdef
  have hqne : q ≠ 0 := Function.Periodic.qParam_ne_zero z
  have hqnorm : ‖q‖ = Real.exp (-2 * Real.pi * Complex.im z) := by
    rw [hqdef, Function.Periodic.norm_qParam]; simp
  have hqρ : ‖q‖ < ρ := by
    rw [hqnorm, hρdef, Real.exp_lt_exp]; nlinarith [Real.pi_pos, hz]
  have hqmem : q ∈ Metric.ball (0:ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hqρ
  -- Schwarz lemma on the disc of radius `ρ`
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hφDiffOn hφmap hqmem
  rw [dist_eq_norm, dist_eq_norm, hφ0, sub_zero, sub_zero] at hsch
  have hφq : φ q = ψ z := by
    rw [hφdef, Function.Periodic.cuspFunction_eq_of_nonzero 1 ψ hqne]
    rw [hqdef]
    obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period (h := (1:ℝ)) one_ne_zero z
    rw [hm]
    simp only [Complex.ofReal_one, mul_one]
    exact psi_int_period hper m z hz
  rw [hφq] at hsch
  calc ‖ψ z‖ ≤ M / ρ * ‖q‖ := hsch
    _ = M * Real.exp (-2 * Real.pi * (Complex.im z - y)) := by
        rw [hqnorm, hρdef, div_eq_mul_inv, mul_assoc, ← Real.exp_neg, ← Real.exp_add]
        congr 1
        ring_nf

end Work.L62
