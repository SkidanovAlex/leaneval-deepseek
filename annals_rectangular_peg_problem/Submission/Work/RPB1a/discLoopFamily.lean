import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric Filter
open scoped ContDiff Real Topology
open Work.RPB1a

/-- N8: the level circles of a locally biholomorphic map of a disc form a loop family from the unit
circle to `(F (e^{it}) - F 0)/a`.

Put `h := dslope F 0 / a`, holomorphic on `ball 0 R` (`differentiableOn_dslope`) with
`h 0 = deriv F 0 / a = 1`, and `c s t := exp (t*I) * h (φ s * exp (t*I))` with
`φ := Real.smoothTransition`.  Joint `C^∞`: `h` is `ContDiffOn ℂ ∞` on the open ball, restrict
scalars, and compose with `(s,t) ↦ φ s * exp (t*I)`, which maps into `closedBall 0 1 ⊆ ball 0 R`.
Then `c 0 = exp (t*I)` and `c 1 t = (F (exp (t*I)) - F 0)/a`.
Injectivity: for `r := φ s > 0`, `c s t = (F (r exp (t*I)) - F 0)/(a r)`, so it follows from
injectivity of `F` and of `exp` mod `2π`; `r = 0` is the circle.
Immersion: with `k z := z * h z = (F z - F 0)/a`,
`∂_t c = I * exp (t*I) * k' (r exp (t*I)) = I * exp (t*I) * F' (r exp (t*I))/a ≠ 0`, one formula
for all `r ∈ [0,1]`. -/
theorem discLoopFamily (F : ℂ → ℂ) (R : ℝ) (hR : 1 < R)
    (hFd : DifferentiableOn ℂ F (ball 0 R)) (hFi : InjOn F (ball 0 R))
    (hFd' : ∀ z ∈ ball 0 R, deriv F z ≠ 0) (a : ℝ) (ha : 0 < a) (hFa : deriv F 0 = a) :
    ∃ c : ℝ → ℝ → ℂ, IsLoopFamily c ∧ (∀ t : ℝ, c 0 t = Complex.exp (t * I)) ∧
      ∀ t : ℝ, c 1 t = (F (Complex.exp (t * I)) - F 0) / a := by
  have hR0 : (0:ℝ) < R := lt_trans zero_lt_one hR
  have haC : (((a:ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  -- `r * exp (t I)` stays in the disc of radius `R` for `0 ≤ r ≤ 1`
  have hmem_of : ∀ (r : ℝ), 0 ≤ r → r ≤ 1 → ∀ t : ℝ,
      r * Complex.exp (t*Complex.I) ∈ Metric.ball 0 R := by
    intro r hr0 hr1 t
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖r * Complex.exp (t*Complex.I)‖
        = ‖((r:ℝ):ℂ)‖ * ‖Complex.exp ((t:ℂ)*Complex.I)‖ := norm_mul _ _
      _ = |r| * 1 := by rw [Complex.norm_exp_ofReal_mul_I]; simp
      _ = r := by rw [abs_of_nonneg hr0, mul_one]
      _ ≤ 1 := hr1
      _ < R := hR
  -- `h := dslope F 0 / a` is holomorphic (hence smooth) on the disc
  have hcontC : ContDiffOn ℂ ∞ (fun z => dslope F 0 z / (a:ℂ)) (Metric.ball 0 R) := by
    have hmem : Metric.ball (0:ℂ) R ∈ 𝓝 (0:ℂ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR0)
    have hd : DifferentiableOn ℂ (dslope F 0) (Metric.ball 0 R) :=
      (Complex.differentiableOn_dslope hmem).mpr hFd
    exact (((Complex.analyticOn_iff_differentiableOn Metric.isOpen_ball).mpr
      (hd.div_const _)).contDiffOn Metric.isOpen_ball.uniqueDiffOn)
  -- joint smoothness of `(s,t) ↦ exp (t I) * h (φ s * exp (t I))`
  have hsmooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => Complex.exp (z.2 * Complex.I) *
      (dslope F 0 (Real.smoothTransition z.1 * Complex.exp (z.2 * Complex.I)) / (a:ℂ))) := by
    have hcontR : ContDiffOn ℝ ∞ (fun z => dslope F 0 z / (a:ℂ)) (Metric.ball 0 R) :=
      hcontC.restrict_scalars ℝ
    have hexp : ContDiff ℝ ∞ (fun z : ℝ×ℝ => Complex.exp (z.2 * Complex.I)) :=
      Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
    have hg : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
        Real.smoothTransition z.1 * Complex.exp (z.2 * Complex.I)) :=
      (Complex.ofRealCLM.contDiff.comp
        (Real.smoothTransition.contDiff (n := ⊤) |>.comp contDiff_fst)).mul hexp
    have hmaps : ∀ z : ℝ×ℝ,
        Real.smoothTransition z.1 * Complex.exp (z.2*Complex.I) ∈ Metric.ball 0 R :=
      fun z => hmem_of _ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _) z.2
    exact hexp.mul (ContDiffOn.comp_contDiff hcontR hg hmaps)
  -- `k z := (F z - F 0)/a` is complex differentiable on the disc with derivative `F' z / a`
  have hk_deriv : ∀ z ∈ Metric.ball 0 R,
      HasDerivAt (fun w => (F w - F 0)/(a:ℂ)) (deriv F z/(a:ℂ)) z := by
    intro z hz
    have hdz : HasDerivAt F (deriv F z) z :=
      (hFd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
    simpa using (hdz.sub_const (F 0)).div_const (a:ℂ)
  -- the divided-difference identity `z * h z = k z`, in the form needed at `z = r exp (t I)`
  have hc_form : ∀ (r t : ℝ), r ≠ 0 → Complex.exp (t*Complex.I) *
      (dslope F 0 (r * Complex.exp (t*Complex.I)) / (a:ℂ))
      = (F (r * Complex.exp (t*Complex.I)) - F 0) / ((a:ℂ) * r) := by
    intro r t hr
    have he : Complex.exp (t * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hrc : ((r:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hz : r * Complex.exp (t*Complex.I) ≠ 0 := mul_ne_zero hrc he
    have hs := sub_smul_dslope F (0:ℂ) (r * Complex.exp (t*Complex.I))
    rw [sub_zero, smul_eq_mul] at hs
    have hds : dslope F 0 (r * Complex.exp (t*Complex.I)) =
        (F (r*Complex.exp (t*Complex.I)) - F 0)/(r * Complex.exp (t*Complex.I)) := by
      rw [eq_div_iff hz, mul_comm]; exact hs
    rw [hds]
    field_simp
  -- derivative of `t ↦ exp (t I)`
  have hd_exp : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (t*Complex.I))
      (Complex.exp (t*Complex.I) * Complex.I) t := by
    intro t
    have hid : HasDerivAt (fun t : ℝ => (t:ℂ) * Complex.I) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
    simpa using hid.cexp
  -- injectivity of `exp (· I)` modulo `2π`
  have hexp_inj : ∀ t t' : ℝ, Complex.exp (t * Complex.I) = Complex.exp (t' * Complex.I) →
      ∃ m : ℤ, t' = t + 2 * π * m := by
    intro t t' he
    rw [Complex.exp_eq_exp_iff_exists_int] at he
    obtain ⟨n, hn⟩ := he
    have h3 : t = t' + n * (2 * π) := by
      have := congrArg Complex.im hn
      simpa using this
    exact ⟨-n, by push_cast at h3 ⊢; linarith⟩
  -- `2π`-periodicity of `t ↦ exp (t I)`
  have hper : ∀ t : ℝ, Complex.exp (((t + 2*π : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((t : ℂ) * Complex.I) := by
    intro t
    have harg : (((t + 2*π : ℝ) : ℂ)) * Complex.I =
        (t : ℂ) * Complex.I + ((2*π : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_add]
    have h2 : Complex.exp (((2*π : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show ((2*π : ℝ) : ℂ) = 2 * (Real.pi : ℂ) by push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    rw [h2, mul_one]
  refine ⟨fun s t => Complex.exp (t*Complex.I) *
      (dslope F 0 (Real.smoothTransition s * Complex.exp (t*Complex.I)) / (a:ℂ)), ?_, ?_, ?_⟩
  · refine ⟨hsmooth, ?_, ?_, ?_⟩
    · -- `2π`-periodicity
      intro s t
      dsimp only
      rw [hper t]
    · -- injectivity modulo `2π`
      intro s hs t t' heq
      dsimp only at heq
      by_cases hr : Real.smoothTransition s = 0
      · -- `r = 0`: the unit circle itself
        rw [hr] at heq
        simp only [Complex.ofReal_zero, zero_mul, dslope_same, hFa, div_self haC, mul_one] at heq
        exact hexp_inj t t' heq
      · -- `r > 0`: the level circle `r·S¹`
        have h1 := hc_form (Real.smoothTransition s) t hr
        have h2 := hc_form (Real.smoothTransition s) t' hr
        rw [h1, h2] at heq
        have hden : ((a:ℂ) * ((Real.smoothTransition s : ℝ):ℂ)) ≠ 0 :=
          mul_ne_zero haC (Complex.ofReal_ne_zero.mpr hr)
        have hF : F (Real.smoothTransition s * Complex.exp (t*Complex.I)) =
            F (Real.smoothTransition s * Complex.exp (t'*Complex.I)) := by
          have hh := congrArg (fun z => z * ((a:ℂ) * ((Real.smoothTransition s : ℝ):ℂ))) heq
          rw [div_mul_cancel₀ _ hden, div_mul_cancel₀ _ hden] at hh
          exact sub_left_inj.mp hh
        have hmem1 := hmem_of (Real.smoothTransition s) (Real.smoothTransition.nonneg s)
          (Real.smoothTransition.le_one s) t
        have hmem2 := hmem_of (Real.smoothTransition s) (Real.smoothTransition.nonneg s)
          (Real.smoothTransition.le_one s) t'
        have hz := hFi hmem1 hmem2 hF
        have hee : Complex.exp (t*Complex.I) = Complex.exp (t'*Complex.I) :=
          mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr) hz
        exact hexp_inj t t' hee
    · -- immersion
      intro s hs t
      dsimp only
      by_cases hr : Real.smoothTransition s = 0
      · -- `r = 0`: derivative of the unit circle
        have hcs : (fun t : ℝ => Complex.exp (t*Complex.I) *
            (dslope F 0 (Real.smoothTransition s * Complex.exp (t*Complex.I))/(a:ℂ)))
            = fun t : ℝ => Complex.exp (t*Complex.I) := by
          funext t
          rw [hr, Complex.ofReal_zero, zero_mul, dslope_same, hFa, div_self haC, mul_one]
        rw [hcs, (hd_exp t).deriv]
        exact mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
      · -- `r > 0`: derivative of a level circle, `I·exp (t I)·k'(r exp (t I))`
        have hcs : (fun t : ℝ => Complex.exp (t*Complex.I) *
            (dslope F 0 (Real.smoothTransition s * Complex.exp (t*Complex.I))/(a:ℂ)))
            = fun t : ℝ => ((F (Real.smoothTransition s * Complex.exp (t*Complex.I)) - F 0)/(a:ℂ))/(Real.smoothTransition s) := by
          funext t
          rw [hc_form (Real.smoothTransition s) t hr, div_div]
        rw [hcs]
        have hmem := hmem_of (Real.smoothTransition s) (Real.smoothTransition.nonneg s)
          (Real.smoothTransition.le_one s) t
        have hinner : HasDerivAt (fun t : ℝ => Real.smoothTransition s * Complex.exp (t*Complex.I))
            (((Real.smoothTransition s : ℝ) : ℂ) * (Complex.exp (t*Complex.I) * Complex.I)) t := by
          simpa using (hd_exp t).const_mul (((Real.smoothTransition s : ℝ)) : ℂ)
        have hdiv := ((hk_deriv _ hmem).comp t hinner).div_const (((Real.smoothTransition s : ℝ)) : ℂ)
        have hd : deriv (fun t : ℝ => ((F (↑(Real.smoothTransition s) * Complex.exp (↑t*Complex.I)) - F 0)/(a:ℂ))/(Real.smoothTransition s)) t =
            (deriv F (↑(Real.smoothTransition s) * Complex.exp (↑t*Complex.I))/↑a *
              (↑(Real.smoothTransition s) * (Complex.exp (↑t*Complex.I)*Complex.I)))/↑(Real.smoothTransition s) := by
          simpa only [Function.comp_apply] using hdiv.deriv
        rw [hd]
        refine div_ne_zero (mul_ne_zero (div_ne_zero (hFd' _ hmem) haC) ?_)
          (Complex.ofReal_ne_zero.mpr hr)
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr)
          (mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero)
  · -- `c 0 t = exp (t I)`
    intro t
    dsimp only
    rw [Real.smoothTransition.zero, Complex.ofReal_zero, zero_mul, dslope_same, hFa, div_self haC, mul_one]
  · -- `c 1 t = (F (exp (t I)) - F 0)/a`
    intro t
    dsimp only
    rw [Real.smoothTransition.one, Complex.ofReal_one, one_mul]
    have he : Complex.exp (t*Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hs := sub_smul_dslope F (0:ℂ) (Complex.exp (t*Complex.I))
    rw [sub_zero, smul_eq_mul] at hs
    have hds : dslope F 0 (Complex.exp (t*Complex.I)) =
        (F (Complex.exp (t*Complex.I)) - F 0)/Complex.exp (t*Complex.I) := by
      rw [eq_div_iff he, mul_comm]; exact hs
    rw [hds]
    field_simp

end Work.RPB1a
