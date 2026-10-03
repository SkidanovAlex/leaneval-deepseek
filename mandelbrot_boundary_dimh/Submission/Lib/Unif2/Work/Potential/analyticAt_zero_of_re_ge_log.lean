import Mathlib
import Submission.Lib.Unif2.Work.Potential.extend_of_exp_neg_eq

/-!
# Extension of a holomorphic function across `0` from a logarithmic lower bound

`Work.Potential.analyticAt_zero_of_re_ge_log`: if `f` is holomorphic on the punctured disc
`0 < ‖z‖ < ρ` and its real part grows at most logarithmically near `0`,
`(f z).re ≥ -L * log (1/‖z‖) - C`, then `f` extends holomorphically to the whole disc `‖z‖ < ρ`.

The mathematical content (Riemann's removable singularity theorem in logarithmic form) is that
`z ↦ exp (-(f z))`, whose modulus is bounded above by `exp C * ‖z‖^{-L}`, is meromorphic at `0`
with meromorphic order `0`: a non-zero order would exhibit `f` as a logarithm of a monomial, which
is impossible for a single-valued function.  Consequently `exp (-(f z))` extends to a
nonvanishing analytic function `g` near `0`, and `f` is (locally) an analytic logarithm of `g`;
the actual extension is then produced by gluing a holomorphic logarithm of `g` to `f`, see
`Work.Potential.extend_of_exp_neg_eq`.

The proof is organised as

* `exists_analyticAt_of_exp_neg_of_re_ge_log_aux` : the meromorphic-order-zero statement
  (`exp (-(f ·))` extends to a nonvanishing analytic function near `0`),
* `analyticAt_glue_of_punctured` : gluing an extension on a small disc to `f`,
* `analyticAt_zero_of_re_ge_log` : the assembly.
-/

namespace Work.Potential

open Complex Filter

set_option maxHeartbeats 2000000 in
/-- **Auxiliary statement.**  Under the logarithmic lower bound, `z ↦ exp (-(f z))` agrees, in a
punctured neighbourhood of `0`, with a nonvanishing function analytic at `0`. -/
theorem exists_analyticAt_of_exp_neg_of_re_ge_log_aux {f : ℂ → ℂ} {ρ L C : ℝ} (hρ : 0 < ρ)
    (hf : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → AnalyticAt ℂ f z)
    (hlo : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → -L * Real.log (1 / ‖z‖) - C ≤ (f z).re) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → Complex.exp (-(f z)) = g z := by
  -- `N` is a natural number with `L < N`; the growth bound is `‖z‖^{-L} ≤ ‖z‖^{-N}`-free, we
  -- simply multiply `exp (-(f ·))` by `z ^ N`.
  let N : ℕ := Nat.floor L + 1
  have hNL : L < (N : ℝ) := by
    show L < ((Nat.floor L + 1 : ℕ) : ℝ)
    push_cast
    exact Nat.lt_floor_add_one L
  -- The growth bound on `z ^ N * exp (-(f z))`.
  have hbound : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ →
      ‖z ^ N * Complex.exp (-(f z))‖ ≤ Real.exp C * ρ ^ ((N : ℝ) + -L) := by
    intro z hz hzρ
    have hz0 : 0 < ‖z‖ := hz
    have h2 : -((f z).re) ≤ L * Real.log (1 / ‖z‖) + C := by linarith [hlo z hz hzρ]
    have h3 : Real.exp (-((f z).re)) ≤ Real.exp (L * Real.log (1 / ‖z‖) + C) :=
      Real.exp_le_exp.mpr h2
    have hlog : Real.log (1 / ‖z‖) = -Real.log ‖z‖ := by rw [one_div, Real.log_inv]
    have h4 : Real.exp (L * Real.log (1 / ‖z‖) + C) = Real.exp C * ‖z‖ ^ (-L) := by
      rw [hlog, Real.exp_add, Real.rpow_def_of_pos hz0]; ring_nf
    calc ‖z ^ N * Complex.exp (-(f z))‖
        = ‖z‖ ^ N * Real.exp (-((f z).re)) := by
          rw [norm_mul, norm_pow, Complex.norm_exp, Complex.neg_re]
      _ ≤ ‖z‖ ^ N * Real.exp (L * Real.log (1 / ‖z‖) + C) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Real.exp C * (‖z‖ ^ N * ‖z‖ ^ (-L)) := by rw [h4]; ring
      _ = Real.exp C * (‖z‖ ^ ((N:ℝ)) * ‖z‖ ^ (-L)) := by rw [← Real.rpow_natCast ‖z‖ N]
      _ = Real.exp C * ‖z‖ ^ ((N:ℝ) + (-L)) := by rw [Real.rpow_add hz0]
      _ ≤ Real.exp C * ρ ^ ((N:ℝ) + (-L)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos C).le
          exact Real.rpow_le_rpow hz0.le hzρ.le (by linarith [hNL])
  have hd : DifferentiableOn ℂ (fun z => z ^ N * Complex.exp (-(f z))) (Metric.ball 0 ρ \ {0}) := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz.2)
    have hzlt : ‖z‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hz.1
    exact ((analyticAt_id.pow N).mul ((hf z hzpos hzlt).neg.cexp)).differentiableAt.differentiableWithinAt
  have hb : BddAbove (norm ∘ (fun z => z ^ N * Complex.exp (-(f z)))
      '' (Metric.ball 0 ρ \ {0})) := by
    refine ⟨Real.exp C * ρ ^ ((N:ℝ) + -L), ?_⟩
    rintro y ⟨z, hz, rfl⟩
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz.2)
    have hzlt : ‖z‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hz.1
    exact hbound z hzpos hzlt
  -- Riemann's removable singularity theorem produces `A`, analytic on the disc, with
  -- `A z = z ^ N * exp (-(f z))` off the origin.
  obtain ⟨A, hA_an, hA_eq⟩ : ∃ A : ℂ → ℂ, (∀ z : ℂ, ‖z‖ < ρ → AnalyticAt ℂ A z) ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → A z = z ^ N * Complex.exp (-(f z)) := by
    refine ⟨Function.update (fun z => z ^ N * Complex.exp (-(f z))) 0
      (limUnder (nhdsWithin 0 {0}ᶜ) (fun z => z ^ N * Complex.exp (-(f z)))), ?_, ?_⟩
    · intro z hz
      have hball : Metric.ball (0:ℂ) ρ ∈ nhds (0:ℂ) := Metric.ball_mem_nhds 0 hρ
      have := Complex.differentiableOn_update_limUnder_of_bddAbove hball hd hb
      refine this.analyticAt (Metric.isOpen_ball.mem_nhds ?_)
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hz
    · intro z h1 _h2
      have hz : z ≠ 0 := norm_pos_iff.mp h1
      simp only [Function.update_of_ne hz]
  have hA_an0 : AnalyticAt ℂ A 0 := hA_an 0 (by simpa using hρ)
  -- `A` does not vanish identically on a neighbourhood of `0`.
  have hAev_ne : ¬ (A =ᶠ[nhds (0:ℂ)] 0) := by
    intro h
    obtain ⟨δ', hδ', hδ''⟩ := Metric.mem_nhds_iff.mp h
    set t : ℝ := min δ' ρ / 2 with htdef
    have htpos : 0 < t := by rw [htdef]; exact half_pos (lt_min hδ' hρ)
    have htne : ((t : ℝ) : ℂ) ≠ 0 := fun h0 => htpos.ne' (Complex.ofReal_eq_zero.mp h0)
    have htlt : ‖((t:ℝ):ℂ)‖ < ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      have := min_le_right δ' ρ; rw [htdef]; linarith
    have h1 : A ((t:ℝ):ℂ) = 0 := hδ'' (by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos htpos]
      have := min_le_left δ' ρ; rw [htdef]; linarith)
    have h2 : A ((t:ℝ):ℂ) = ((t:ℝ):ℂ) ^ N * Complex.exp (-(f ((t:ℝ):ℂ))) :=
      hA_eq _ (norm_pos_iff.mpr htne) htlt
    rw [h2] at h1
    exact (mul_ne_zero (pow_ne_zero N htne) (Complex.exp_ne_zero _)) h1
  have htop : analyticOrderAt A 0 ≠ ⊤ := fun h => hAev_ne (analyticOrderAt_eq_top.mp h)
  -- Factor `A = z ^ m * B` near `0`.
  obtain ⟨B, hB_an, hB0, hAB⟩ := (hA_an0.analyticOrderAt_ne_top).mp htop
  set m : ℕ := analyticOrderNatAt A 0 with hmdef
  have hABev : A =ᶠ[nhds (0:ℂ)] fun z => z ^ m * B z := by
    refine hAB.mono ?_
    intro z hz
    simpa using hz
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_nhds_iff.mp hABev
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.mem_nhds_iff.mp hB_an.eventually_analyticAt
  have hBne_ev : ∀ᶠ z in nhds (0:ℂ), B z ≠ 0 := hB_an.continuousAt.eventually_ne hB0
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.mem_nhds_iff.mp hBne_ev
  set δ : ℝ := min δ₀ (min δ₁ (min δ₂ ρ)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ (lt_min hδ₁ (lt_min hδ₂ hρ))
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδδ₁ : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδδ₂ : δ ≤ δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδρ : δ ≤ ρ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmem : ∀ {r' : ℝ} {z : ℂ}, ‖z‖ < r' → z ∈ Metric.ball (0:ℂ) r' := by
    intro r' z hz; rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hz
  -- The logarithmic derivative of `exp (-(f ·))`.
  have hlogu_lemma : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ →
      logDeriv (fun z => Complex.exp (-(f z))) z = -deriv f z := by
    intro z h1 h2
    have hfd : DifferentiableAt ℂ f z := (hf z h1 h2).differentiableAt
    have hd' : DifferentiableAt ℂ (fun z => -(f z)) z := hfd.neg
    have hdneg : deriv (fun z => -(f z)) z = -(deriv f z) := by
      simpa using hfd.hasDerivAt.neg.deriv
    have hderiv : deriv (fun z => Complex.exp (-(f z))) z
        = Complex.exp (-(f z)) * (-(deriv f z)) := by
      rw [show (fun z => Complex.exp (-(f z))) = Complex.exp ∘ (fun z => -(f z)) from rfl]
      rw [deriv_comp _ differentiable_exp.differentiableAt hd', Complex.deriv_exp, hdneg]
    rw [logDeriv_apply, hderiv, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  -- The central identity `deriv f = -((m - N)/z) - B'/B`.
  have hkey : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ →
      deriv f z = -(((m : ℂ) - (N : ℂ)) / z) - deriv B z / B z := by
    intro z hz1 hz2
    have hBz_an : AnalyticAt ℂ B z := hδ₁' (hmem (lt_of_lt_of_le hz2 hδδ₁))
    have hBz : B z ≠ 0 := hδ₂' (hmem (lt_of_lt_of_le hz2 hδδ₂))
    have hP : (fun w => Complex.exp (-(f w))) =ᶠ[nhds z] (fun w => w ^ m * B w / w ^ N) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hmem hz2),
        isOpen_compl_singleton.mem_nhds (norm_pos_iff.mp hz1)] with w hw hwne
      have hwdelta : ‖w‖ < δ := by rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw; exact hw
      have hwne' : w ≠ 0 := by simpa using hwne
      have h1 : A w = w ^ N * Complex.exp (-(f w)) :=
        hA_eq w (norm_pos_iff.mpr hwne') (lt_of_lt_of_le hwdelta hδρ)
      have h2 : A w = w ^ m * B w := hδ₀' (hmem (lt_of_lt_of_le hwdelta hδδ₀))
      rw [h1] at h2
      rw [eq_div_iff (pow_ne_zero N hwne')]
      simpa [mul_comm] using h2
    have hcongr : logDeriv (fun w => Complex.exp (-(f w))) z
        = logDeriv (fun w => w ^ m * B w / w ^ N) z := (logDeriv_congr_nhds hP).eq_of_nhds
    have hcalc : logDeriv (fun w => w ^ m * B w / w ^ N) z
        = ((m:ℂ) - (N:ℂ))/z + deriv B z / B z := by
      have hz0 : z ≠ 0 := norm_pos_iff.mp hz1
      have hnum : z ^ m * B z ≠ 0 := mul_ne_zero (pow_ne_zero m hz0) hBz
      have hden : z ^ N ≠ 0 := pow_ne_zero N hz0
      have hdn : DifferentiableAt ℂ (fun w : ℂ => w ^ m * B w) z :=
        (differentiableAt_id.pow m).mul hBz_an.differentiableAt
      have hdd : DifferentiableAt ℂ (fun w : ℂ => w ^ N) z := differentiableAt_id.pow N
      rw [logDeriv_fun_div z hnum hden hdn hdd]
      rw [logDeriv_fun_mul z (f := fun w : ℂ => w ^ m) (g := B) (pow_ne_zero m hz0) hBz
        (differentiableAt_id.pow m) hBz_an.differentiableAt]
      rw [logDeriv_pow, logDeriv_pow, logDeriv_apply]
      ring
    have hsum : -deriv f z = ((m:ℂ) - (N:ℂ))/z + deriv B z / B z := by
      rw [← hlogu_lemma z hz1 (lt_of_lt_of_le hz2 hδρ), hcongr, hcalc]
    show deriv f z = -(((m:ℂ) - (N:ℂ)) / z) - deriv B z / B z
    have h5 : deriv f z = -(((m:ℂ) - (N:ℂ))/z + deriv B z / B z) := by
      rw [← neg_neg (deriv f z), hsum]
    rw [h5]; ring
  have hdiffB : DifferentiableOn ℂ (fun z => deriv B z / B z) (Metric.ball 0 δ) := by
    intro z hz
    have hzlt : ‖z‖ < δ := by rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz; exact hz
    have hBan : AnalyticAt ℂ B z := hδ₁' (hmem (lt_of_lt_of_le hzlt hδδ₁))
    have hBden : B z ≠ 0 := hδ₂' (hmem (lt_of_lt_of_le hzlt hδδ₂))
    exact (hBan.deriv.differentiableAt.div hBan.differentiableAt hBden).differentiableWithinAt
  -- The contour integral of `deriv f` around a small circle vanishes, while the identity above
  -- evaluates it to `2 * π * I * (N - m)`.
  set r : ℝ := δ / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrδ : r < δ := by rw [hrdef]; linarith
  have hsphere : ∀ z ∈ Metric.sphere (0:ℂ) r, 0 < ‖z‖ ∧ ‖z‖ < δ := by
    intro z hz
    have hzn : ‖z‖ = r := by rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz; exact hz
    exact ⟨by rw [hzn]; exact hrpos, by rw [hzn]; exact hrδ⟩
  have hint1 : (∮ z in C(0, r), deriv f z) = 0 := by
    refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := f) hrpos.le (fun z hz => ?_)
    obtain ⟨h1, h2⟩ := hsphere z hz
    exact (hf z h1 (lt_of_lt_of_le h2 hδρ)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hint2 : (∮ z in C(0, r), deriv f z)
      = ∮ z in C(0, r), (-(((m:ℂ)-(N:ℂ))/z) - deriv B z / B z) := by
    refine circleIntegral.integral_congr hrpos.le (fun z hz => ?_)
    obtain ⟨h1, h2⟩ := hsphere z hz
    exact hkey z h1 h2
  have hcont1 : ContinuousOn (fun z : ℂ => -(((m:ℂ)-(N:ℂ))/z)) (Metric.sphere (0:ℂ) r) := by
    refine ContinuousOn.neg ?_
    refine ContinuousOn.div continuousOn_const continuousOn_id ?_
    intro z hz
    have hzn : ‖z‖ = r := by rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz; exact hz
    intro h; rw [h, norm_zero] at hzn; linarith
  have hcont2 : ContinuousOn (fun z : ℂ => deriv B z / B z) (Metric.sphere (0:ℂ) r) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · intro z hz
      obtain ⟨h1, h2⟩ := hsphere z hz
      exact (hδ₁' (hmem (lt_of_lt_of_le h2 hδδ₁))).deriv.continuousAt.continuousWithinAt
    · intro z hz
      obtain ⟨h1, h2⟩ := hsphere z hz
      exact (hδ₁' (hmem (lt_of_lt_of_le h2 hδδ₁))).continuousAt.continuousWithinAt
    · intro z hz
      obtain ⟨h1, h2⟩ := hsphere z hz
      exact hδ₂' (hmem (lt_of_lt_of_le h2 hδδ₂))
  have hsplit : (∮ z in C(0, r), (-(((m:ℂ)-(N:ℂ))/z) - deriv B z / B z))
      = (∮ z in C(0, r), (-(((m:ℂ)-(N:ℂ))/z))) - (∮ z in C(0, r), deriv B z / B z) :=
    circleIntegral.integral_sub (hcont1.circleIntegrable hrpos.le)
      (hcont2.circleIntegrable hrpos.le)
  have hA_int : (∮ z in C(0, r), (-(((m:ℂ)-(N:ℂ))/z)))
      = -((m:ℂ)-(N:ℂ)) * (2*(Real.pi:ℂ)*Complex.I) := by
    rw [show (fun z : ℂ => -(((m:ℂ)-(N:ℂ))/z))
        = (fun z : ℂ => (-((m:ℂ)-(N:ℂ))) * (z - 0)⁻¹) from by
      funext z; simp only [div_eq_mul_inv, sub_zero]; ring]
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv 0 hrpos.ne']
  have hB_int : (∮ z in C(0, r), deriv B z / B z) = 0 := by
    obtain ⟨Ψ, -, hΨ⟩ := (hdiffB.isExactOn_ball).with_val_at 0 0
    refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := Ψ) hrpos.le (fun z hz => ?_)
    obtain ⟨h1, h2⟩ := hsphere z hz
    exact (hΨ z (hmem h2)).hasDerivWithinAt
  have hzero : -((m:ℂ)-(N:ℂ)) * (2*(Real.pi:ℂ)*Complex.I) = 0 := by
    have h := hint1
    rw [hint2, hsplit, hA_int, hB_int, sub_zero] at h
    exact h
  have hmN : m = N := by
    have h2p : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := mul_ne_zero h2p Complex.I_ne_zero
    rcases mul_eq_zero.mp hzero with h | h
    · have h' : (m:ℂ) - (N:ℂ) = 0 := neg_eq_zero.mp h
      exact Nat.cast_injective (sub_eq_zero.mp h')
    · exact absurd h h2pi
  -- With `m = N` the order of `A` equals the order of the factor `z ^ N`, so `exp (-(f ·))`
  -- agrees with the nonvanishing analytic function `B` near `0`.
  refine ⟨B, hB_an, hB0, δ, hδpos, ?_⟩
  intro z hz1 hz2
  have h1 : A z = z ^ N * Complex.exp (-(f z)) := hA_eq z hz1 (lt_of_lt_of_le hz2 hδρ)
  have h2 : A z = z ^ m * B z := hδ₀' (hmem (lt_of_lt_of_le hz2 hδδ₀))
  rw [h1, hmN] at h2
  exact mul_left_cancel₀ (pow_ne_zero N (norm_pos_iff.mp hz1)) h2

/-- **Gluing lemma.** If `f` is holomorphic on the punctured disc `0 < ‖z‖ < ρ` and `F` is a
holomorphic extension of `f` to the smaller disc `‖z‖ < r`, then the function which equals `F`
inside `‖z‖ < r` and `f` outside is holomorphic on the whole disc `‖z‖ < ρ` and agrees with `f`
off the origin. -/
theorem analyticAt_glue_of_punctured {f F : ℂ → ℂ} {ρ r : ℝ} (hr : 0 < r)
    (hf : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → AnalyticAt ℂ f z)
    (hF : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ F z)
    (hFeq : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r → F z = f z) :
    (∀ z : ℂ, ‖z‖ < ρ → AnalyticAt ℂ (fun z => if ‖z‖ < r then F z else f z) z) ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → (if ‖z‖ < r then F z else f z) = f z := by
  constructor
  · intro z hz
    by_cases hzr : ‖z‖ < r
    · -- `z` lies inside the small disc: use `F` locally
      refine AnalyticAt.congr (hF z hzr) ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hzr] with w hw
      simp [hw]
    · -- `z ≠ 0` lies outside the small disc: use `f` locally
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hr (not_lt.mp hzr)
      have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
      refine AnalyticAt.congr (hf z hzpos hz) ?_
      filter_upwards [isOpen_compl_singleton.mem_nhds hzne] with w hw
      by_cases hwr : ‖w‖ < r
      · rw [if_pos hwr]
        exact (hFeq w (norm_pos_iff.mpr hw) hwr).symm
      · rw [if_neg hwr]
  · intro z h1 h2
    by_cases hzr : ‖z‖ < r
    · rw [if_pos hzr]; exact hFeq z h1 hzr
    · rw [if_neg hzr]

theorem analyticAt_zero_of_re_ge_log {f : ℂ → ℂ} {ρ L C : ℝ} (hρ : 0 < ρ)
    (hf : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → AnalyticAt ℂ f z)
    (hlo : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → -L * Real.log (1 / ‖z‖) - C ≤ (f z).re) :
    ∃ g : ℂ → ℂ, (∀ z : ℂ, ‖z‖ < ρ → AnalyticAt ℂ g z) ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → g z = f z := by
  -- `exp (-(f ·))` extends to a nonvanishing analytic function near `0`.
  obtain ⟨g, hg_an, hg0, ε, hε, heq⟩ :=
    exists_analyticAt_of_exp_neg_of_re_ge_log_aux hρ hf hlo
  -- `g` is analytic on a Euclidean ball around `0`
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.mem_nhds_iff.mp hg_an.eventually_analyticAt
  -- `g` does not vanish on a Euclidean ball around `0`
  have hne_ev : ∀ᶠ z in nhds (0 : ℂ), g z ≠ 0 := hg_an.continuousAt.eventually_ne hg0
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.mem_nhds_iff.mp hne_ev
  set r : ℝ := min δ₁ (min δ₂ (min ε ρ)) with hrdef
  have hr : 0 < r := lt_min hδ₁ (lt_min hδ₂ (lt_min hε hρ))
  have hrδ₁ : r ≤ δ₁ := min_le_left _ _
  have hrδ₂ : r ≤ δ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrε : r ≤ ε := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrρ : r ≤ ρ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨G, hG_an, hG_eq⟩ := extend_of_exp_neg_eq hr
    (fun z h1 h2 => hf z h1 (lt_of_lt_of_le h2 hrρ))
    (fun z hz => hδ₁' (by simpa [Metric.mem_ball, dist_eq_norm] using lt_of_lt_of_le hz hrδ₁))
    (fun z hz => hδ₂' (by simpa [Metric.mem_ball, dist_eq_norm] using lt_of_lt_of_le hz hrδ₂))
    (fun z h1 h2 => heq z h1 (lt_of_lt_of_le h2 hrε))
  exact ⟨_, analyticAt_glue_of_punctured hr hf hG_an hG_eq⟩

end Work.Potential
