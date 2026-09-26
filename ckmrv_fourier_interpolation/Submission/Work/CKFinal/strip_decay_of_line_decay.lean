/-
# `strip_decay_of_line_decay`

Statement (part (f), step 4 of CKMRV):  a holomorphic `f : ℍ → ℂ` with `(T-I)²f = 0`, moderate
growth `‖f τ‖ ≤ C · scale τ ^ N` and decay of `f` at the cusp of order `m - 1` decays like
`(1 + |τ|) e^{-2π m im τ}` on the strip `-1 ≤ re τ ≤ 1`, `2 ≤ im τ`, with a constant depending only
on `m`, `C` and `N`.

The proof is the standard `q`-expansion argument.  Write

  `B τ = f (τ+1) - f τ`,   `A τ = f τ - τ · B τ`.

`(T-I)²f = 0` says that `B` is `1`-periodic, and then so is `A`, and `f = A + τ B`.  Both have
moderate growth, and the decay hypothesis on the lines propagates to `B` (and, using the resulting
exponential bound on `B`, to `A`).  For a `1`-periodic holomorphic `g` of moderate growth, the
function `q ↦ g` of `q = e^{2πiτ}` is holomorphic on the punctured unit disc and extends
holomorphically to `0` (the growth `(1+|log|q||)^A` is `o(1/|q|)`); decay of order `ρ` along the
line `re τ = -1/2` says that the extension vanishes to order `ρ + 1` at `q = 0`.  Schwarz's lemma
(maximum modulus on the disc `|q| ≤ e^{-2π y₀}`) then gives

  `‖g τ‖ ≤ M e^{-2π (ρ+1) (im τ - y₀)}`,   `M = sup_{re = [-1/2,1/2], im = y₀} ‖g‖`,

with `M` controlled by the growth constants alone.  Applying this to `B` (with `ρ = m-1`) and
then to `A` and adding concludes the proof.
-/
import Mathlib
import Submission.Work.CKFinal.EngineDefs
import Submission.Work.CKFinal.qExp_basic
import Submission.Work.CKFinal.strip_structure
import Submission.Work.CKFinal.strip_constants
import Submission.Work.CKFinal.cusp_at_zero

noncomputable section

open Filter Metric UpperHalfPlane
open scoped Topology

namespace Work.CKFinal

/-! ## 1. The Schwarz-lemma core

If a holomorphic `Φ` vanishes at `0` and is bounded by `N` on the circle `|q| = R < 1`, then
`‖Φ q‖ ≤ N ‖q‖ / R` on the closed disc. -/

theorem norm_le_of_sphere {Φ : ℂ → ℂ} {R N : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hd : DifferentiableOn ℂ Φ (ball 0 1)) (h0 : Φ 0 = 0)
    (hN : ∀ q : ℂ, ‖q‖ = R → ‖Φ q‖ ≤ N) :
    ∀ q : ℂ, ‖q‖ ≤ R → ‖Φ q‖ ≤ N * ‖q‖ / R := by
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := Metric.closedBall_subset_ball hR1
  have hd' : DifferentiableOn ℂ Φ (closedBall 0 R) := hd.mono hsub
  have hcont : ContinuousOn Φ (closedBall 0 R) := hd.continuousOn.mono hsub
  have hdc : DiffContOnCl ℂ Φ (closedBall 0 R) :=
    ⟨hd', by rwa [isClosed_closedBall.closure_eq]⟩
  have hmax : ∀ q : ℂ, q ∈ closedBall 0 R → ‖Φ q‖ ≤ N := by
    intro q hq
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_closedBall hdc ?_
      (by rwa [isClosed_closedBall.closure_eq])
    intro z hz
    rw [frontier_closedBall _ hR.ne'] at hz
    exact hN z (mem_sphere_zero_iff_norm.mp hz)
  intro q hq
  rcases lt_or_eq_of_le hq with hlt | heq
  · have hmem : q ∈ ball (0 : ℂ) R := by rwa [mem_ball, dist_zero_right]
    have hmaps : Set.MapsTo Φ (ball (0 : ℂ) R) (closedBall (Φ 0) N) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm]
      simpa [h0] using hmax z (ball_subset_closedBall hz)
    have h1 := Complex.dist_le_div_mul_dist_of_mapsTo_ball (f := Φ) (c := (0 : ℂ))
      (R₁ := R) (R₂ := N) (hd.mono (ball_subset_ball hR1.le)) hmaps hmem
    rw [dist_eq_norm, dist_eq_norm] at h1
    simp only [h0, sub_zero] at h1
    calc ‖Φ q‖ ≤ N / R * ‖q‖ := h1
      _ = N * ‖q‖ / R := by ring
  · have hbound := hmax q (by rw [mem_closedBall, dist_zero_right, heq])
    calc ‖Φ q‖ ≤ N := hbound
      _ = N * R / R := by rw [mul_div_assoc, div_self hR.ne', mul_one]
      _ = N * ‖q‖ / R := by rw [heq]

/-! ## 2. The bound for the `q`-expansion on the circle `|q| = e^{-2π y₀}` -/

/-- The real part of `invQParam 1 q` is `arg q / 2π` (so it lies in `(-1/2, 1/2]`). -/
lemma invQParam_one_re (q : ℂ) :
    (Function.Periodic.invQParam 1 q).re = Complex.arg q / (2 * Real.pi) := by
  have h1 : Function.Periodic.invQParam 1 q
      = Complex.log q / ((((2 : ℝ) * Real.pi : ℝ)) * Complex.I : ℂ) := by
    rw [Function.Periodic.invQParam]
    field_simp
    push_cast
    ring
  rw [h1]
  have h2 : Complex.log q / ((((2 : ℝ) * Real.pi : ℝ)) * Complex.I : ℂ)
      = (Complex.log q / (((2 : ℝ) * Real.pi : ℝ) : ℂ)) / Complex.I := by ring
  rw [h2, Complex.div_I, Complex.neg_re, Complex.mul_I_re, neg_neg,
    Complex.div_ofReal_im, Complex.log_im]

theorem qExp_sphere_bound (g : UpperHalfPlane → ℂ) {y₀ M : ℝ} (hy₀ : 0 < y₀)
    (happ : ∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ)
    (hbdy : ∀ τ : UpperHalfPlane, τ.im = y₀ → |τ.re| ≤ 1 / 2 → ‖g τ‖ ≤ M) :
    ∀ q : ℂ, ‖q‖ = Real.exp (-(2 * Real.pi * y₀)) → ‖qExp g q‖ ≤ M := by
  intro q hq
  have hR : 0 < Real.exp (-(2 * Real.pi * y₀)) := Real.exp_pos _
  have hq0 : q ≠ 0 := by
    intro h; rw [h, norm_zero] at hq; exact absurd hq.symm hR.ne'
  have hzlog : (Function.Periodic.invQParam 1 q).im = y₀ := by
    rw [Function.Periodic.im_invQParam, hq, Real.log_exp]
    field_simp
  have hzpos : 0 < (Function.Periodic.invQParam 1 q).im := by rw [hzlog]; exact hy₀
  have hqparam : Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q) = q :=
    Function.Periodic.qParam_right_inv one_ne_zero hq0
  have hre : |(Function.Periodic.invQParam 1 q).re| ≤ 1 / 2 := by
    have h1 := Complex.neg_pi_lt_arg q
    have h2 := Complex.arg_le_pi q
    rw [invQParam_one_re, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi),
      div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi), abs_le]
    constructor <;> linarith
  have h := happ ⟨Function.Periodic.invQParam 1 q, hzpos⟩
  rw [hqparam] at h
  rw [h]
  exact hbdy ⟨Function.Periodic.invQParam 1 q, hzpos⟩ hzlog hre

/-! ## 3. The two `q`-expansion decay estimates -/

/-- A `1`-periodic `g` whose `q`-expansion is holomorphic on the punctured disc, holomorphic at
`0` with value `0` and bounded by `M` on the circle `|q| = e^{-2π y₀}`, satisfies
`‖g τ‖ ≤ M e^{-2π (im τ - y₀)}` for `im τ ≥ y₀`. -/
theorem periodic_decay_zero (g : UpperHalfPlane → ℂ) {y₀ M : ℝ} (hy₀ : 0 < y₀)
    (happ : ∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ)
    (hdiff : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → DifferentiableAt ℂ (qExp g) q)
    (h0 : DifferentiableAt ℂ
      (Function.update (qExp g) 0 ((nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g))) 0)
    (hval : (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g) = 0)
    (hbdy : ∀ τ : UpperHalfPlane, τ.im = y₀ → |τ.re| ≤ 1 / 2 → ‖g τ‖ ≤ M) :
    ∀ τ : UpperHalfPlane, y₀ ≤ τ.im →
      ‖g τ‖ ≤ M * Real.exp (-(2 * Real.pi * (τ.im - y₀))) := by
  have hF0 : qExp g 0 = (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g) :=
    Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne 1 (pext g)
  have hupd : Function.update (qExp g) 0 ((nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g))
      = qExp g := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [Function.update_self]; exact hF0.symm
    · rw [Function.update_of_ne hx]
  have h0' : DifferentiableAt ℂ (qExp g) 0 := by rw [← hupd]; exact h0
  have hval' : qExp g 0 = 0 := by rw [hF0, hval]
  have hR : 0 < Real.exp (-(2 * Real.pi * y₀)) := Real.exp_pos _
  have hR1 : Real.exp (-(2 * Real.pi * y₀)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hy₀]
  have hd1 : DifferentiableOn ℂ (qExp g) (ball 0 1) := by
    intro q hq
    rw [mem_ball, dist_zero_right] at hq
    rcases eq_or_ne q 0 with rfl | hq0
    · exact h0'.differentiableWithinAt
    · exact (hdiff q (norm_pos_iff.mpr hq0) hq).differentiableWithinAt
  have hN : ∀ q : ℂ, ‖q‖ = Real.exp (-(2 * Real.pi * y₀)) → ‖qExp g q‖ ≤ M :=
    qExp_sphere_bound g hy₀ happ hbdy
  have hkey := norm_le_of_sphere hR hR1 hd1 hval' hN
  intro τ hτ
  have hqnorm : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Function.Periodic.norm_qParam]; norm_num
  have hle : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ Real.exp (-(2 * Real.pi * y₀)) := by
    rw [hqnorm]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h := hkey _ hle
  rw [happ τ] at h
  have hnum : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ / Real.exp (-(2 * Real.pi * y₀))
      = Real.exp (-(2 * Real.pi * (τ.im - y₀))) := by
    rw [hqnorm, ← Real.exp_sub]
    congr 1
    ring
  calc ‖g τ‖ ≤ M * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ / Real.exp (-(2 * Real.pi * y₀)) := h
    _ = M * (‖Function.Periodic.qParam 1 (τ : ℂ)‖ / Real.exp (-(2 * Real.pi * y₀))) := by ring
    _ = M * Real.exp (-(2 * Real.pi * (τ.im - y₀))) := by rw [hnum]

/-- A `1`-periodic `g` whose `q`-expansion is holomorphic on the punctured disc, vanishes to
order one at `0` and is bounded by `M` on the circle `|q| = e^{-2π y₀}`, satisfies
`‖g τ‖ ≤ M e^{-4π (im τ - y₀)}` for `im τ ≥ y₀`. -/
theorem periodic_decay_one (g : UpperHalfPlane → ℂ) {y₀ M : ℝ} (hy₀ : 0 < y₀)
    (happ : ∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ)
    (hdiff : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → DifferentiableAt ℂ (qExp g) q)
    (hdiv : DifferentiableAt ℂ (Function.update (fun q : ℂ => q⁻¹ * qExp g q) 0 0) 0)
    (hbdy : ∀ τ : UpperHalfPlane, τ.im = y₀ → |τ.re| ≤ 1 / 2 → ‖g τ‖ ≤ M) :
    ∀ τ : UpperHalfPlane, y₀ ≤ τ.im →
      ‖g τ‖ ≤ M * Real.exp (-(2 * Real.pi * 2 * (τ.im - y₀))) := by
  have hR : 0 < Real.exp (-(2 * Real.pi * y₀)) := Real.exp_pos _
  have hR1 : Real.exp (-(2 * Real.pi * y₀)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hy₀]
  have hsphere : ∀ q : ℂ, ‖q‖ = Real.exp (-(2 * Real.pi * y₀)) → ‖qExp g q‖ ≤ M :=
    qExp_sphere_bound g hy₀ happ hbdy
  have hd1 : DifferentiableOn ℂ
      (Function.update (fun q : ℂ => q⁻¹ * qExp g q) 0 0) (ball 0 1) := by
    intro q hq
    rw [mem_ball, dist_zero_right] at hq
    rcases eq_or_ne q 0 with rfl | hq0
    · exact hdiv.differentiableWithinAt
    · have h1 : DifferentiableAt ℂ (fun q : ℂ => q⁻¹ * qExp g q) q :=
        (differentiableAt_inv hq0).mul (hdiff q (norm_pos_iff.mpr hq0) hq)
      have h2 : Function.update (fun q : ℂ => q⁻¹ * qExp g q) 0 0 =ᶠ[𝓝 q]
          (fun q : ℂ => q⁻¹ * qExp g q) := by
        filter_upwards [isOpen_ne.mem_nhds hq0] with x hx
        rw [Function.update_of_ne hx]
      exact (h1.congr_of_eventuallyEq h2).differentiableWithinAt
  have hG0 : Function.update (fun q : ℂ => q⁻¹ * qExp g q) 0 0 0 = 0 :=
    Function.update_self 0 0 _
  have hN : ∀ q : ℂ, ‖q‖ = Real.exp (-(2 * Real.pi * y₀)) →
      ‖Function.update (fun q : ℂ => q⁻¹ * qExp g q) 0 0 q‖
        ≤ M / Real.exp (-(2 * Real.pi * y₀)) := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, norm_zero] at hq
      exact absurd hq.symm hR.ne'
    rw [Function.update_of_ne hq0, norm_mul, norm_inv, hq, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hsphere q hq) hR.le
  have hkey := norm_le_of_sphere hR hR1 hd1 hG0 hN
  intro τ hτ
  have hqnorm : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Function.Periodic.norm_qParam]; norm_num
  have hle : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ Real.exp (-(2 * Real.pi * y₀)) := by
    rw [hqnorm]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h := hkey _ hle
  have hq0 : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hGq : Function.update (fun q : ℂ => q⁻¹ * qExp g q) 0 0
        (Function.Periodic.qParam 1 (τ : ℂ))
      = (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ * g τ := by
    rw [Function.update_of_ne hq0, happ τ]
  rw [hGq, norm_mul, norm_inv, hqnorm, inv_mul_eq_div] at h
  have hpos : 0 < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  rw [div_le_iff₀ hpos] at h
  have hnum : (Real.exp (-(2 * Real.pi * τ.im)) / Real.exp (-(2 * Real.pi * y₀))) ^ 2
      = Real.exp (-(2 * Real.pi * 2 * (τ.im - y₀))) := by
    rw [div_pow, sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  calc ‖g τ‖
      ≤ ((M / Real.exp (-(2 * Real.pi * y₀))) * Real.exp (-(2 * Real.pi * τ.im))
          / Real.exp (-(2 * Real.pi * y₀))) * Real.exp (-(2 * Real.pi * τ.im)) := h
    _ = M * ((Real.exp (-(2 * Real.pi * τ.im)) / Real.exp (-(2 * Real.pi * y₀))) ^ 2) := by ring
    _ = M * Real.exp (-(2 * Real.pi * 2 * (τ.im - y₀))) := by rw [hnum]


/-! ## 4. Two elementary limits -/

/-- `(y+1) e^{-cy} → 0` as `y → ∞`, for `c > 0`. -/
lemma tendsto_add_one_mul_exp_neg (c : ℝ) (hc : 0 < c) :
    Tendsto (fun y : ℝ => (y + 1) * Real.exp (-(c * y))) atTop (𝓝 0) := by
  have hc' : Tendsto (fun y : ℝ => c * y) atTop atTop := tendsto_id.const_mul_atTop hc
  have h1 : Tendsto (fun y : ℝ => (c * y) * Real.exp (-(c * y))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hc'
    exact h.congr' (Filter.Eventually.of_forall fun y => by
      simp [Function.comp_apply])
  have h2 : Tendsto (fun y : ℝ => Real.exp (-(c * y))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hc'
  have h3 : Tendsto (fun y : ℝ =>
      ((c * y) * Real.exp (-(c * y)) + c * Real.exp (-(c * y))) / c) atTop (𝓝 0) := by
    have h := (h1.add (h2.const_mul c)).div_const c
    simpa using h
  refine h3.congr' (Filter.Eventually.of_forall fun y => ?_)
  rw [div_eq_iff hc.ne']
  ring

/-- The `∃Y` form of the previous limit, with a constant factor `M ≥ 0`. -/
lemma eventually_add_one_mul_exp_le (c M ε : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → (y + 1) * (M * Real.exp (-(c * y))) ≤ ε := by
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · exact ⟨0, fun y _ => by rw [← hM0]; simp only [zero_mul, mul_zero]; exact hε.le⟩
  · have hlim := tendsto_add_one_mul_exp_neg c hc
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨Y, hY⟩ := hlim (ε / M) (by positivity)
    refine ⟨max Y 0, fun y hy => ?_⟩
    have hy0 : (0 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
    have hY' : Y ≤ y := le_trans (le_max_left _ _) hy
    have h := hY y hY'
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_nonneg _))] at h
    calc (y + 1) * (M * Real.exp (-(c * y))) = M * ((y + 1) * Real.exp (-(c * y))) := by ring
      _ ≤ M * (ε / M) := le_of_lt (mul_lt_mul_of_pos_left h hMpos)
      _ = ε := by field_simp

/-- A family of complex numbers whose norms are eventually `≤ ε` for every `ε > 0` tends to `0`. -/
lemma tendsto_zero_of_eventually_norm_le {f : ℝ → ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → ‖f y‖ ≤ ε) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Y, hY⟩ := h (ε / 2) (by linarith)
  refine ⟨Y, fun y hy => ?_⟩
  rw [dist_eq_norm, sub_zero]
  exact lt_of_le_of_lt (hY y hy) (by linarith)

/-- `qParam 1 (1/2 + iy) = - e^{-2πy}`. -/
lemma qParam_one_half_add (y : ℝ) :
    Function.Periodic.qParam 1 (((1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I)
      = -((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ) := by
  rw [Function.Periodic.qParam]
  have hmain : (2 : ℂ) * ↑Real.pi * Complex.I * (((1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I)
        / ((1 : ℝ) : ℂ)
      = ((Real.pi : ℂ) * Complex.I) + ((-(2 * Real.pi * y) : ℝ) : ℂ) := by
    rw [Complex.ofReal_one, div_one]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hmain, Complex.exp_add, Complex.exp_pi_mul_I, Complex.ofReal_exp]
  ring

/-! ## 5. The growth of the `q`-expansion and the facts at `q = 0` -/

/-- The `q`-expansion of a `1`-periodic holomorphic function of moderate growth grows at most like
a power of `|log ‖q‖|` near `q = 0`. -/
lemma qExp_logGrowth (g : UpperHalfPlane → ℂ)
    (happ : ∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ)
    {y₀ Ke A : ℝ} (hy₀ : 0 < y₀) (hKe : 0 ≤ Ke) (hA : 0 ≤ A)
    (hgrow : ∀ τ : UpperHalfPlane, y₀ ≤ τ.im → ‖g τ‖ ≤ Ke * (1 + ‖(τ : ℂ)‖) ^ A) :
    ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ ≤ Real.exp (-(2 * Real.pi * y₀)) →
      ‖qExp g q‖ ≤ Ke * 2 ^ A * (1 + |Real.log ‖q‖|) ^ A := by
  intro q hq0 hqR
  have hR1 : Real.exp (-(2 * Real.pi * y₀)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hy₀]
  have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hqR hR1
  have hqne : q ≠ 0 := norm_pos_iff.mp hq0
  have hzpos : 0 < (Function.Periodic.invQParam 1 q).im := invQParam_one_im_pos q hq0 hq1
  set τ : UpperHalfPlane := ⟨Function.Periodic.invQParam 1 q, hzpos⟩ with hτ
  have hqparam : Function.Periodic.qParam 1 (τ : ℂ) = q := by
    rw [hτ, UpperHalfPlane.coe_mk]
    exact Function.Periodic.qParam_right_inv one_ne_zero hqne
  have him : y₀ ≤ τ.im := by
    rw [hτ, UpperHalfPlane.mk_im, Function.Periodic.im_invQParam]
    have hlog : Real.log ‖q‖ ≤ -(2 * Real.pi * y₀) := by
      have h := Real.log_le_log hq0 hqR
      rwa [Real.log_exp] at h
    rw [show (-(1 : ℝ)) / (2 * Real.pi) * Real.log ‖q‖
        = -(Real.log ‖q‖) / (2 * Real.pi) by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith
  have hFq : qExp g q = g τ := by rw [← hqparam]; exact happ τ
  rw [hFq]
  refine le_trans (hgrow τ him) ?_
  -- norm of `invQParam 1 q` in terms of `log ‖q‖`
  have hlogdec : Complex.log q = (Real.log ‖q‖ : ℂ) + (q.arg : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re, Complex.add_re, Complex.mul_re]
    · simp [Complex.log_im, Complex.add_im, Complex.mul_im]
  have hlog1 : ‖Complex.log q‖ ≤ |Real.log ‖q‖| + |q.arg| := by
    rw [hlogdec]
    refine le_trans (norm_add_le _ _) (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, mul_one]
    simp
  have hlog2 : |q.arg| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨le_of_lt (Complex.neg_pi_lt_arg q), Complex.arg_le_pi q⟩
  have hnorm : ‖Function.Periodic.invQParam 1 q‖ = ‖Complex.log q‖ / (2 * Real.pi) := by
    have h1 : Function.Periodic.invQParam 1 q
        = Complex.log q / ((((2 : ℝ) * Real.pi : ℝ)) * Complex.I : ℂ) := by
      rw [Function.Periodic.invQParam]
      field_simp
      push_cast
      ring
    rw [h1, norm_div, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos Real.pi_pos]
  have hinv : ‖Function.Periodic.invQParam 1 q‖ ≤ (|Real.log ‖q‖| + Real.pi) / (2 * Real.pi) := by
    rw [hnorm]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have htau : ‖(τ : ℂ)‖ ≤ (|Real.log ‖q‖| + Real.pi) / (2 * Real.pi) := by
    simpa [hτ] using hinv
  have hpile : Real.pi / (2 * Real.pi) = 1 / 2 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]; ring
  have h3 : (|Real.log ‖q‖| + Real.pi) / (2 * Real.pi)
      = |Real.log ‖q‖| / (2 * Real.pi) + 1 / 2 := by
    rw [add_div, hpile]
  have h4 : |Real.log ‖q‖| / (2 * Real.pi) ≤ |Real.log ‖q‖| := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three, abs_nonneg (Real.log ‖q‖)]
  have h5 : 1 + ‖(τ : ℂ)‖ ≤ 2 * (1 + |Real.log ‖q‖|) := by
    have h3' := h3
    rw [h3'] at htau
    nlinarith [Real.pi_gt_three, abs_nonneg (Real.log ‖q‖)]
  have h6 : (1 + ‖(τ : ℂ)‖) ^ A ≤ (2 * (1 + |Real.log ‖q‖|)) ^ A :=
    Real.rpow_le_rpow (by positivity) h5 hA
  have h7 : (2 * (1 + |Real.log ‖q‖|)) ^ A = 2 ^ A * (1 + |Real.log ‖q‖|) ^ A :=
    Real.mul_rpow (by norm_num) (by positivity)
  calc Ke * (1 + ‖(τ : ℂ)‖) ^ A ≤ Ke * (2 * (1 + |Real.log ‖q‖|)) ^ A :=
        mul_le_mul_of_nonneg_left h6 hKe
    _ = Ke * (2 ^ A * (1 + |Real.log ‖q‖|) ^ A) := by rw [h7]
    _ = Ke * 2 ^ A * (1 + |Real.log ‖q‖|) ^ A := by ring

/-- The ray estimates for `qExp g` from unweighted decay on `re τ = -1/2`. -/
lemma qExp_ray0 (g : UpperHalfPlane → ℂ)
    (hper : ∀ τ : UpperHalfPlane, g ((1 : ℝ) +ᵥ τ) = g τ)
    (happ : ∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ)
    {hline : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 → Y ≤ τ.im →
      ‖g τ‖ ≤ ε} :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      ‖qExp g (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))‖ ≤ ε := by
  intro ε hε
  obtain ⟨Y₀, hY₀⟩ := hline ε hε
  refine ⟨max Y₀ 1, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hY' : Y₀ ≤ y := le_trans (le_max_left _ _) hy
  have hz1 : 0 < (((1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I).im := by
    simpa [Complex.add_im, Complex.mul_im] using hy0
  have hz2 : 0 < (((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I).im := by
    simpa [Complex.add_im, Complex.mul_im] using hy0
  have hper2 : (⟨(((1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz1⟩ : UpperHalfPlane)
      = (1 : ℝ) +ᵥ (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane) := by
    ext
    rw [UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have heq : qExp g (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))
      = g (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane) := by
    rw [← qParam_one_half_add y,
      ← UpperHalfPlane.coe_mk (((1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I) hz1, happ, hper2, hper]
  rw [heq]
  exact hY₀ _ (by simp) (by simpa using hY')

/-- The ray estimates for `qExp g` from weighted decay on `re τ = -1/2`. -/
lemma qExp_ray1 (g : UpperHalfPlane → ℂ)
    (hper : ∀ τ : UpperHalfPlane, g ((1 : ℝ) +ᵥ τ) = g τ)
    (happ : ∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ)
    {hline : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 → Y ≤ τ.im →
      ‖g τ‖ * Real.exp (2 * Real.pi * τ.im) ≤ ε} :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      ‖qExp g (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))‖
        ≤ ε * Real.exp (-(2 * Real.pi * y)) := by
  intro ε hε
  obtain ⟨Y₀, hY₀⟩ := hline ε hε
  refine ⟨max Y₀ 1, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hY' : Y₀ ≤ y := le_trans (le_max_left _ _) hy
  have hz1 : 0 < (((1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I).im := by
    simpa [Complex.add_im, Complex.mul_im] using hy0
  have hz2 : 0 < (((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I).im := by
    simpa [Complex.add_im, Complex.mul_im] using hy0
  have hper2 : (⟨(((1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz1⟩ : UpperHalfPlane)
      = (1 : ℝ) +ᵥ (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane) := by
    ext
    rw [UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have heq : qExp g (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))
      = g (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane) := by
    rw [← qParam_one_half_add y,
      ← UpperHalfPlane.coe_mk (((1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I) hz1, happ, hper2, hper]
  rw [heq]
  have him : (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane).im = y := by
    simp [Complex.add_im, Complex.mul_im]
  have h := hY₀ (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane)
    (by simp) (by rw [him]; exact hY')
  rw [him] at h
  have hexp : Real.exp (-(2 * Real.pi * y)) * Real.exp (2 * Real.pi * y) = 1 := by
    rw [← Real.exp_add, add_comm, add_neg_cancel, Real.exp_zero]
  calc ‖g (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane)‖
      = ‖g (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane)‖
          * (Real.exp (-(2 * Real.pi * y)) * Real.exp (2 * Real.pi * y)) := by rw [hexp, mul_one]
    _ = (‖g (⟨(((-1 : ℝ) / 2 : ℂ) + (y : ℂ) * Complex.I), hz2⟩ : UpperHalfPlane)‖
          * Real.exp (2 * Real.pi * y)) * Real.exp (-(2 * Real.pi * y)) := by ring
    _ ≤ ε * Real.exp (-(2 * Real.pi * y)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)

/-- The basic facts at `q = 0` for the `q`-expansion of a `1`-periodic holomorphic `g` of moderate
growth with unweighted decay along `re τ = -1/2`:  `qExp g` is holomorphic on the punctured unit
disc, extends holomorphically to `0`, and the extension vanishes there. -/
theorem cusp_facts0 (g : UpperHalfPlane → ℂ)
    (hper : ∀ τ : UpperHalfPlane, g ((1 : ℝ) +ᵥ τ) = g τ)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g)
    {Ke A : ℝ} (hKe : 0 ≤ Ke) (hA : 0 ≤ A)
    (hgrow : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im → ‖g τ‖ ≤ Ke * (1 + ‖(τ : ℂ)‖) ^ A)
    (hline0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 → Y ≤ τ.im →
      ‖g τ‖ ≤ ε) :
    (∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ) ∧
    (∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → DifferentiableAt ℂ (qExp g) q) ∧
    DifferentiableAt ℂ
      (Function.update (qExp g) 0 ((nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g))) 0 ∧
    (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g) = 0 := by
  obtain ⟨_, _, _, happ, hdiff⟩ := qExp_basic g hper hhol
  have hR : 0 < Real.exp (-(2 * Real.pi * (3 / 2))) := Real.exp_pos _
  have hR1 : Real.exp (-(2 * Real.pi * (3 / 2))) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hlog := qExp_logGrowth g happ (y₀ := 3 / 2) (by norm_num) hKe hA
    (by intro τ hτ; exact hgrow τ hτ)
  have hG : DifferentiableOn ℂ (qExp g)
      (Metric.ball 0 (Real.exp (-(2 * Real.pi * (3 / 2)))) \ {0}) := by
    intro q hq
    have hqlt : ‖q‖ < Real.exp (-(2 * Real.pi * (3 / 2))) := by
      simpa [Metric.mem_ball, dist_zero_right] using hq.1
    have hqne : q ≠ 0 := by simpa using hq.2
    exact (hdiff q (norm_pos_iff.mpr hqne) (lt_of_lt_of_le hqlt hR1.le)).differentiableWithinAt
  have hgr : ∀ q : ℂ, q ≠ 0 → ‖q‖ < Real.exp (-(2 * Real.pi * (3 / 2))) →
      ‖qExp g q‖ ≤ Ke * 2 ^ A * (1 + |Real.log ‖q‖|) ^ A := by
    intro q hqne hq
    exact hlog q (norm_pos_iff.mpr hqne) hq.le
  obtain ⟨hTend, h0⟩ := cusp_removable_update (G := qExp g)
    (ρ := Real.exp (-(2 * Real.pi * (3 / 2)))) (C := Ke * 2 ^ A) (N := A)
    hR (by positivity) hA hG hgr
  have hray0 := qExp_ray0 g hper happ (hline := hline0)
  have hval : (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g) = 0 :=
    tendsto_nhds_unique (hTend.comp cuspRay_tendsto)
      (tendsto_zero_of_eventually_norm_le (by
        intro ε hε
        obtain ⟨Y, hY⟩ := hray0 ε hε
        exact ⟨Y, fun y hy => by simpa [cuspRay] using hY y hy⟩))
  exact ⟨happ, hdiff, h0, hval⟩

/-- The facts at `q = 0` for `qExp g`, including the vanishing of the first `q`-coefficient, from
weighted decay along `re τ = -1/2`. -/
theorem cusp_facts1 (g : UpperHalfPlane → ℂ)
    (hper : ∀ τ : UpperHalfPlane, g ((1 : ℝ) +ᵥ τ) = g τ)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g)
    {Ke A : ℝ} (hKe : 0 ≤ Ke) (hA : 0 ≤ A)
    (hgrow : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im → ‖g τ‖ ≤ Ke * (1 + ‖(τ : ℂ)‖) ^ A)
    (hline0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 → Y ≤ τ.im →
      ‖g τ‖ ≤ ε)
    (hline1 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 → Y ≤ τ.im →
      ‖g τ‖ * Real.exp (2 * Real.pi * τ.im) ≤ ε) :
    (∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ) ∧
    (∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → DifferentiableAt ℂ (qExp g) q) ∧
    DifferentiableAt ℂ
      (Function.update (qExp g) 0 ((nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g))) 0 ∧
    (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).limUnder (qExp g) = 0 ∧
    DifferentiableAt ℂ (Function.update (fun q : ℂ => q⁻¹ * qExp g q) 0 0) 0 := by
  obtain ⟨_, _, _, happ, hdiff⟩ := qExp_basic g hper hhol
  have hlog := qExp_logGrowth g happ (y₀ := 3 / 2) (by norm_num) hKe hA
    (by intro τ hτ; exact hgrow τ hτ)
  have hgr : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ ≤ Real.exp (-(2 * Real.pi * (3 / 2))) →
      ‖qExp g q‖ ≤ Ke * 2 ^ A * (1 + |Real.log ‖q‖|) ^ A :=
    fun q hq0 hq => hlog q hq0 hq
  have hray1 := qExp_ray1 g hper happ (hline := hline1)
  have hray0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      ‖qExp g (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))‖ ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hray1 ε hε
    refine ⟨max Y 0, fun y hy => ?_⟩
    have hy0 : (0 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
    have h := hY y (le_trans (le_max_left _ _) hy)
    have hexp : Real.exp (-(2 * Real.pi * y)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hy0]
    calc ‖qExp g (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))‖
        ≤ ε * Real.exp (-(2 * Real.pi * y)) := h
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hexp hε.le
      _ = ε := mul_one ε
  obtain ⟨h0, hval, hdiv⟩ := cusp_at_zero (ℓ := Real.exp (-(2 * Real.pi * (3 / 2)))) hA
    (Real.exp_pos _) hdiff hgr hray0 hray1
  exact ⟨happ, hdiff, h0, hval, hdiv⟩

/-! ## 7. Line decay of the two shifts, and the combination step -/

/-- The decay of `f` on the two lines propagates to `shiftB f`. -/
lemma shiftB_line_decay (f : UpperHalfPlane → ℂ) {ρ : ℕ}
    (hline : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖f τ‖ * Real.exp (2 * Real.pi * (ρ : ℝ) * τ.im) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 → Y ≤ τ.im →
      ‖shiftB f τ‖ * Real.exp (2 * Real.pi * (ρ : ℝ) * τ.im) ≤ ε := by
  intro ε hε
  obtain ⟨Y, hY⟩ := hline (ε / 2) (by linarith)
  refine ⟨Y, fun τ hτre hτY => ?_⟩
  have hre1 : ((1 : ℝ) +ᵥ τ).re = 1 / 2 := by
    show (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ).re = 1 / 2
    rw [UpperHalfPlane.coe_vadd]
    norm_num [hτre]
  have him1 : ((1 : ℝ) +ᵥ τ).im = τ.im := by
    show (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ).im = τ.im
    rw [UpperHalfPlane.coe_vadd]
    simp
  have h1 := hY ((1 : ℝ) +ᵥ τ) (Or.inl hre1) (by rw [him1]; exact hτY)
  have h2 := hY τ (Or.inr hτre) hτY
  have hB : ‖shiftB f τ‖ ≤ ‖f ((1 : ℝ) +ᵥ τ)‖ + ‖f τ‖ := by
    rw [shiftB]; exact norm_sub_le _ _
  calc ‖shiftB f τ‖ * Real.exp (2 * Real.pi * (ρ : ℝ) * τ.im)
      ≤ (‖f ((1 : ℝ) +ᵥ τ)‖ + ‖f τ‖) * Real.exp (2 * Real.pi * (ρ : ℝ) * τ.im) :=
        mul_le_mul_of_nonneg_right hB (Real.exp_nonneg _)
    _ = ‖f ((1 : ℝ) +ᵥ τ)‖ * Real.exp (2 * Real.pi * (ρ : ℝ) * τ.im)
          + ‖f τ‖ * Real.exp (2 * Real.pi * (ρ : ℝ) * τ.im) := by ring
    _ ≤ ε / 2 + ε / 2 := add_le_add (by simpa [him1] using h1) h2
    _ = ε := by ring

/-- The decay of `shiftB f` at rate `c = w + 2π` and the decay of `f` with weight `w` together give
the decay of `shiftA f` with weight `w`. -/
lemma shiftA_line_decay (f : UpperHalfPlane → ℂ) {c w MB : ℝ} (hcw : c - w = 2 * Real.pi)
    (hMB : 0 ≤ MB)
    (hBdecay : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
      ‖shiftB f τ‖ ≤ MB * Real.exp (-(c * (τ.im - 3 / 2))))
    (hline : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im → ‖f τ‖ * Real.exp (w * τ.im) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 → Y ≤ τ.im →
      ‖shiftA f τ‖ * Real.exp (w * τ.im) ≤ ε := by
  intro ε hε
  obtain ⟨Y₁, hY₁⟩ := hline (ε / 2) (by linarith)
  obtain ⟨Y₂, hY₂⟩ := eventually_add_one_mul_exp_le (c - w) (MB * Real.exp (c * (3 / 2)))
    (ε / 2) (by rw [hcw]; positivity) (by positivity) (by linarith)
  refine ⟨max Y₁ (max Y₂ (3 / 2)), fun τ hτre hτY => ?_⟩
  have hY₁' : Y₁ ≤ τ.im := le_trans (le_max_left _ _) hτY
  have hY₂' : Y₂ ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hτY)
  have h3 : (3 / 2 : ℝ) ≤ τ.im := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτY)
  have hnormτ : ‖(τ : ℂ)‖ ≤ τ.im + 1 := by
    have h := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h
    have hre : |τ.re| ≤ 1 / 2 := by rw [hτre]; norm_num
    linarith
  have hB2 : ‖shiftB f τ‖ * Real.exp (w * τ.im)
      ≤ MB * Real.exp (c * (3 / 2)) * Real.exp (-((c - w) * τ.im)) := by
    have hexp : Real.exp (-(c * (τ.im - 3 / 2))) * Real.exp (w * τ.im)
        = Real.exp (c * (3 / 2)) * Real.exp (-((c - w) * τ.im)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1 <;> ring
    calc ‖shiftB f τ‖ * Real.exp (w * τ.im)
        ≤ (MB * Real.exp (-(c * (τ.im - 3 / 2)))) * Real.exp (w * τ.im) :=
          mul_le_mul_of_nonneg_right (hBdecay τ h3) (Real.exp_nonneg _)
      _ = MB * (Real.exp (-(c * (τ.im - 3 / 2))) * Real.exp (w * τ.im)) := by ring
      _ = MB * (Real.exp (c * (3 / 2)) * Real.exp (-((c - w) * τ.im))) := by rw [hexp]
      _ = MB * Real.exp (c * (3 / 2)) * Real.exp (-((c - w) * τ.im)) := by ring
  have h6 : ‖(τ : ℂ)‖ * (‖shiftB f τ‖ * Real.exp (w * τ.im))
      ≤ (τ.im + 1) * (MB * Real.exp (c * (3 / 2)) * Real.exp (-((c - w) * τ.im))) :=
    mul_le_mul hnormτ hB2 (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)) (by linarith)
  have hA : ‖shiftA f τ‖ * Real.exp (w * τ.im)
      ≤ (‖f τ‖ + ‖(τ : ℂ)‖ * ‖shiftB f τ‖) * Real.exp (w * τ.im) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    calc ‖shiftA f τ‖ = ‖f τ - (τ : ℂ) * shiftB f τ‖ := by rw [shiftA]
      _ ≤ ‖f τ‖ + ‖(τ : ℂ) * shiftB f τ‖ := norm_sub_le _ _
      _ = ‖f τ‖ + ‖(τ : ℂ)‖ * ‖shiftB f τ‖ := by rw [norm_mul]
  have hf := hY₁ τ (Or.inr hτre) hY₁'
  have hlim := hY₂ τ.im hY₂'
  have hexpand : (‖f τ‖ + ‖(τ : ℂ)‖ * ‖shiftB f τ‖) * Real.exp (w * τ.im)
      = ‖f τ‖ * Real.exp (w * τ.im)
        + ‖(τ : ℂ)‖ * (‖shiftB f τ‖ * Real.exp (w * τ.im)) := by ring
  rw [hexpand] at hA
  linarith

/-- The combination step:  `f = shiftA f + τ · shiftB f`, and the two exponential decay
estimates give the decay of `f` with the extra factor `1 + ‖τ‖`. -/
lemma norm_f_le_of_decay (f : UpperHalfPlane → ℂ) (ρ : ℕ) {MA MB : ℝ} (hMA : 0 ≤ MA)
    (hMB : 0 ≤ MB)
    (hdecomp : ∀ τ : UpperHalfPlane, f τ = shiftA f τ + (τ : ℂ) * shiftB f τ)
    (hAdecay : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
      ‖shiftA f τ‖ ≤ MA * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * (τ.im - 3 / 2))))
    (hBdecay : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
      ‖shiftB f τ‖ ≤ MB * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * (τ.im - 3 / 2)))) :
    ∀ τ : UpperHalfPlane, -1 ≤ τ.re → τ.re ≤ 1 → 2 ≤ τ.im →
      ‖f τ‖ ≤ (MA + MB) * Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2)) * (1 + ‖(τ : ℂ)‖) *
        Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im)) := by
  intro τ _ _ hy
  have h3 : (3 / 2 : ℝ) ≤ τ.im := by linarith
  have hA := hAdecay τ h3
  have hB := hBdecay τ h3
  have hexp : Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * (τ.im - 3 / 2)))
      = Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
        * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hA' : ‖shiftA f τ‖
      ≤ MA * (Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
          * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im))) := by
    rw [← hexp]; exact hA
  have hB' : ‖shiftB f τ‖
      ≤ MB * (Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
          * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im))) := by
    rw [← hexp]; exact hB
  have hEpos : 0 < Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
      * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im)) := by positivity
  have hτnn : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have hcomb : ‖shiftA f τ‖ + ‖(τ : ℂ)‖ * ‖shiftB f τ‖
      ≤ (MA + MB) * (Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
          * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im))) * (1 + ‖(τ : ℂ)‖) := by
    have h1 : ‖(τ : ℂ)‖ * ‖shiftB f τ‖
        ≤ ‖(τ : ℂ)‖ * (MB * (Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
            * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im)))) :=
      mul_le_mul_of_nonneg_left hB' hτnn
    have h2 : 0 ≤ MA * (Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
            * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im))) * ‖(τ : ℂ)‖ :=
      mul_nonneg (mul_nonneg hMA hEpos.le) hτnn
    have h3 : 0 ≤ MB * (Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
            * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im))) :=
      mul_nonneg hMB hEpos.le
    nlinarith [hA', h1, h2, h3]
  calc ‖f τ‖ = ‖shiftA f τ + (τ : ℂ) * shiftB f τ‖ := by rw [hdecomp τ]
    _ ≤ ‖shiftA f τ‖ + ‖(τ : ℂ) * shiftB f τ‖ := norm_add_le _ _
    _ = ‖shiftA f τ‖ + ‖(τ : ℂ)‖ * ‖shiftB f τ‖ := by rw [norm_mul]
    _ ≤ (MA + MB) * (Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2))
          * Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im))) * (1 + ‖(τ : ℂ)‖) := hcomb
    _ = (MA + MB) * Real.exp (2 * Real.pi * ((ρ : ℝ) + 1) * (3 / 2)) * (1 + ‖(τ : ℂ)‖) *
        Real.exp (-(2 * Real.pi * ((ρ : ℝ) + 1) * τ.im)) := by ring

/-! ## 8. The two cases `m = 1` and `m = 2`, and the target theorem -/

/-- The target estimate in the case `m = 1` (weight `ρ = 0`). -/
theorem strip_decay_zero (f : UpperHalfPlane → ℂ)
    (hT2 : ∀ τ : UpperHalfPlane, Work.Kernels.T2op f τ = 0)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f)
    {KeB AB KeA AA MB MA : ℝ} (hKeB : 0 ≤ KeB) (hAB : 0 ≤ AB) (hKeA : 0 ≤ KeA) (hAA : 0 ≤ AA)
    (hMB : 0 ≤ MB) (hMA : 0 ≤ MA)
    (hBgrow : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im → ‖shiftB f τ‖ ≤ KeB * (1 + ‖(τ : ℂ)‖) ^ AB)
    (hAgrow : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im → ‖shiftA f τ‖ ≤ KeA * (1 + ‖(τ : ℂ)‖) ^ AA)
    (hBseg : ∀ τ : UpperHalfPlane, τ.im = 3 / 2 → |τ.re| ≤ 1 / 2 → ‖shiftB f τ‖ ≤ MB)
    (hAseg : ∀ τ : UpperHalfPlane, τ.im = 3 / 2 → |τ.re| ≤ 1 / 2 → ‖shiftA f τ‖ ≤ MA)
    (hline : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im → ‖f τ‖ ≤ ε) :
    ∀ τ : UpperHalfPlane, -1 ≤ τ.re → τ.re ≤ 1 → 2 ≤ τ.im →
      ‖f τ‖ ≤ (MA + MB) * Real.exp (2 * Real.pi * 1 * (3 / 2)) * (1 + ‖(τ : ℂ)‖) *
        Real.exp (-(2 * Real.pi * 1 * τ.im)) := by
  have hline' : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖f τ‖ * Real.exp (2 * Real.pi * (((1 : ℕ) : ℝ) - 1) * τ.im) ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hline ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  obtain ⟨hBper, hAper, hBmd, hAmd, hdecomp, _⟩ := strip_structure 1 f hT2 hhol hline'
  have hline0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖f τ‖ * Real.exp (2 * Real.pi * ((0 : ℕ) : ℝ) * τ.im) ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hline ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  have hline0w : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im → ‖f τ‖ * Real.exp (0 * τ.im) ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hline0 ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  have hBline0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 →
      Y ≤ τ.im → ‖shiftB f τ‖ ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := shiftB_line_decay f (ρ := 0) hline0 ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  obtain ⟨happB, hdiffB, h0B, hvalB⟩ :=
    cusp_facts0 (shiftB f) hBper hBmd hKeB hAB hBgrow hBline0
  have hBdecay : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
      ‖shiftB f τ‖ ≤ MB * Real.exp (-(2 * Real.pi * 1 * (τ.im - 3 / 2))) := by
    intro τ hτ
    simpa using periodic_decay_zero (shiftB f) (by norm_num : (0 : ℝ) < 3 / 2) happB hdiffB
      h0B hvalB hBseg τ hτ
  have hlineA0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 →
      Y ≤ τ.im → ‖shiftA f τ‖ ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := shiftA_line_decay f (c := 2 * Real.pi * 1) (w := 0) (MB := MB)
      (by ring) hMB (by intro τ hτ; simpa using hBdecay τ hτ) hline0w ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  obtain ⟨happA, hdiffA, h0A, hvalA⟩ :=
    cusp_facts0 (shiftA f) hAper hAmd hKeA hAA hAgrow hlineA0
  have hAdecay : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
      ‖shiftA f τ‖ ≤ MA * Real.exp (-(2 * Real.pi * 1 * (τ.im - 3 / 2))) := by
    intro τ hτ
    simpa using periodic_decay_zero (shiftA f) (by norm_num : (0 : ℝ) < 3 / 2) happA hdiffA
      h0A hvalA hAseg τ hτ
  have hexp0a : ∀ y : ℝ, Real.exp (2 * Real.pi * (((0 : ℕ) : ℝ) + 1) * y)
      = Real.exp (2 * Real.pi * 1 * y) := by
    intro y; congr 1; push_cast; ring
  have hexp0b : ∀ y : ℝ, Real.exp (-(2 * Real.pi * (((0 : ℕ) : ℝ) + 1) * y))
      = Real.exp (-(2 * Real.pi * 1 * y)) := by
    intro y; congr 1; push_cast; ring
  have hexp0c : ∀ y : ℝ, Real.exp (-(2 * Real.pi * 1 * y))
      = Real.exp (-(2 * Real.pi * (((0 : ℕ) : ℝ) + 1) * y)) := by
    intro y; congr 1; push_cast; ring
  intro τ h1 h2 h3
  have h := norm_f_le_of_decay f 0 hMA hMB hdecomp
    (by intro τ hτ; simpa only [hexp0c] using hAdecay τ hτ)
    (by intro τ hτ; simpa only [hexp0c] using hBdecay τ hτ) τ h1 h2 h3
  simpa only [hexp0a, hexp0b] using h

/-- The target estimate in the case `m = 2` (weight `ρ = 1`). -/
theorem strip_decay_one (f : UpperHalfPlane → ℂ)
    (hT2 : ∀ τ : UpperHalfPlane, Work.Kernels.T2op f τ = 0)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f)
    {KeB AB KeA AA MB MA : ℝ} (hKeB : 0 ≤ KeB) (hAB : 0 ≤ AB) (hKeA : 0 ≤ KeA) (hAA : 0 ≤ AA)
    (hMB : 0 ≤ MB) (hMA : 0 ≤ MA)
    (hBgrow : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im → ‖shiftB f τ‖ ≤ KeB * (1 + ‖(τ : ℂ)‖) ^ AB)
    (hAgrow : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im → ‖shiftA f τ‖ ≤ KeA * (1 + ‖(τ : ℂ)‖) ^ AA)
    (hBseg : ∀ τ : UpperHalfPlane, τ.im = 3 / 2 → |τ.re| ≤ 1 / 2 → ‖shiftB f τ‖ ≤ MB)
    (hAseg : ∀ τ : UpperHalfPlane, τ.im = 3 / 2 → |τ.re| ≤ 1 / 2 → ‖shiftA f τ‖ ≤ MA)
    (hline : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖f τ‖ * Real.exp (2 * Real.pi * τ.im) ≤ ε) :
    ∀ τ : UpperHalfPlane, -1 ≤ τ.re → τ.re ≤ 1 → 2 ≤ τ.im →
      ‖f τ‖ ≤ (MA + MB) * Real.exp (2 * Real.pi * 2 * (3 / 2)) * (1 + ‖(τ : ℂ)‖) *
        Real.exp (-(2 * Real.pi * 2 * τ.im)) := by
  have hline' : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖f τ‖ * Real.exp (2 * Real.pi * (((2 : ℕ) : ℝ) - 1) * τ.im) ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hline ε hε
    refine ⟨Y, fun τ h1 h2 => ?_⟩
    convert hY τ h1 h2 using 2
    norm_num
  obtain ⟨hBper, hAper, hBmd, hAmd, hdecomp, _⟩ := strip_structure 2 f hT2 hhol hline'
  have hline1 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖f τ‖ * Real.exp (2 * Real.pi * ((1 : ℕ) : ℝ) * τ.im) ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hline ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  have hline1w : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖f τ‖ * Real.exp ((2 * Real.pi) * τ.im) ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hline ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  have hBline1 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 →
      Y ≤ τ.im → ‖shiftB f τ‖ * Real.exp (2 * Real.pi * ((1 : ℕ) : ℝ) * τ.im) ≤ ε :=
    shiftB_line_decay f (ρ := 1) hline1
  have hBline0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 →
      Y ≤ τ.im → ‖shiftB f τ‖ ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hBline1 ε hε
    refine ⟨max Y 0, fun τ h1 h2 => ?_⟩
    have hy : 0 ≤ τ.im := le_trans (le_max_right _ _) h2
    have h := hY τ h1 (le_trans (le_max_left _ _) h2)
    calc ‖shiftB f τ‖ = ‖shiftB f τ‖ * 1 := by ring
      _ ≤ ‖shiftB f τ‖ * Real.exp (2 * Real.pi * ((1 : ℕ) : ℝ) * τ.im) :=
          mul_le_mul_of_nonneg_left
            (Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) hy)) (norm_nonneg _)
      _ ≤ ε := h
  have hBline1' : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 →
      Y ≤ τ.im → ‖shiftB f τ‖ * Real.exp (2 * Real.pi * τ.im) ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hBline1 ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  obtain ⟨happB, hdiffB, h0B, hvalB, hdivB⟩ :=
    cusp_facts1 (shiftB f) hBper hBmd hKeB hAB hBgrow hBline0 hBline1'
  have hBdecay : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
      ‖shiftB f τ‖ ≤ MB * Real.exp (-(2 * Real.pi * (((1 : ℕ) : ℝ) + 1) * (τ.im - 3 / 2))) := by
    intro τ hτ
    convert periodic_decay_one (shiftB f) (by norm_num : (0 : ℝ) < 3 / 2) happB hdiffB
      hdivB hBseg τ hτ using 2
    push_cast
    ring_nf
  have hlineA1 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 →
      Y ≤ τ.im → ‖shiftA f τ‖ * Real.exp (2 * Real.pi * τ.im) ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := shiftA_line_decay f (c := 2 * Real.pi * 2) (w := 2 * Real.pi) (MB := MB)
      (by ring) hMB (by intro τ hτ; have h := hBdecay τ hτ; convert h using 2; push_cast; ring_nf)
      hline1w ε hε
    exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
  have hlineA0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, τ.re = -1 / 2 →
      Y ≤ τ.im → ‖shiftA f τ‖ ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hlineA1 ε hε
    refine ⟨max Y 0, fun τ h1 h2 => ?_⟩
    have hy : 0 ≤ τ.im := le_trans (le_max_right _ _) h2
    have h := hY τ h1 (le_trans (le_max_left _ _) h2)
    calc ‖shiftA f τ‖ = ‖shiftA f τ‖ * 1 := by ring
      _ ≤ ‖shiftA f τ‖ * Real.exp (2 * Real.pi * τ.im) :=
          mul_le_mul_of_nonneg_left
            (Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) hy)) (norm_nonneg _)
      _ ≤ ε := h
  obtain ⟨happA, hdiffA, h0A, hvalA, hdivA⟩ :=
    cusp_facts1 (shiftA f) hAper hAmd hKeA hAA hAgrow hlineA0 hlineA1
  have hAdecay : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
      ‖shiftA f τ‖ ≤ MA * Real.exp (-(2 * Real.pi * (((1 : ℕ) : ℝ) + 1) * (τ.im - 3 / 2))) := by
    intro τ hτ
    convert periodic_decay_one (shiftA f) (by norm_num : (0 : ℝ) < 3 / 2) happA hdiffA
      hdivA hAseg τ hτ using 2
    push_cast
    ring_nf
  have hexp1a : ∀ y : ℝ, Real.exp (2 * Real.pi * (((1 : ℕ) : ℝ) + 1) * y)
      = Real.exp (2 * Real.pi * 2 * y) := by
    intro y; congr 1; push_cast; ring
  have hexp1b : ∀ y : ℝ, Real.exp (-(2 * Real.pi * (((1 : ℕ) : ℝ) + 1) * y))
      = Real.exp (-(2 * Real.pi * 2 * y)) := by
    intro y; congr 1; push_cast; ring
  have hexp1c : ∀ y : ℝ, Real.exp (-(2 * Real.pi * 2 * y))
      = Real.exp (-(2 * Real.pi * (((1 : ℕ) : ℝ) + 1) * y)) := by
    intro y; congr 1; push_cast; ring
  intro τ h1 h2 h3
  have h := norm_f_le_of_decay f 1 hMA hMB hdecomp
    (by intro τ hτ; simpa only [hexp1c] using hAdecay τ hτ)
    (by intro τ hτ; simpa only [hexp1c] using hBdecay τ hτ) τ h1 h2 h3
  simpa only [hexp1a, hexp1b] using h

/-- A holomorphic `f` on `ℍ` with `(T-I)²f = 0` and moderate growth `‖f‖ ≤ C scale^N`, whose
product with `e^{2π(m-1) Im τ}` tends to `0` along the two lines `Re τ = ±1/2`, decays like
`(1+|τ|) e^{-2πm Im τ}` on the strip, with a constant depending only on `m`, `C`, `N`. -/
theorem strip_decay_of_line_decay (m : ℕ) (hm : m = 1 ∨ m = 2) (C N : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ f : UpperHalfPlane → ℂ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f →
      (∀ τ : UpperHalfPlane, Work.Kernels.T2op f τ = 0) →
      (∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) →
      (∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane, (τ.re = 1 / 2 ∨ τ.re = -1 / 2) →
        Y ≤ τ.im → ‖f τ‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) ≤ ε) →
      ∀ τ : UpperHalfPlane, -1 ≤ τ.re → τ.re ≤ 1 → 2 ≤ τ.im →
        ‖f τ‖ ≤ C' * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im)) := by
  obtain ⟨KeB, AB, hKeB, hAB, hBgrow⟩ := (strip_constants C N).1
  obtain ⟨KeA, AA, hKeA, hAA, hAgrow⟩ := (strip_constants C N).2.1
  obtain ⟨MB, hMB, hBseg⟩ := (strip_constants C N).2.2.1
  obtain ⟨MA, hMA, hAseg⟩ := (strip_constants C N).2.2.2
  rcases hm with rfl | rfl
  · refine ⟨(MA + MB) * Real.exp (2 * Real.pi * 1 * (3 / 2)), by positivity, ?_⟩
    intro f hhol hT2 hgr hline
    have hline0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im → ‖f τ‖ ≤ ε := by
      intro ε hε
      obtain ⟨Y, hY⟩ := hline ε hε
      exact ⟨Y, fun τ h1 h2 => by simpa using hY τ h1 h2⟩
    simpa using strip_decay_zero f hT2 hhol hKeB hAB hKeA hAA hMB hMA (hBgrow f hgr)
      (hAgrow f hgr) (hBseg f hgr) (hAseg f hgr) hline0
  · refine ⟨(MA + MB) * Real.exp (2 * Real.pi * 2 * (3 / 2)), by positivity, ?_⟩
    intro f hhol hT2 hgr hline
    have hline1 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
        ‖f τ‖ * Real.exp (2 * Real.pi * τ.im) ≤ ε := by
      intro ε hε
      obtain ⟨Y, hY⟩ := hline ε hε
      refine ⟨Y, fun τ h1 h2 => ?_⟩
      convert hY τ h1 h2 using 2
      norm_num
    simpa using strip_decay_one f hT2 hhol hKeB hAB hKeA hAA hMB hMA (hBgrow f hgr)
      (hAgrow f hgr) (hBseg f hgr) (hAseg f hgr) hline1

end Work.CKFinal
