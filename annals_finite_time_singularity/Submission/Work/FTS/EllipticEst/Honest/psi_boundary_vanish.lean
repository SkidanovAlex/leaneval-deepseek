/-
Work module for `Work.FTS.EllipticEst.Honest.psi_boundary_vanish`.

# The boundary terms of the slice integration by parts vanish

For `u : ℝ → ℝ` of class `C²` on the open interval `(0, π/2)` and `ψ = u / cos` (the slice
variable `Work.FTS.EllipticEst.TanTheta.psi`), we prove that the boundary quantities

  `ρ θ · ψ θ²`   and   `ρ θ · ψ' θ²`,      `ρ = sin θ cos θ · sin(2θ)^{-η}` (`η = 99/100`),

tend to `0` at `θ → 0⁺` and at `θ → π/2⁻`, under the honest integrability hypotheses
`∫ ψ² σ < ∞`, `∫ ψ'² σ < ∞`, `∫ (u'')² σ < ∞` (`σ = sin(2θ)^{-η}`).

## The mathematics

On `(0, π/2)` write `s = sin(2θ)`, `σ = s^{-η}`, `ρ = (1/2) s^{1-η} = ((1/2)·sin 2θ)·σ`, and
`ψ = u / cos`.  The two identities behind the proof are

* `(ρ ψ²)' = ρ' ψ² + 2 ρ ψ ψ'`  with `|ρ'| = (1-η)|cos 2θ| σ ≤ (1-η)σ`, so
  `∫ |(ρψ²)'| ≤ (1-η)∫σψ² + ∫ρψ² + ∫ρψ'² < ∞` by the AM–GM inequality `2ab ≤ a²+b²`;
* `cos θ · ψ'' = u'' + 2 sin θ · ψ' + cos θ · ψ` (Leibniz, `u = ψ cos`), so
  `|2ρψ'ψ''| ≤ 2ρ|ψ'||u''|/cos θ + 4ρ tan θ ψ'² + 2ρ|ψ'||ψ|`, and each term is dominated by an
  integrable function: `ρ tan θ = σ sin²θ ≤ σ`,
  `2ρ|ψ'||u''|/cosθ ≤ (1/2)σψ'² + 2σu''²` (weighted AM–GM, using
  `s^{2-η}/cos²θ = 4 sin²θ σ ≤ 4σ`), and `2ρ|ψ'||ψ| ≤ ρψ'² + ρψ² ≤ σψ'² + σψ²`.

Hence `F = ρψ²` and `G = ρψ'²` are nonnegative with integrable derivative on `(0, π/2)`, so
both have finite limits at the endpoints.  A positive limit at an endpoint is impossible: it
forces `ρ ψ² ≥ c > 0` near the endpoint, and since `ρ ≤ tσ` with `t = dist(θ, endpoint)` this
gives `σ ψ² ≥ c/t`, whose integral diverges; this contradicts `∫ σ ψ² < ∞`.  So both limits
are `0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.EllipticEst.TanTheta.wrho_mul_sq_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

open Work.FTS.EllipticEst.TanTheta (psi wrho wrhoD wrho_eq_half_sin_rpow wrho_deriv)

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The angular interval `(0, π/2)` of the slice. -/
local notation "Iθ" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The exponent `η = 99/100` of the paper. -/
local notation "eη" => Work.Spaces.eta

/-! ## Elementary angular facts -/

private lemma pi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]

private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Iθ) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sin_two_le_one {θ : ℝ} (hθ : θ ∈ Iθ) : Real.sin (2 * θ) ≤ 1 :=
  Real.sin_le_one _

private lemma cos_pos {θ : ℝ} (hθ : θ ∈ Iθ) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

private lemma sig_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ AngSecond.sig θ :=
  AngSecond.sig_nonneg ⟨hθ.1.le, hθ.2.le⟩

private lemma sig_pos {θ : ℝ} (hθ : θ ∈ Iθ) : 0 < AngSecond.sig θ :=
  Real.rpow_pos_of_pos (sin_two_pos hθ) _

private lemma continuousOn_wrho : ContinuousOn (wrho eη) Iθ := by
  change ContinuousOn
    (fun θ : ℝ => Real.sin θ * Real.cos θ * (Real.sin (2 * θ)) ^ (-(eη))) Iθ
  refine (Real.continuous_sin.continuousOn.mul Real.continuous_cos.continuousOn).mul ?_
  exact ContinuousOn.rpow_const
    (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2))
    (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))

private lemma continuousOn_wrhoD : ContinuousOn (wrhoD eη) Iθ := by
  change ContinuousOn
    (fun θ : ℝ => (1 - eη) * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(eη))) Iθ
  refine (continuousOn_const.mul
    (Real.continuous_cos.comp_continuousOn (continuousOn_id.const_mul 2))).mul ?_
  exact ContinuousOn.rpow_const
    (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2))
    (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))

/-! ## The algebra of the weight `ρ` against `σ = sin(2θ)^{-η}` -/

/-- On the open interval, `ρ = ((1/2) sin 2θ) · σ`. -/
private lemma wrho_eq_half_sin_mul_sig {θ : ℝ} (hθ : θ ∈ Iθ) :
    wrho eη θ = (1 / 2 * Real.sin (2 * θ)) * AngSecond.sig θ := by
  rw [wrho_eq_half_sin_rpow _ hθ]
  have hs := sin_two_pos hθ
  have h1 : (Real.sin (2 * θ)) ^ (1 - eη)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(eη)) := by
    rw [show 1 - eη = 1 + (-(eη)) by ring, Real.rpow_add hs, Real.rpow_one]
  rw [h1, AngSecond.sig]
  ring

private lemma wrho_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ wrho eη θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (sin_two_pos hθ))) (sig_nonneg hθ)

/-- `ρ > 0` on the open interval. -/
private lemma wrho_pos {θ : ℝ} (hθ : θ ∈ Iθ) : 0 < wrho eη θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  exact mul_pos (mul_pos (by norm_num) (sin_two_pos hθ)) (sig_pos hθ)

/-- `ρ ≤ σ` on the open interval. -/
private lemma wrho_le_sig {θ : ℝ} (hθ : θ ∈ Iθ) : wrho eη θ ≤ AngSecond.sig θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  have hsig := sig_nonneg hθ
  have h : (1 / 2 * Real.sin (2 * θ)) ≤ 1 := by
    have := sin_two_le_one hθ; linarith
  calc (1 / 2 * Real.sin (2 * θ)) * AngSecond.sig θ ≤ 1 * AngSecond.sig θ :=
        mul_le_mul_of_nonneg_right h hsig
    _ = AngSecond.sig θ := one_mul _

/-- `ρ ≤ θ · σ` on the open interval (used as `θ → 0⁺`). -/
private lemma wrho_le_mul_sig_right {θ : ℝ} (hθ : θ ∈ Iθ) :
    wrho eη θ ≤ θ * AngSecond.sig θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  refine mul_le_mul_of_nonneg_right ?_ (sig_nonneg hθ)
  have h2 := Real.sin_le (show (0 : ℝ) ≤ 2 * θ by linarith [hθ.1])
  linarith

/-- `ρ ≤ (π/2 - θ) · σ` on the open interval (used as `θ → π/2⁻`). -/
private lemma wrho_le_mul_sig_left {θ : ℝ} (hθ : θ ∈ Iθ) :
    wrho eη θ ≤ (Real.pi / 2 - θ) * AngSecond.sig θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  refine mul_le_mul_of_nonneg_right ?_ (sig_nonneg hθ)
  have h0 : (0 : ℝ) ≤ Real.pi - 2 * θ := by linarith [hθ.2]
  have h2 := Real.sin_le h0
  rw [Real.sin_pi_sub] at h2
  linarith

/-- `ρ · tan θ ≤ σ` on the open interval. -/
private lemma wrho_mul_tan_le_sig {θ : ℝ} (hθ : θ ∈ Iθ) :
    wrho eη θ * (Real.sin θ / Real.cos θ) ≤ AngSecond.sig θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  have hsig := sig_pos hθ
  have hc : Real.cos θ ≠ 0 := ne_of_gt (cos_pos hθ)
  have hkey : (1 / 2 * Real.sin (2 * θ)) * (Real.sin θ / Real.cos θ) = (Real.sin θ) ^ 2 := by
    rw [Real.sin_two_mul]
    field_simp
  calc ((1 / 2 * Real.sin (2 * θ)) * AngSecond.sig θ) * (Real.sin θ / Real.cos θ)
      = ((1 / 2 * Real.sin (2 * θ)) * (Real.sin θ / Real.cos θ)) * AngSecond.sig θ := by ring
    _ = (Real.sin θ) ^ 2 * AngSecond.sig θ := by rw [hkey]
    _ ≤ 1 * AngSecond.sig θ :=
        mul_le_mul_of_nonneg_right (Real.sin_sq_le_one θ) hsig.le
    _ = AngSecond.sig θ := one_mul _

/-- `|ρ'| ≤ (1-η) σ`. -/
private lemma abs_wrhoD_le_sig {θ : ℝ} (hθ : θ ∈ Iθ) :
    |wrhoD eη θ| ≤ (1 - eη) * AngSecond.sig θ := by
  change |(1 - eη) * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(eη))|
      ≤ (1 - eη) * AngSecond.sig θ
  rw [AngSecond.sig]
  have h1 : 0 ≤ 1 - eη := by linarith [Work.Spaces.eta_lt_one]
  have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(eη)) :=
    (Real.rpow_pos_of_pos (sin_two_pos hθ) _).le
  rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
  have h3 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  calc (1 - eη) * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(eη))
      ≤ (1 - eη) * 1 * (Real.sin (2 * θ)) ^ (-(eη)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 h1) h2
    _ = (1 - eη) * (Real.sin (2 * θ)) ^ (-(eη)) := by ring

/-- `sin(2θ)^{2-η} = sin(2θ)² σ`. -/
private lemma sin_two_pow_two_sub_eta_eq {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ (2 - eη)
      = (Real.sin (2 * θ)) ^ 2 * AngSecond.sig θ := by
  have hs := sin_two_pos hθ
  rw [show (2 : ℝ) - eη = 2 + (-(eη)) by ring, Real.rpow_add hs, Real.rpow_two, pow_two,
    AngSecond.sig]

/-- `sin(2θ)^{2-η} / cos²θ ≤ 4 σ` on the open interval. -/
private lemma sin_two_pow_two_sub_eta_div_cos_sq_le {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ (2 - eη) / (Real.cos θ) ^ 2 ≤ 4 * AngSecond.sig θ := by
  rw [sin_two_pow_two_sub_eta_eq hθ]
  have hc := cos_pos hθ
  have hcs : 0 < (Real.cos θ) ^ 2 := sq_pos_of_pos hc
  rw [div_le_iff₀ hcs]
  have hsig := sig_nonneg hθ
  have hs2 : (Real.sin (2 * θ)) ^ 2 = 4 * (Real.sin θ) ^ 2 * (Real.cos θ) ^ 2 := by
    rw [Real.sin_two_mul]; ring
  rw [hs2]
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hX : 0 ≤ (Real.cos θ) ^ 2 * AngSecond.sig θ := mul_nonneg hcs.le hsig
  calc 4 * (Real.sin θ) ^ 2 * (Real.cos θ) ^ 2 * AngSecond.sig θ
      = 4 * ((Real.cos θ) ^ 2 * AngSecond.sig θ) * (Real.sin θ) ^ 2 := by ring
    _ ≤ 4 * ((Real.cos θ) ^ 2 * AngSecond.sig θ) * 1 :=
        mul_le_mul_of_nonneg_left hsin (by linarith)
    _ = 4 * AngSecond.sig θ * (Real.cos θ) ^ 2 := by ring

/-- The weighted AM–GM inequality for the mixed term `2ρ|A|(|B|/cos θ)`. -/
private lemma two_wrho_mul_le {θ : ℝ} (hθ : θ ∈ Iθ) (A B : ℝ) :
    2 * wrho eη θ * |A| * (|B| / Real.cos θ)
      ≤ (1 / 2) * (AngSecond.sig θ * A ^ 2) + 2 * (AngSecond.sig θ * B ^ 2) := by
  have hs := sin_two_pos hθ
  have hρ := wrho_eq_half_sin_mul_sig hθ
  set X : ℝ := (Real.sin (2 * θ)) ^ (-(eη) / 2) * |A| with hX
  set Y : ℝ := (Real.sin (2 * θ)) ^ ((2 - eη) / 2) * (|B| / Real.cos θ) with hY
  have hsq : (Real.sin (2 * θ)) ^ (-(eη) / 2) * (Real.sin (2 * θ)) ^ ((2 - eη) / 2)
      = Real.sin (2 * θ) * AngSecond.sig θ := by
    rw [← Real.rpow_add hs, show -(eη) / 2 + (2 - eη) / 2 = 1 - eη by ring,
      show (1 : ℝ) - eη = 1 + (-(eη)) by ring, Real.rpow_add hs, Real.rpow_one]
    rfl
  have hLHS : 2 * wrho eη θ * |A| * (|B| / Real.cos θ) = X * Y := by
    rw [hX, hY, hρ]
    calc 2 * ((1 / 2 * Real.sin (2 * θ)) * AngSecond.sig θ) * |A| * (|B| / Real.cos θ)
        = ((Real.sin (2 * θ)) ^ (-(eη) / 2) * (Real.sin (2 * θ)) ^ ((2 - eη) / 2)) * |A|
            * (|B| / Real.cos θ) := by rw [hsq]; ring
      _ = ((Real.sin (2 * θ)) ^ (-(eη) / 2) * |A|)
            * ((Real.sin (2 * θ)) ^ ((2 - eη) / 2) * (|B| / Real.cos θ)) := by ring
  have hXs : X ^ 2 = AngSecond.sig θ * A ^ 2 := by
    rw [hX, mul_pow]
    have h1 : ((Real.sin (2 * θ)) ^ (-(eη) / 2)) ^ 2 = AngSecond.sig θ := by
      rw [pow_two, ← Real.rpow_add hs, show -(eη) / 2 + -(eη) / 2 = -(eη) by ring]
      rfl
    rw [h1, sq_abs]
  have hYs : Y ^ 2 ≤ 4 * (AngSecond.sig θ * B ^ 2) := by
    rw [hY, mul_pow]
    have h1 : ((Real.sin (2 * θ)) ^ ((2 - eη) / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (2 - eη) := by
      rw [pow_two, ← Real.rpow_add hs, show (2 - eη) / 2 + (2 - eη) / 2 = 2 - eη by ring]
    rw [h1]
    have hd : (|B| / Real.cos θ) ^ 2 = B ^ 2 / (Real.cos θ) ^ 2 := by
      rw [div_pow, sq_abs]
    rw [hd]
    calc (Real.sin (2 * θ)) ^ (2 - eη) * (B ^ 2 / (Real.cos θ) ^ 2)
        = ((Real.sin (2 * θ)) ^ (2 - eη) / (Real.cos θ) ^ 2) * B ^ 2 := by ring
      _ ≤ (4 * AngSecond.sig θ) * B ^ 2 :=
          mul_le_mul_of_nonneg_right (sin_two_pow_two_sub_eta_div_cos_sq_le hθ) (sq_nonneg B)
      _ = 4 * (AngSecond.sig θ * B ^ 2) := by ring
  have h2 : 2 * X * Y ≤ X ^ 2 + Y ^ 2 := two_mul_le_add_sq X Y
  have h2' : 2 * X * Y = 2 * (2 * wrho eη θ * |A| * (|B| / Real.cos θ)) := by
    rw [show 2 * X * Y = 2 * (X * Y) by ring, hLHS]
  rw [hLHS]
  linarith [h2, h2', hXs, hYs]

/-- `2|a||b| ≤ a² + b²`. -/
private lemma two_mul_abs_mul_le (a b : ℝ) : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
  have h := two_mul_le_add_sq |a| |b|
  rwa [sq_abs, sq_abs] at h

/-! ## The second derivative of the slice variable -/

/-- **Leibniz for the slice variable.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then
`u''(θ) = ψ''(θ) cos θ - 2 ψ'(θ) sin θ - ψ(θ) cos θ` with `ψ = u / cos`.
(Copy of the private companion of `Work.FTS.EllipticEst.TanTheta.psi_second_deriv`, stated for
`ContDiffAt` so that it applies to the honest hypotheses on the open interval.) -/
private lemma deriv_deriv_eq_div_cos_at (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    deriv (deriv u) θ
      = deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ * Real.cos θ
        - 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        - (u θ / Real.cos θ) * Real.cos θ := by
  obtain ⟨s, hs_mem, hs_reg⟩ := hu.contDiffOn le_rfl (by simp)
  have hmem : interior s ∈ 𝓝 θ :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs_mem)
  have hreg : ContDiffOn ℝ 2 u (interior s) := hs_reg.mono interior_subset
  have hdiff : ∀ t ∈ interior s, DifferentiableAt ℝ u t := fun t ht =>
    (hreg.differentiableOn (by simp)).differentiableAt (isOpen_interior.mem_nhds ht)
  have hcos_nhds : ∀ᶠ t in 𝓝 θ, Real.cos t ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hcos
  have heq_deriv : deriv u =ᶠ[𝓝 θ]
      fun t : ℝ =>
        deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t - (u t / Real.cos t) * Real.sin t := by
    filter_upwards [hcos_nhds, hmem] with t ht hts
    have heqt : u =ᶠ[𝓝 t] fun s : ℝ => (u s / Real.cos s) * Real.cos s := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne ht] with s hs
      exact (div_mul_cancel₀ (u s) hs).symm
    have hd : deriv (fun s : ℝ => (u s / Real.cos s) * Real.cos s) t
        = deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
          + (u t / Real.cos t) * (-Real.sin t) := by
      have hVt : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) t :=
        (hdiff t hts).div Real.differentiableAt_cos ht
      have h3 : HasDerivAt (fun s : ℝ => (u s / Real.cos s) * Real.cos s)
          (deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
            + (u t / Real.cos t) * (-Real.sin t)) t :=
        hVt.hasDerivAt.mul (Real.hasDerivAt_cos t)
      exact h3.deriv
    rw [heqt.deriv_eq, hd]
    ring
  rw [heq_deriv.deriv_eq]
  have hVd : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) θ :=
    (hu.div (Real.contDiff_cos.contDiffAt) hcos).differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ (deriv (fun s : ℝ => u s / Real.cos s)) θ :=
    ((hu.div (Real.contDiff_cos.contDiffAt) hcos).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by simp)
  have h1 : HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t)
      (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
        + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ)) θ :=
    hDd.hasDerivAt.mul (Real.hasDerivAt_cos θ)
  have h2 : HasDerivAt (fun t : ℝ => (u t / Real.cos t) * Real.sin t)
      (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ) θ :=
    hVd.hasDerivAt.mul (Real.hasDerivAt_sin θ)
  have h3 := h1.sub h2
  have h4 : deriv (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
        - (u t / Real.cos t) * Real.sin t) θ
      = (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
          + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ))
        - (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
            + (u θ / Real.cos θ) * Real.cos θ) := h3.deriv
  rw [h4]
  ring

/-- **The Leibniz identity for `ψ = u / cos`**, in the form used below:
`cos θ · ψ'' θ = u''(θ) + 2 sin θ · ψ' θ + cos θ · ψ θ`. -/
private lemma psi_second_deriv_Ioo (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u Iθ) {θ : ℝ}
    (hθ : θ ∈ Iθ) :
    Real.cos θ * deriv (deriv (psi u)) θ
      = deriv (deriv u) θ + 2 * deriv (psi u) θ * Real.sin θ + psi u θ * Real.cos θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt (cos_pos hθ)
  have h := deriv_deriv_eq_div_cos_at u (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)) hc
  change Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
      = deriv (deriv u) θ + 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ
  rw [h]; ring

/-! ## The divergence of `∫ dt / t` at the right endpoint -/

/-- **`c/(π/2 - θ)` is not integrable near `π/2`.**  Obtained from the divergence of `∫ dt/t`
at `0` (`Work.FTS.EllipticEst.Honest.not_integrableOn_div_of_ge_const`) by the reflection
`θ ↦ π/2 - θ` (`IntervalIntegrable.comp_sub_left_iff`). -/
private lemma not_integrableOn_right {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ¬ IntegrableOn (fun θ : ℝ => c / (Real.pi / 2 - θ))
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
  have hleft : ¬ IntegrableOn (fun u : ℝ => c / u) (Set.Ioo (0 : ℝ) δ) := by
    have h := not_integrableOn_div_of_ge_const (F := fun _ : ℝ => c) hc hδ
      (fun t _ => le_refl c)
    simpa using h
  intro hI
  have hle : Real.pi / 2 - δ ≤ Real.pi / 2 := by linarith
  have hII : IntervalIntegrable (fun θ : ℝ => c / (Real.pi / 2 - θ)) volume
      (Real.pi / 2 - δ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mpr hI
  have hiff := (IntervalIntegrable.comp_sub_left_iff (f := fun u : ℝ => c / u)
    (a := δ) (b := 0) (Real.pi / 2) (by simp)).mp
  have hII' : IntervalIntegrable (fun u : ℝ => c / u) volume δ 0 := by
    apply hiff
    simpa using hII
  have hII'' : IntervalIntegrable (fun u : ℝ => c / u) volume (0 : ℝ) δ := hII'.symm
  exact hleft ((intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mp hII'')

/-! ## A positive limit is impossible -/

/-- If `F = ρ W² ≥ 0` on `(0, π/2)` with `∫ σ W² < ∞`, then a limit of `F` at `0⁺` must be
`0`: a positive limit forces `σ W² ≥ c/t`, whose integral diverges. -/
private lemma eq_zero_of_tendsto_right {F W : ℝ → ℝ} {L : ℝ}
    (hL : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hFnn : ∀ x ∈ Iθ, 0 ≤ F x)
    (hFW : ∀ x ∈ Iθ, F x = wrho eη x * (W x) ^ 2)
    (hWint : IntegrableOn (fun x => AngSecond.sig x * (W x) ^ 2) Iθ) : L = 0 := by
  have hLnn : 0 ≤ L :=
    ge_of_tendsto hL (by
      filter_upwards [Ioo_mem_nhdsGT pi_half_pos] with x hx
      exact hFnn x hx)
  by_contra hne
  have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
  have hm : Set.Ioi (L / 2) ∈ 𝓝 L := Ioi_mem_nhds (by linarith)
  have hev : {x : ℝ | L / 2 < F x} ∈ 𝓝[>] (0 : ℝ) := hL hm
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hbpos : (0 : ℝ) < b := hb
  set δ : ℝ := min b (Real.pi / 2) with hδ
  have hδpos : 0 < δ := lt_min hbpos pi_half_pos
  have hδle : δ ≤ Real.pi / 2 := min_le_right _ _
  have hδsub : Set.Ioo (0 : ℝ) δ ⊆ Iθ := fun x hx =>
    ⟨hx.1, lt_of_lt_of_le hx.2 hδle⟩
  have hkey : ∀ t ∈ Set.Ioo (0 : ℝ) δ, L / 2 ≤ t * (AngSecond.sig t * (W t) ^ 2) := by
    intro t ht
    have htI : t ∈ Iθ := hδsub ht
    have htb : t ∈ Set.Ioo (0 : ℝ) b := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have hFt : L / 2 < F t := hbsub htb
    rw [hFW t htI] at hFt
    have hρle : wrho eη t ≤ t * AngSecond.sig t := wrho_le_mul_sig_right htI
    calc L / 2 ≤ wrho eη t * (W t) ^ 2 := le_of_lt hFt
      _ ≤ (t * AngSecond.sig t) * (W t) ^ 2 :=
          mul_le_mul_of_nonneg_right hρle (sq_nonneg _)
      _ = t * (AngSecond.sig t * (W t) ^ 2) := by ring
  have hnot := not_integrableOn_div_of_ge_const
    (F := fun t : ℝ => t * (AngSecond.sig t * (W t) ^ 2)) (by linarith : 0 < L / 2) hδpos hkey
  have heq : Set.EqOn (fun t : ℝ => (t * (AngSecond.sig t * (W t) ^ 2)) / t)
      (fun t => AngSecond.sig t * (W t) ^ 2) (Set.Ioo (0 : ℝ) δ) := by
    intro t ht
    rw [div_eq_iff (ne_of_gt ht.1)]
    ring
  have hnot' : ¬ IntegrableOn (fun t => AngSecond.sig t * (W t) ^ 2)
      (Set.Ioo (0 : ℝ) δ) := by
    intro h
    exact hnot (h.congr_fun heq.symm measurableSet_Ioo)
  exact hnot' (hWint.mono_set hδsub)

/-- If `F = ρ W² ≥ 0` on `(0, π/2)` with `∫ σ W² < ∞`, then a limit of `F` at `π/2⁻` must be
`0`. -/
private lemma eq_zero_of_tendsto_left {F W : ℝ → ℝ} {L : ℝ}
    (hL : Tendsto F (𝓝[<] (Real.pi / 2)) (𝓝 L))
    (hFnn : ∀ x ∈ Iθ, 0 ≤ F x)
    (hFW : ∀ x ∈ Iθ, F x = wrho eη x * (W x) ^ 2)
    (hWint : IntegrableOn (fun x => AngSecond.sig x * (W x) ^ 2) Iθ) : L = 0 := by
  have hLnn : 0 ≤ L :=
    ge_of_tendsto hL (by
      filter_upwards [Ioo_mem_nhdsLT pi_half_pos] with x hx
      exact hFnn x hx)
  by_contra hne
  have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
  have hm : Set.Ioi (L / 2) ∈ 𝓝 L := Ioi_mem_nhds (by linarith)
  have hev : {x : ℝ | L / 2 < F x} ∈ 𝓝[<] (Real.pi / 2) := hL hm
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  have hblt : b < Real.pi / 2 := hb
  set δ : ℝ := min (Real.pi / 2 - b) (Real.pi / 2) with hδ
  have hδle1 : δ ≤ Real.pi / 2 - b := min_le_left _ _
  have hδle2 : δ ≤ Real.pi / 2 := min_le_right _ _
  have hδpos : 0 < δ := lt_min (by linarith) pi_half_pos
  have hδsub : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, hδle2], hx.2⟩
  have hkey : ∀ t ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
      L / 2 ≤ (Real.pi / 2 - t) * (AngSecond.sig t * (W t) ^ 2) := by
    intro t ht
    have htI : t ∈ Iθ := hδsub ht
    have htb : t ∈ Set.Ioo b (Real.pi / 2) := by
      exact ⟨by linarith [ht.1, hδle1], ht.2⟩
    have hFt : L / 2 < F t := hbsub htb
    rw [hFW t htI] at hFt
    have hρle : wrho eη t ≤ (Real.pi / 2 - t) * AngSecond.sig t :=
      wrho_le_mul_sig_left htI
    calc L / 2 ≤ wrho eη t * (W t) ^ 2 := le_of_lt hFt
      _ ≤ ((Real.pi / 2 - t) * AngSecond.sig t) * (W t) ^ 2 :=
          mul_le_mul_of_nonneg_right hρle (sq_nonneg _)
      _ = (Real.pi / 2 - t) * (AngSecond.sig t * (W t) ^ 2) := by ring
  have hcomp : IntegrableOn (fun t : ℝ => (L / 2) / (Real.pi / 2 - t))
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
    refine Integrable.mono' (hWint.mono_set hδsub) ?_ ?_
    · have hcont : ContinuousOn (fun t : ℝ => (L / 2) / (Real.pi / 2 - t))
          (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
        refine continuousOn_const.div (continuousOn_const.sub continuousOn_id) ?_
        intro t ht
        linarith [ht.2]
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpos : 0 < Real.pi / 2 - t := by linarith [ht.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hpos.le)]
      rw [div_le_iff₀ hpos]
      calc L / 2 ≤ (Real.pi / 2 - t) * (AngSecond.sig t * (W t) ^ 2) := hkey t ht
        _ = (AngSecond.sig t * (W t) ^ 2) * (Real.pi / 2 - t) := by ring
  exact not_integrableOn_right (by linarith : 0 < L / 2) hδpos hcomp

/-! ## The main theorem -/

set_option maxHeartbeats 1600000 in
theorem psi_boundary_vanish (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hB : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA' : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (u θ / Real.cos θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (u θ / Real.cos θ) ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  -- ## Smoothness of the slice variable and its derivatives
  have hψcd : ContDiffOn ℝ 2 (psi u) Iθ :=
    hu.div Real.contDiff_cos.contDiffOn (fun θ hθ => ne_of_gt (cos_pos hθ))
  have hψcont : ContinuousOn (psi u) Iθ := hψcd.continuousOn
  have hψ1d : ∀ θ ∈ Iθ, HasDerivAt (psi u) (deriv (psi u) θ) θ := fun θ hθ =>
    ((hψcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hψ1cd : ContDiffOn ℝ 1 (deriv (psi u)) Iθ :=
    hψcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hψ1cont : ContinuousOn (deriv (psi u)) Iθ := hψ1cd.continuousOn
  have hψ2cd : ContDiffOn ℝ 0 (deriv (deriv (psi u))) Iθ :=
    hψ1cd.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
  have hψ2cont : ContinuousOn (deriv (deriv (psi u))) Iθ := hψ2cd.continuousOn
  have hψ2d : ∀ θ ∈ Iθ, HasDerivAt (deriv (psi u)) (deriv (deriv (psi u)) θ) θ := fun θ hθ =>
    ((hψ1cd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  -- ## Lebesgue integrability of the three basic weights
  have hSg : IntegrableOn (fun θ => AngSecond.sig θ * (psi u θ) ^ 2) Iθ := by
    change IntegrableOn (fun θ => AngSecond.sig θ * (u θ / Real.cos θ) ^ 2) Iθ
    exact hA.congr_fun (fun θ _ => by ring) measurableSet_Ioo
  have hSg1 : IntegrableOn (fun θ => AngSecond.sig θ * (deriv (psi u) θ) ^ 2) Iθ := by
    change IntegrableOn
      (fun θ => AngSecond.sig θ * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2) Iθ
    exact hA'.congr_fun (fun θ _ => by ring) measurableSet_Ioo
  have hSgu : IntegrableOn (fun θ => AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) Iθ :=
    hX.congr_fun (fun θ _ => by ring) measurableSet_Ioo
  have hRho : IntegrableOn (fun θ => wrho eη θ * (psi u θ) ^ 2) Iθ := by
    refine Integrable.mono' hSg ?_ ?_
    · exact (continuousOn_wrho.mul (hψcont.pow 2)).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wrho_nonneg hθ) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _)
  have hRho1 : IntegrableOn (fun θ => wrho eη θ * (deriv (psi u) θ) ^ 2) Iθ := by
    refine Integrable.mono' hSg1 ?_ ?_
    · exact (continuousOn_wrho.mul (hψ1cont.pow 2)).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wrho_nonneg hθ) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _)
  -- ## The two derivative functions
  have hF1d : ∀ θ ∈ Iθ, HasDerivAt (fun t => wrho eη t * (psi u t) ^ 2)
      (wrhoD eη θ * (psi u θ) ^ 2 + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)) θ := by
    intro θ hθ
    have h1 := wrho_deriv eη hθ
    have h2 : HasDerivAt (fun t => (psi u t) ^ 2) (2 * psi u θ * deriv (psi u) θ) θ := by
      have hp := (hψ1d θ hθ).pow 2
      refine hp.congr_deriv ?_
      push_cast
      ring
    have h3 := h1.mul h2
    convert h3 using 1
  have hF2d : ∀ θ ∈ Iθ, HasDerivAt (fun t => wrho eη t * (deriv (psi u) t) ^ 2)
      (wrhoD eη θ * (deriv (psi u) θ) ^ 2
        + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)) θ := by
    intro θ hθ
    have h1 := wrho_deriv eη hθ
    have h2 : HasDerivAt (fun t => (deriv (psi u) t) ^ 2)
        (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ) θ := by
      have hp := (hψ2d θ hθ).pow 2
      refine hp.congr_deriv ?_
      push_cast
      ring
    have h3 := h1.mul h2
    convert h3 using 1
  -- ## The dominating integrable function
  have hDm : IntegrableOn (fun θ => AngSecond.sig θ * (psi u θ) ^ 2
      + AngSecond.sig θ * (deriv (psi u) θ) ^ 2
      + AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) Iθ :=
    (hSg.add hSg1).add hSgu
  -- ## Integrability of the derivative of `ρψ²`
  have hG1int : IntegrableOn (fun θ => wrhoD eη θ * (psi u θ) ^ 2
      + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)) Iθ := by
    refine Integrable.mono' (hDm.const_mul 10) ?_ ?_
    · refine ((continuousOn_wrhoD.mul (hψcont.pow 2)).add
        (continuousOn_wrho.mul ((continuousOn_const.mul hψcont).mul hψ1cont))).aestronglyMeasurable
        measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hsig := sig_nonneg hθ
      have hρ0 := wrho_nonneg hθ
      have hS1 : 0 ≤ AngSecond.sig θ * (psi u θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hS2 : 0 ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hS3 : 0 ≤ AngSecond.sig θ * (deriv (deriv u) θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hA1 : |wrhoD eη θ| * (psi u θ) ^ 2
          ≤ (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2) := by
        calc |wrhoD eη θ| * (psi u θ) ^ 2
            ≤ ((1 - eη) * AngSecond.sig θ) * (psi u θ) ^ 2 :=
              mul_le_mul_of_nonneg_right (abs_wrhoD_le_sig hθ) (sq_nonneg _)
          _ = (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2) := by ring
      have hA2 : wrho eη θ * (2 * |psi u θ| * |deriv (psi u) θ|)
          ≤ wrho eη θ * ((psi u θ) ^ 2 + (deriv (psi u) θ) ^ 2) :=
        mul_le_mul_of_nonneg_left (two_mul_abs_mul_le _ _) hρ0
      have hA3 : wrho eη θ * ((psi u θ) ^ 2 + (deriv (psi u) θ) ^ 2)
          ≤ AngSecond.sig θ * (psi u θ) ^ 2 + AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _))
      have htri : |wrhoD eη θ * (psi u θ) ^ 2 + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)|
          ≤ |wrhoD eη θ| * (psi u θ) ^ 2
            + wrho eη θ * (2 * |psi u θ| * |deriv (psi u) θ|) := by
        calc |wrhoD eη θ * (psi u θ) ^ 2 + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)|
            ≤ |wrhoD eη θ * (psi u θ) ^ 2|
              + |wrho eη θ * (2 * psi u θ * deriv (psi u) θ)| := abs_add_le _ _
          _ = |wrhoD eη θ| * (psi u θ) ^ 2
              + wrho eη θ * (2 * |psi u θ| * |deriv (psi u) θ|) := by
                rw [abs_mul, abs_mul, abs_of_nonneg hρ0,
                  abs_of_nonneg (sq_nonneg (psi u θ)), abs_mul, abs_mul,
                  abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hstep : (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2)
          ≤ AngSecond.sig θ * (psi u θ) ^ 2 := by
        calc (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2)
            ≤ 1 * (AngSecond.sig θ * (psi u θ) ^ 2) :=
              mul_le_mul_of_nonneg_right
                (by linarith [Work.Spaces.eta_lt_one, Work.Spaces.eta_nonneg]) hS1
          _ = AngSecond.sig θ * (psi u θ) ^ 2 := one_mul _
      rw [Real.norm_eq_abs]
      calc |wrhoD eη θ * (psi u θ) ^ 2 + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)|
          ≤ |wrhoD eη θ| * (psi u θ) ^ 2
            + wrho eη θ * (2 * |psi u θ| * |deriv (psi u) θ|) := htri
        _ ≤ (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2)
            + wrho eη θ * ((psi u θ) ^ 2 + (deriv (psi u) θ) ^ 2) := add_le_add hA1 hA2
        _ ≤ AngSecond.sig θ * (psi u θ) ^ 2
            + (AngSecond.sig θ * (psi u θ) ^ 2 + AngSecond.sig θ * (deriv (psi u) θ) ^ 2) :=
              add_le_add hstep hA3
        _ ≤ 10 * (AngSecond.sig θ * (psi u θ) ^ 2 + AngSecond.sig θ * (deriv (psi u) θ) ^ 2
            + AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) := by
              nlinarith [hS1, hS2, hS3]
  -- ## Integrability of the derivative of `ρψ'²`
  have hG2int : IntegrableOn (fun θ => wrhoD eη θ * (deriv (psi u) θ) ^ 2
      + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)) Iθ := by
    refine Integrable.mono' (hDm.const_mul 10) ?_ ?_
    · refine ((continuousOn_wrhoD.mul (hψ1cont.pow 2)).add
        (continuousOn_wrho.mul ((continuousOn_const.mul hψ1cont).mul hψ2cont))).aestronglyMeasurable
        measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hsig := sig_nonneg hθ
      have hρ0 := wrho_nonneg hθ
      have hcos := cos_pos hθ
      have hsin : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, Real.pi_pos])
      have hS1 : 0 ≤ AngSecond.sig θ * (psi u θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hS2 : 0 ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hS3 : 0 ≤ AngSecond.sig θ * (deriv (deriv u) θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      -- Leibniz: `ψ'' cos θ = u'' + 2 sin θ ψ' + ψ cos θ`
      have hid := psi_second_deriv_Ioo u hu hθ
      have hW2 : deriv (deriv (psi u)) θ * Real.cos θ
          = deriv (deriv u) θ + 2 * deriv (psi u) θ * Real.sin θ + psi u θ * Real.cos θ := by
        rw [mul_comm]; exact hid
      have hnum : |deriv (deriv (psi u)) θ| * Real.cos θ
          ≤ |deriv (deriv u) θ| + 2 * |deriv (psi u) θ| * Real.sin θ
            + |psi u θ| * Real.cos θ := by
        have habs : |deriv (deriv (psi u)) θ| * Real.cos θ
            = |deriv (deriv (psi u)) θ * Real.cos θ| := by
          rw [abs_mul, abs_of_pos hcos]
        rw [habs, hW2]
        calc |deriv (deriv u) θ + 2 * deriv (psi u) θ * Real.sin θ + psi u θ * Real.cos θ|
            ≤ |deriv (deriv u) θ + 2 * deriv (psi u) θ * Real.sin θ|
              + |psi u θ * Real.cos θ| := abs_add_le _ _
          _ ≤ (|deriv (deriv u) θ| + |2 * deriv (psi u) θ * Real.sin θ|)
              + |psi u θ| * Real.cos θ :=
                add_le_add (abs_add_le _ _) (by rw [abs_mul, abs_of_pos hcos])
          _ = |deriv (deriv u) θ| + 2 * |deriv (psi u) θ| * Real.sin θ
              + |psi u θ| * Real.cos θ := by
                rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                  abs_of_nonneg hsin]
      have hW2le : |deriv (deriv (psi u)) θ| ≤ |deriv (deriv u) θ| / Real.cos θ
          + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ| := by
        calc |deriv (deriv (psi u)) θ|
            = (|deriv (deriv (psi u)) θ| * Real.cos θ) / Real.cos θ := by
              field_simp
          _ ≤ (|deriv (deriv u) θ| + 2 * |deriv (psi u) θ| * Real.sin θ
                + |psi u θ| * Real.cos θ) / Real.cos θ :=
              div_le_div_of_nonneg_right hnum hcos.le
          _ = |deriv (deriv u) θ| / Real.cos θ
              + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ| := by
              field_simp
      -- the three pieces
      have hT1 : wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ))
          ≤ (1 / 2) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
            + 2 * (AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) := by
        have h := two_wrho_mul_le hθ (deriv (psi u) θ) (deriv (deriv u) θ)
        have h' : wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ))
            = 2 * wrho eη θ * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ) := by
          ring
        linarith [h, h']
      have hT2 : wrho eη θ * (4 * (|deriv (psi u) θ| * |deriv (psi u) θ|)
          * (Real.sin θ / Real.cos θ)) ≤ 4 * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) := by
        have htan := wrho_mul_tan_le_sig hθ
        have hsq : |deriv (psi u) θ| * |deriv (psi u) θ| = (deriv (psi u) θ) ^ 2 := by
          rw [← sq_abs]; ring
        calc wrho eη θ * (4 * (|deriv (psi u) θ| * |deriv (psi u) θ|)
              * (Real.sin θ / Real.cos θ))
            = 4 * (wrho eη θ * (Real.sin θ / Real.cos θ)) * (deriv (psi u) θ) ^ 2 := by
              rw [hsq]; ring
          _ ≤ 4 * AngSecond.sig θ * (deriv (psi u) θ) ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htan (by norm_num))
                (sq_nonneg _)
          _ = 4 * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) := by ring
      have hT3 : wrho eη θ * (2 * |deriv (psi u) θ| * |psi u θ|)
          ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 + AngSecond.sig θ * (psi u θ) ^ 2 := by
        have h := two_mul_abs_mul_le (deriv (psi u) θ) (psi u θ)
        have h2 := mul_le_mul_of_nonneg_left h hρ0
        calc wrho eη θ * (2 * |deriv (psi u) θ| * |psi u θ|)
            ≤ wrho eη θ * ((deriv (psi u) θ) ^ 2 + (psi u θ) ^ 2) := h2
          _ = wrho eη θ * (deriv (psi u) θ) ^ 2 + wrho eη θ * (psi u θ) ^ 2 := by ring
          _ ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 + AngSecond.sig θ * (psi u θ) ^ 2 :=
              add_le_add (mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _))
                (mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _))
      have hA1 : |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
          ≤ (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) := by
        calc |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
            ≤ ((1 - eη) * AngSecond.sig θ) * (deriv (psi u) θ) ^ 2 :=
              mul_le_mul_of_nonneg_right (abs_wrhoD_le_sig hθ) (sq_nonneg _)
          _ = (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) := by ring
      -- assemble
      have htri : |wrhoD eη θ * (deriv (psi u) θ) ^ 2
          + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)|
          ≤ |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
            + wrho eη θ * (2 * |deriv (psi u) θ| * |deriv (deriv (psi u)) θ|) := by
        calc |wrhoD eη θ * (deriv (psi u) θ) ^ 2
            + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)|
            ≤ |wrhoD eη θ * (deriv (psi u) θ) ^ 2|
              + |wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)| := abs_add_le _ _
          _ = |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
              + wrho eη θ * (2 * |deriv (psi u) θ| * |deriv (deriv (psi u)) θ|) := by
                rw [abs_mul, abs_mul, abs_of_nonneg hρ0,
                  abs_of_nonneg (sq_nonneg (deriv (psi u) θ)), abs_mul, abs_mul,
                  abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hmid : wrho eη θ * (2 * |deriv (psi u) θ| * |deriv (deriv (psi u)) θ|)
          ≤ wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ
              + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hW2le (by positivity)) hρ0
      have hdist : wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ
          + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ|))
          = wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ))
            + wrho eη θ * (4 * (|deriv (psi u) θ| * |deriv (psi u) θ|)
                * (Real.sin θ / Real.cos θ))
            + wrho eη θ * (2 * |deriv (psi u) θ| * |psi u θ|) := by
        ring
      rw [Real.norm_eq_abs]
      calc |wrhoD eη θ * (deriv (psi u) θ) ^ 2
          + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)|
          ≤ |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
            + wrho eη θ * (2 * |deriv (psi u) θ| * |deriv (deriv (psi u)) θ|) := htri
        _ ≤ (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
            + wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ
              + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ|)) :=
              add_le_add hA1 hmid
        _ = (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
            + (wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ))
              + wrho eη θ * (4 * (|deriv (psi u) θ| * |deriv (psi u) θ|)
                  * (Real.sin θ / Real.cos θ))
              + wrho eη θ * (2 * |deriv (psi u) θ| * |psi u θ|)) := by
              rw [hdist]
        _ ≤ (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
            + (((1 / 2) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
                + 2 * (AngSecond.sig θ * (deriv (deriv u) θ) ^ 2))
              + 4 * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
              + (AngSecond.sig θ * (deriv (psi u) θ) ^ 2
                + AngSecond.sig θ * (psi u θ) ^ 2)) := by
              refine add_le_add le_rfl ?_
              exact add_le_add (add_le_add hT1 hT2) hT3
        _ ≤ 10 * (AngSecond.sig θ * (psi u θ) ^ 2 + AngSecond.sig θ * (deriv (psi u) θ) ^ 2
            + AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) := by
              have h1 : (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
                  ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := by
                calc (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
                    ≤ 1 * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) :=
                      mul_le_mul_of_nonneg_right
                        (by linarith [Work.Spaces.eta_lt_one, Work.Spaces.eta_nonneg]) hS2
                  _ = AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := one_mul _
              linarith [h1, hS1, hS2, hS3]
  -- ## The four limits
  obtain ⟨L1, hL1⟩ := exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    pi_half_pos hF1d hG1int
  obtain ⟨L2, hL2⟩ := exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    pi_half_pos hF2d hG2int
  obtain ⟨M1, hM1⟩ := exists_tendsto_nhdsLT_of_integrableOn_deriv
    pi_half_pos hF1d hG1int
  obtain ⟨M2, hM2⟩ := exists_tendsto_nhdsLT_of_integrableOn_deriv
    pi_half_pos hF2d hG2int
  have hL1z : L1 = 0 := eq_zero_of_tendsto_right hL1
    (fun θ hθ => mul_nonneg (wrho_nonneg hθ) (sq_nonneg _)) (fun θ _ => rfl) hSg
  have hL2z : L2 = 0 := eq_zero_of_tendsto_right hL2
    (fun θ hθ => mul_nonneg (wrho_nonneg hθ) (sq_nonneg _)) (fun θ _ => rfl) hSg1
  have hM1z : M1 = 0 := eq_zero_of_tendsto_left hM1
    (fun θ hθ => mul_nonneg (wrho_nonneg hθ) (sq_nonneg _)) (fun θ _ => rfl) hSg
  have hM2z : M2 = 0 := eq_zero_of_tendsto_left hM2
    (fun θ hθ => mul_nonneg (wrho_nonneg hθ) (sq_nonneg _)) (fun θ _ => rfl) hSg1
  rw [hL1z] at hL1
  rw [hL2z] at hL2
  rw [hM1z] at hM1
  rw [hM2z] at hM2
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Filter.Tendsto (fun t : ℝ => wrho eη t * (psi u t) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
    exact hL1
  · change Filter.Tendsto (fun t : ℝ => wrho eη t * (psi u t) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
    exact hM1
  · change Filter.Tendsto (fun t : ℝ => wrho eη t * (deriv (psi u) t) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
    exact hL2
  · change Filter.Tendsto (fun t : ℝ => wrho eη t * (deriv (psi u) t) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
    exact hM2

end Work.FTS.EllipticEst.Honest
