import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Norms =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The angular weight `ρ = sin(2θ)^{-η}` and the full weight `W = w · ρ^{1/2}` -/

/-- `ρ θ = sin(2θ)^{-η}`, the angular weight of the `k = 0` elliptic estimate (`η = 99/100`). -/
def rho (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The full weight `W = w / sin(2θ)^{η/2}`, the weight occurring in `HkIntegrand α 0`. -/
def Wf (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem rho_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ rho θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _


/-- `(s^{-η/2})² = s^{-η}` for `s > 0`, the algebra behind `Wf_sq_eq`. -/
theorem rpow_half_sq {s : ℝ} (h : 0 < s) :
    (s ^ (-(Work.Spaces.eta / 2))) ^ 2 = s ^ (-(Work.Spaces.eta)) := by
  rw [pow_two, ← Real.rpow_add h,
    show -(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2) = -(Work.Spaces.eta) by ring]

/-- The square of the full weight is `w² · ρ`, the weight of the iterated integrals below. -/
theorem Wf_sq_eq {z θ : ℝ} (h : 0 ≤ Real.sin (2 * θ)) :
    (Wf z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * rho θ := by
  rw [Wf, rho]
  rcases eq_or_lt_of_le h with h0 | h0
  · rw [← h0,
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : Work.Spaces.eta / 2 ≠ 0),
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≠ 0),
      div_zero, mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  · rw [div_eq_mul_inv, ← Real.rpow_neg h0.le, mul_pow, rpow_half_sq h0]

/-! ## The two squared norms -/











end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_G2_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

namespace Work.FTS.EllipticEst.remov

noncomputable section

/-! ## Elementary facts about the weight `σ = sin(2θ)^{2-γ}` -/

section SigmaFacts

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) > 0` on the open interval. -/
private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sigG_nonneg (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ sigG γ θ := by
  intro θ hθ
  simp only [sigG]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

private lemma sigG_le_one (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∀ θ ∈ Work.Spaces.Iθ, sigG γ θ ≤ 1 := by
  intro θ hθ
  simp only [sigG]
  exact Real.rpow_le_one (sin_two_nonneg hθ) (Real.sin_le_one _) (by linarith)

private lemma sigG_pos (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < sigG γ θ := by
  intro θ hθ
  simp only [sigG]
  exact Real.rpow_pos_of_pos (sin_two_pos hθ) _

private lemma sigG_zero_left (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) : sigG γ 0 = 0 := by
  simp only [sigG, mul_zero, Real.sin_zero]
  exact Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)

private lemma sigG_zero_right (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    sigG γ (Real.pi / 2) = 0 := by
  have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
  simp only [sigG, h2, Real.sin_pi]
  exact Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)

/-- `σ` is nondecreasing on `[0, π/4]`. -/
private lemma sigG_monoOn (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    MonotoneOn (sigG γ) (Set.Icc 0 (Real.pi / 4)) := by
  intro θ₁ h₁ θ₂ h₂ hle
  simp only [sigG]
  refine Real.rpow_le_rpow
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [h₁.1], by linarith [h₁.2, Real.pi_pos]⟩) ?_
    (by linarith : (0 : ℝ) ≤ 2 - γ)
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [h₁.1, Real.pi_pos])
    (by linarith [h₂.2, Real.pi_pos]) (by linarith)

/-- `σ` is nonincreasing on `[π/4, π/2]`. -/
private lemma sigG_antitoneOn (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    AntitoneOn (sigG γ) (Set.Icc (Real.pi / 4) (Real.pi / 2)) := by
  intro θ₁ h₁ θ₂ h₂ hle
  simp only [sigG]
  have e₁ : Real.sin (2 * θ₁) = Real.sin (2 * (Real.pi / 2 - θ₁)) := by
    rw [show 2 * (Real.pi / 2 - θ₁) = Real.pi - 2 * θ₁ by ring, Real.sin_pi_sub]
  have e₂ : Real.sin (2 * θ₂) = Real.sin (2 * (Real.pi / 2 - θ₂)) := by
    rw [show 2 * (Real.pi / 2 - θ₂) = Real.pi - 2 * θ₂ by ring, Real.sin_pi_sub]
  rw [e₁, e₂]
  refine Real.rpow_le_rpow
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [h₂.2, Real.pi_pos], by linarith [h₂.1, Real.pi_pos]⟩)
    ?_ (by linarith : (0 : ℝ) ≤ 2 - γ)
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [h₂.2, Real.pi_pos])
    (by linarith [h₁.1, Real.pi_pos]) (by linarith)

private lemma sigG_continuousOn (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ContinuousOn (sigG γ) (Set.Icc 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  change ContinuousOn (fun x : ℝ => Real.sin (2 * x) ^ (2 - γ)) (Set.Icc 0 (Real.pi / 2))
  exact hsin.rpow_const (fun θ hθ => Or.inr (by linarith))

private lemma sigG_integrableOn_Icc (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    IntegrableOn (sigG γ) (Set.Icc 0 (Real.pi / 2)) :=
  (sigG_continuousOn γ hγ1 hγ2).integrableOn_compact isCompact_Icc

/-- Integrability of `σ` on any subinterval of `Iθ`. -/
private lemma sigG_integrableOn_Ioo (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) :
    IntegrableOn (sigG γ) (Set.Ioo a b) :=
  (sigG_integrableOn_Icc γ hγ1 hγ2).mono_set
    (fun x hx => ⟨le_trans ha (le_of_lt hx.1), le_trans (le_of_lt hx.2) hb⟩)

end SigmaFacts

/-! ## The third derivative of `u` in terms of `g'` -/

section DerivFacts

/-- `u` is differentiable at interior points. -/
private lemma diffAt_of_contDiffOn {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ u θ :=
  (hu.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- `u'` is differentiable at interior points. -/
private lemma diffAt_deriv_of_contDiffOn {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (deriv u) θ :=
  ((hu.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- `u''` is differentiable at interior points. -/
private lemma diffAt_deriv_deriv_of_contDiffOn {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (deriv (deriv u)) θ :=
  (((hu.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)

/-- `cos θ ≠ 0` on the open angular interval. -/
private lemma cos_ne_zero_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-- Cauchy–Schwarz for three terms. -/
private lemma sum_three_sq_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- `∂_θ(tan θ · u) = (1/cos²θ)·u + tan θ·u'`. -/
private lemma deriv_tan_mul {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : DifferentiableAt ℝ u θ) :
    deriv (fun θ' => Real.tan θ' * u θ') θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ :=
  ((Real.hasDerivAt_tan (cos_ne_zero_of_Ioo hθ)).mul hu.hasDerivAt).deriv

/-- `∂_θ(1/cos²θ) = 2 sin θ / cos³θ`. -/
private lemma hasDerivAt_inv_cos_sq {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => 1 / Real.cos t ^ 2) (2 * Real.sin θ / Real.cos θ ^ 3) θ := by
  have hcos := cos_ne_zero_of_Ioo hθ
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ 2) (2 * Real.cos θ * (-Real.sin θ)) θ := by
    refine ((Real.hasDerivAt_cos θ).fun_pow 2).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 by norm_num]
    ring
  have h2 : HasDerivAt (fun t : ℝ => 1 / Real.cos t ^ 2)
      ((0 * Real.cos θ ^ 2 - 1 * (2 * Real.cos θ * (-Real.sin θ))) / (Real.cos θ ^ 2) ^ 2) θ :=
    (hasDerivAt_const (x := θ) (c := (1 : ℝ))).div h1 (pow_ne_zero 2 hcos)
  have h3 : ((0 * Real.cos θ ^ 2 - 1 * (2 * Real.cos θ * (-Real.sin θ))) / (Real.cos θ ^ 2) ^ 2)
      = 2 * Real.sin θ / Real.cos θ ^ 3 := by
    field_simp
    ring
  exact h2.congr_deriv h3

/-- The second derivative of `tan θ·u`. -/
private lemma deriv_deriv_tan_mul {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = (2 * Real.sin θ / Real.cos θ ^ 3) * u θ
        + 2 * (1 / Real.cos θ ^ 2) * deriv u θ
        + Real.tan θ * deriv (deriv u) θ := by
  have hsum := ((hasDerivAt_inv_cos_sq hθ).mul (diffAt_of_contDiffOn hu hθ).hasDerivAt).add
      ((Real.hasDerivAt_tan (cos_ne_zero_of_Ioo hθ)).mul
        (diffAt_deriv_of_contDiffOn hu hθ).hasDerivAt)
  have hloc : (fun t => deriv (fun s => Real.tan s * u s) t) =ᶠ[𝓝 θ]
      (fun t : ℝ => (1 / Real.cos t ^ 2) * u t + Real.tan t * deriv u t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact deriv_tan_mul ht (diffAt_of_contDiffOn hu ht)
  have hval : ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ + (1 / Real.cos θ ^ 2) * deriv u θ
        + (1 / Real.cos θ ^ 2 * deriv u θ + Real.tan θ * deriv (deriv u) θ))
      = ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ
        + 2 * (1 / Real.cos θ ^ 2) * deriv u θ + Real.tan θ * deriv (deriv u) θ) := by ring
  exact ((hsum.congr_of_eventuallyEq hloc).congr_deriv hval).deriv

/-- `HasDerivAt` of `Lzero1 u`, expanded. -/
private lemma hasDerivAt_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Work.FTS.EllipticEst.Lzero1 u)
      ((-(deriv (deriv (deriv u)) θ)
        + ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ
            + 2 * (1 / Real.cos θ ^ 2) * deriv u θ + Real.tan θ * deriv (deriv u) θ))
        - 6 * deriv u θ) θ := by
  have hd1 : DifferentiableAt ℝ (deriv (deriv u)) θ := diffAt_deriv_deriv_of_contDiffOn hu hθ
  have hd3 : DifferentiableAt ℝ u θ := diffAt_of_contDiffOn hu hθ
  have hmiddle : HasDerivAt (fun t : ℝ => deriv (fun s => Real.tan s * u s) t)
      ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ
        + 2 * (1 / Real.cos θ ^ 2) * deriv u θ + Real.tan θ * deriv (deriv u) θ) θ := by
    have hsum := ((hasDerivAt_inv_cos_sq hθ).mul hd3.hasDerivAt).add
        ((Real.hasDerivAt_tan (cos_ne_zero_of_Ioo hθ)).mul
          (diffAt_deriv_of_contDiffOn hu hθ).hasDerivAt)
    have hloc : (fun t : ℝ => deriv (fun s => Real.tan s * u s) t) =ᶠ[𝓝 θ]
        (fun t : ℝ => (1 / Real.cos t ^ 2) * u t + Real.tan t * deriv u t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact deriv_tan_mul ht (diffAt_of_contDiffOn hu ht)
    have hval : ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ + (1 / Real.cos θ ^ 2) * deriv u θ
          + (1 / Real.cos θ ^ 2 * deriv u θ + Real.tan θ * deriv (deriv u) θ))
        = ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ
          + 2 * (1 / Real.cos θ ^ 2) * deriv u θ + Real.tan θ * deriv (deriv u) θ) := by ring
    exact (hsum.congr_of_eventuallyEq hloc).congr_deriv hval
  have hval2 : ((-(deriv (deriv (deriv u)) θ)
        + ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ
            + 2 * (1 / Real.cos θ ^ 2) * deriv u θ + Real.tan θ * deriv (deriv u) θ))
        - 6 * deriv u θ)
      = ((-(deriv (deriv (deriv u)) θ) + ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ
            + 2 * (1 / Real.cos θ ^ 2) * deriv u θ + Real.tan θ * deriv (deriv u) θ))
        - 6 * deriv u θ) := rfl
  exact ((hd1.hasDerivAt.neg.add hmiddle).sub
    (hd3.hasDerivAt.const_mul 6)).congr_deriv hval2

/-- The derivative of `Lzero1 u`, expanded. -/
private lemma deriv_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (Work.FTS.EllipticEst.Lzero1 u) θ
      = - deriv (deriv (deriv u)) θ
        + ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ
            + 2 * (1 / Real.cos θ ^ 2) * deriv u θ + Real.tan θ * deriv (deriv u) θ)
        - 6 * deriv u θ :=
  (hasDerivAt_Lzero1 hu hθ).deriv

/-- `g' = ∂_θ(Lzero1 u)` on the open interval. -/
private lemma deriv_g_eq {u g : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv g θ = deriv (Work.FTS.EllipticEst.Lzero1 u) θ := by
  have heq : g =ᶠ[𝓝 θ] Work.FTS.EllipticEst.Lzero1 u := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact (hg t ht).symm
  exact heq.deriv_eq

/-- The third derivative of `u` in terms of `u'', u', u` and `g'`. -/
private lemma u_triple_eq {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (deriv u)) θ
      = Real.tan θ * deriv (deriv u) θ + 2 * (1 / Real.cos θ ^ 2) * deriv u θ
        + (2 * Real.sin θ / Real.cos θ ^ 3) * u θ - 6 * deriv u θ - deriv g θ := by
  have h1 : deriv g θ = - deriv (deriv (deriv u)) θ
      + ((2 * Real.sin θ / Real.cos θ ^ 3) * u θ
          + 2 * (1 / Real.cos θ ^ 2) * deriv u θ + Real.tan θ * deriv (deriv u) θ)
      - 6 * deriv u θ := by
    rw [deriv_g_eq hg hθ]
    exact deriv_Lzero1 hu hθ
  linarith

end DerivFacts

/-! ## The pointwise bound on `K = [π/8, 3π/8]` -/

section TripleBound

/-- Cauchy–Schwarz for five terms. -/
private lemma sum_five_sq_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]

/-- On `[π/8, 3π/8]` all three coefficient functions of the `u'''`-identity are bounded. -/
private lemma coeff_bound_K :
    ∃ M : ℝ, 0 < M ∧ ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
      |Real.tan θ| ≤ M ∧ |2 * (1 / Real.cos θ ^ 2)| ≤ M
        ∧ |2 * Real.sin θ / Real.cos θ ^ 3| ≤ M := by
  set K := Set.Icc (Real.pi / 8) (3 * Real.pi / 8) with hKdef
  have hmem : ∀ θ ∈ K, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    intro θ hθ
    rw [hKdef, Set.mem_Icc] at hθ
    exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hcos : ∀ θ ∈ K, Real.cos θ ≠ 0 := fun θ hθ => cos_ne_zero_of_Ioo (hmem θ hθ)
  have hcont : ContinuousOn (fun θ => |Real.tan θ| + |2 * (1 / Real.cos θ ^ 2)|
      + |2 * Real.sin θ / Real.cos θ ^ 3|) K := by
    have htancont : ContinuousOn Real.tan K := by
      rw [show Real.tan = fun θ => Real.sin θ / Real.cos θ from funext Real.tan_eq_sin_div_cos]
      exact ContinuousOn.div Real.continuous_sin.continuousOn Real.continuous_cos.continuousOn hcos
    have hB : ContinuousOn (fun θ : ℝ => 2 * (1 / Real.cos θ ^ 2)) K :=
      continuousOn_const.mul (ContinuousOn.div continuousOn_const
        (Real.continuous_cos.continuousOn.pow 2) (fun θ hθ => pow_ne_zero 2 (hcos θ hθ)))
    have hC : ContinuousOn (fun θ : ℝ => 2 * Real.sin θ / Real.cos θ ^ 3) K :=
      ContinuousOn.div (continuousOn_const.mul Real.continuous_sin.continuousOn)
        (Real.continuous_cos.continuousOn.pow 3) (fun θ hθ => pow_ne_zero 3 (hcos θ hθ))
    exact (htancont.abs.add hB.abs).add hC.abs
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := Real.pi / 8) (b := 3 * Real.pi / 8)).bddAbove_image
    hcont
  refine ⟨max M 1, lt_max_of_lt_right zero_lt_one, fun θ hθ => ?_⟩
  have hle : |Real.tan θ| + |2 * (1 / Real.cos θ ^ 2)| + |2 * Real.sin θ / Real.cos θ ^ 3|
      ≤ M := hM ⟨θ, hθ, rfl⟩
  have hMle : M ≤ max M 1 := le_max_left _ _
  have hsum2 : |Real.tan θ| + |2 * (1 / Real.cos θ ^ 2)|
      ≤ (|Real.tan θ| + |2 * (1 / Real.cos θ ^ 2)|) + |2 * Real.sin θ / Real.cos θ ^ 3| :=
    le_add_of_nonneg_right (abs_nonneg _)
  have hA : |Real.tan θ| ≤ M := by
    have h1 : |Real.tan θ| ≤ |Real.tan θ| + |2 * (1 / Real.cos θ ^ 2)| :=
      le_add_of_nonneg_right (abs_nonneg _)
    exact le_trans (le_trans h1 hsum2) hle
  have hB : |2 * (1 / Real.cos θ ^ 2)| ≤ M := by
    have h1 : |2 * (1 / Real.cos θ ^ 2)| ≤ |Real.tan θ| + |2 * (1 / Real.cos θ ^ 2)| :=
      le_add_of_nonneg_left (abs_nonneg _)
    exact le_trans (le_trans h1 hsum2) hle
  have hC : |2 * Real.sin θ / Real.cos θ ^ 3| ≤ M := by
    have h1 : |2 * Real.sin θ / Real.cos θ ^ 3|
        ≤ (|Real.tan θ| + |2 * (1 / Real.cos θ ^ 2)|) + |2 * Real.sin θ / Real.cos θ ^ 3| :=
      le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans h1 hle
  exact ⟨le_trans hA hMle, le_trans hB hMle, le_trans hC hMle⟩

/-- The pointwise bound for `u'''` on `K`, with a constant independent of `u`, `g`. -/
private theorem u_triple_bound_K :
    ∃ C : ℝ, 0 < C ∧ ∀ (u g : ℝ → ℝ),
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
      (deriv (deriv (deriv u)) θ) ^ 2
        ≤ C * ((deriv (deriv u) θ) ^ 2 + (deriv u θ) ^ 2 + (u θ) ^ 2
            + (deriv g θ) ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := coeff_bound_K
  refine ⟨5 * (M ^ 2 + 36), by positivity, fun u g hu hg θ hθ => ?_⟩
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.mem_Icc] at hθ
    exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  obtain ⟨hA, hB, hC⟩ := hM θ hθ
  have hid := u_triple_eq hu hg hθIoo
  have hAsq : (Real.tan θ) ^ 2 ≤ M ^ 2 := by
    have h := abs_le.mp hA
    nlinarith [h.1, h.2, hM0]
  have hBsq : (2 * (1 / Real.cos θ ^ 2)) ^ 2 ≤ M ^ 2 := by
    have h := abs_le.mp hB
    nlinarith [h.1, h.2, hM0]
  have hCsq : (2 * Real.sin θ / Real.cos θ ^ 3) ^ 2 ≤ M ^ 2 := by
    have h := abs_le.mp hC
    nlinarith [h.1, h.2, hM0]
  have eA : (Real.tan θ * deriv (deriv u) θ) ^ 2 ≤ M ^ 2 * (deriv (deriv u) θ) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hAsq (sq_nonneg _)
  have eB : (2 * (1 / Real.cos θ ^ 2) * deriv u θ) ^ 2 ≤ M ^ 2 * (deriv u θ) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hBsq (sq_nonneg _)
  have eC : (2 * Real.sin θ / Real.cos θ ^ 3 * u θ) ^ 2 ≤ M ^ 2 * (u θ) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hCsq (sq_nonneg _)
  have hexp := sum_five_sq_le (Real.tan θ * deriv (deriv u) θ)
    (2 * (1 / Real.cos θ ^ 2) * deriv u θ) (2 * Real.sin θ / Real.cos θ ^ 3 * u θ)
    (-(6 * deriv u θ)) (-(deriv g θ))
  rw [hid]
  have h2 : 5 * ((Real.tan θ * deriv (deriv u) θ) ^ 2
        + (2 * (1 / Real.cos θ ^ 2) * deriv u θ) ^ 2
        + (2 * Real.sin θ / Real.cos θ ^ 3 * u θ) ^ 2
        + (6 * deriv u θ) ^ 2 + (deriv g θ) ^ 2)
      ≤ 5 * (M ^ 2 + 36) * ((deriv (deriv u) θ) ^ 2 + (deriv u θ) ^ 2 + (u θ) ^ 2
          + (deriv g θ) ^ 2) := by
    nlinarith [eA, eB, eC, sq_nonneg (u θ), sq_nonneg (deriv (deriv u) θ),
      sq_nonneg (deriv u θ), sq_nonneg (deriv g θ), hM0]
  linarith [hexp, h2]

end TripleBound

/-! ## Point bounds for `u`, `u'`, `u''` at `π/4` -/

section PointBounds


/-- Rolle: `u'` vanishes somewhere in the open interval. -/
private lemma exists_deriv_eq_zero {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2))) (h0 : u 0 = 0)
    (h1 : u (Real.pi / 2) = 0) : ∃ ξ ∈ Set.Ioo 0 (Real.pi / 2), deriv u ξ = 0 := by
  have hlt : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hlt huc (hu.differentiableOn (by norm_num))
  refine ⟨c, hc, ?_⟩
  rw [hcd]
  have : u (Real.pi / 2) - u 0 = 0 := by rw [h0, h1]; ring
  rw [this, zero_div]

/-- Triangle inequality for interval integrals, ordered version. -/
private lemma abs_intervalIntegral_le (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := by
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := f) hab
  simpa only [Real.norm_eq_abs] using h

/-- `|f|` is integrable where `f²` is. -/
private lemma integrableOn_abs_of_sq {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AEStronglyMeasurable (fun x => |f x|) (MeasureTheory.volume.restrict s))
    (hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s)
    (h : IntegrableOn (fun x => f x ^ 2) s) : IntegrableOn (fun x => |f x|) s := by
  have hg : IntegrableOn (fun x => (1 / 2) * (1 + f x ^ 2)) s := (hone.add h).const_mul (1 / 2)
  refine hg.mono' hf ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_abs]
  nlinarith [abs_nonneg (f x), sq_abs (f x), sq_nonneg (|f x| - 1)]

/-- Membership of `x` in `uIcc a b` from `x ∈ Ioc a b` (with `a ≤ b`). -/
private lemma mem_uIcc_of_Ioc {a b x : ℝ} (hx : x ∈ Set.Ioc a b) : x ∈ Set.uIcc a b := by
  rw [Set.uIcc, Set.mem_Icc]
  exact ⟨le_trans (min_le_left _ _) (le_of_lt hx.1), le_trans hx.2 (le_max_right _ _)⟩

/-- Membership of `x` in `uIcc a b` from `x ∈ Ioc b a` (with `b ≤ a`). -/
private lemma mem_uIcc_of_Ioc' {a b x : ℝ} (hx : x ∈ Set.Ioc b a) : x ∈ Set.uIcc a b := by
  rw [Set.uIcc, Set.mem_Icc]
  exact ⟨le_trans (min_le_right _ _) (le_of_lt hx.1), le_trans hx.2 (le_max_left _ _)⟩

/-- If `v` is `C¹` on the open interval and `|v'|` is integrable on `s ⊇ uIcc ξ θ`, then
`|v θ - v ξ| ≤ ∫_s |v'|` for interior points `ξ, θ`. -/
private lemma abs_sub_le_integral_abs_on {v : ℝ → ℝ} {s : Set ℝ}
    (hv : ContDiffOn ℝ 1 v (Set.Ioo 0 (Real.pi / 2)))
    (hvint : IntegrableOn (fun x => |deriv v x|) s)
    (hs : s ⊆ Set.Ioo 0 (Real.pi / 2))
    {ξ θ : ℝ} (hξ : ξ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hsub : Set.uIcc ξ θ ⊆ s) : |v θ - v ξ| ≤ ∫ x in s, |deriv v x| := by
  have hcomm : Set.uIcc θ ξ = Set.uIcc ξ θ := by rw [Set.uIcc, Set.uIcc, min_comm, max_comm]
  have hcont : ContinuousOn (deriv v) (Set.uIcc ξ θ) :=
    (hv.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono (fun x hx => hs (hsub hx))
  have hdiff : ∀ x ∈ Set.uIcc ξ θ, DifferentiableAt ℝ v x := fun x hx =>
    (hv.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds (hs (hsub hx)))
  have hmono : ∫ x in (Set.Ioc ξ θ), |deriv v x| ≤ ∫ x in s, |deriv v x| :=
    MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hvint
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub (mem_uIcc_of_Ioc hx))
  have hmono' : ∫ x in (Set.Ioc θ ξ), |deriv v x| ≤ ∫ x in s, |deriv v x| :=
    MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hvint
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub (mem_uIcc_of_Ioc' hx))
  rcases le_total ξ θ with hle | hle
  · have hFTC : ∫ x in ξ..θ, deriv v x = v θ - v ξ :=
      intervalIntegral.integral_deriv_eq_sub' v rfl hdiff hcont
    rw [← hFTC]
    refine le_trans (abs_intervalIntegral_le (deriv v) hle) ?_
    rw [intervalIntegral.integral_of_le hle]
    exact hmono
  · have hFTC : ∫ x in θ..ξ, deriv v x = v ξ - v θ :=
      intervalIntegral.integral_deriv_eq_sub' v rfl
        (fun x hx => hdiff x (by rw [← hcomm]; exact hx))
        (hcont.mono (fun x hx => by rw [← hcomm]; exact hx))
    have hneg : v θ - v ξ = -(∫ x in θ..ξ, deriv v x) := by rw [hFTC]; ring
    rw [hneg, abs_neg]
    refine le_trans (abs_intervalIntegral_le (deriv v) hle) ?_
    rw [intervalIntegral.integral_of_le hle]
    exact hmono'

/-- **B1.** `(u (π/4))² ≤ (π/2)∫(u')²`. -/
private lemma u_sq_le {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2))) (h0 : u 0 = 0)
    (hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ)
    (hC1 : IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ) :
    (u (Real.pi / 4)) ^ 2 ≤ (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 := by
  have hlt : (0 : ℝ) < Real.pi / 4 := by positivity
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), HasDerivAt u (deriv u x) x :=
    fun x hx => (diffAt_of_contDiffOn hu ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩).hasDerivAt
  have habs : IntegrableOn (fun x => |deriv u x|) Work.Spaces.Iθ :=
    integrableOn_abs_of_sq (by simpa only [Real.norm_eq_abs] using
      ((measurable_deriv u).norm).aestronglyMeasurable) hone hC1
  have hint : IntervalIntegrable (deriv u) MeasureTheory.volume 0 (Real.pi / 4) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hlt.le]
    refine (MeasureTheory.integrable_norm_iff (measurable_deriv u).aestronglyMeasurable).mp ?_
    exact habs.mono_set fun x hx => ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hFTC : ∫ x in (0 : ℝ)..(Real.pi / 4), deriv u x = u (Real.pi / 4) - u 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le
      (huc.mono (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)) hderiv hint
  rw [h0, sub_zero] at hFTC
  have h1 : |u (Real.pi / 4)| ≤ ∫ θ in Work.Spaces.Iθ, |deriv u θ| := by
    rw [← hFTC]
    refine le_trans (abs_intervalIntegral_le (deriv u) hlt.le) ?_
    rw [intervalIntegral.integral_of_le hlt.le]
    refine MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) habs
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx => ⟨le_of_lt hx.1, le_of_lt (lt_of_le_of_lt hx.2
        (by linarith [Real.pi_pos]))⟩)
  have h2 : (∫ θ in Work.Spaces.Iθ, |deriv u θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) * (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) := by
    have hu' : MeasureTheory.MemLp (fun θ => |deriv u θ|) 2
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.memLp_two_iff_integrable_sq (by simpa only [Real.norm_eq_abs] using
        ((measurable_deriv u).norm).aestronglyMeasurable)).mpr
        (hC1.congr (Filter.Eventually.of_forall fun θ => (sq_abs (deriv u θ)).symm))
    have h1' : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) 2
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_const).mpr
        (hone.congr (Filter.Eventually.of_forall fun θ => by rw [one_pow]))
    have := Work.Spaces.cs_integral hu' h1'
    simpa only [mul_one, one_pow, sq_abs] using this
  have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, Work.Spaces.Iθ,
      Real.volume_real_Icc_of_le (by linarith [Real.pi_pos])]
    simp
  have h3 : (u (Real.pi / 4)) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, |deriv u θ|) ^ 2 := by
    rw [show (u (Real.pi / 4)) ^ 2 = |u (Real.pi / 4)| ^ 2 from (sq_abs _).symm]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc (u (Real.pi / 4)) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, |deriv u θ|) ^ 2 := h3
    _ ≤ (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) * (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) := h2
    _ = (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 := by rw [hvol]; ring

/-- `sin(2θ)^{-η} ≥ 1` on the open interval. -/
private lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sEta θ := by
  have hpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  rw [sEta]
  calc (1 : ℝ) = (Real.sin (2 * θ)) ^ (0 : ℝ) := (Real.rpow_zero _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _)
          (by linarith [Work.Spaces.eta_pos])

/-- **B2.** `(u'(π/4))² ≤ (π/2)∫(u'')² sin(2θ)^{-η}`. -/
private lemma u'_sq_le {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2))) (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sEta θ) Work.Spaces.Iθ) :
    (deriv u (Real.pi / 4)) ^ 2
      ≤ (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * sEta θ := by
  obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_eq_zero hu huc h0 h1
  have hπ4 : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hsubIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- integrability of `(u'')²` and `|u''|` on the open interval
  have hmono : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := hB.mono_set hsubIoo
  have hInt2 : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine hmono.mono' (((measurable_deriv (deriv u)).pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_sEta hθ)
  have hIntAbs2 : IntegrableOn (fun x => |deriv (deriv u) x|) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_abs_of_sq (by simpa only [Real.norm_eq_abs] using
      ((measurable_deriv (deriv u)).norm).aestronglyMeasurable) hone hInt2
  have hcv : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hsub : Set.uIcc ξ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc, Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le (lt_min hξ.1 hπ4.1) hx.1, lt_of_le_of_lt hx.2 (max_lt hξ.2 hπ4.2)⟩
  have hstep : |deriv u (Real.pi / 4)| ≤ ∫ x in Set.Ioo 0 (Real.pi / 2), |deriv (deriv u) x| := by
    have h := abs_sub_le_integral_abs_on (v := deriv u) hcv hIntAbs2 (fun x hx => hx) hξ hπ4 hsub
    rwa [hξ0, sub_zero] at h
  have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), |deriv (deriv u) θ|) ^ 2
      ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2)
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), (1 : ℝ)) := by
    have hu' : MeasureTheory.MemLp (fun θ => |deriv (deriv u) θ|) 2
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      (MeasureTheory.memLp_two_iff_integrable_sq (by simpa only [Real.norm_eq_abs] using
        ((measurable_deriv (deriv u)).norm).aestronglyMeasurable)).mpr
        (hInt2.congr (Filter.Eventually.of_forall fun θ => (sq_abs (deriv (deriv u) θ)).symm))
    have h1' : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) 2
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_const).mpr
        (hone.congr (Filter.Eventually.of_forall fun θ => by rw [one_pow]))
    have := Work.Spaces.cs_integral hu' h1'
    simpa only [mul_one, one_pow, sq_abs] using this
  have hvol : (∫ θ in Set.Ioo 0 (Real.pi / 2), (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp
  have h3 : (deriv u (Real.pi / 4)) ^ 2
      ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), |deriv (deriv u) θ|) ^ 2 := by
    rw [show (deriv u (Real.pi / 4)) ^ 2 = |deriv u (Real.pi / 4)| ^ 2 from (sq_abs _).symm]
    exact pow_le_pow_left₀ (abs_nonneg _) hstep 2
  have h4 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2)
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * sEta θ := by
    refine MeasureTheory.integral_mono_ae hInt2 hmono ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_sEta hθ)
  have hIθ : (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * sEta θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * sEta θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hIθ]
  calc (deriv u (Real.pi / 4)) ^ 2
      ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), |deriv (deriv u) θ|) ^ 2 := h3
    _ ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), (1 : ℝ)) := h2
    _ ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * sEta θ)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), (1 : ℝ)) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (Real.pi / 2) * ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * sEta θ := by
        rw [hvol]; ring

/-- **B3.** `(u''(π/4))²` is bounded by the squared integrals of `|u''|`, `|u'''|` over `K`. -/
private lemma u''_sq_le {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hInt2 : IntegrableOn (fun x => |deriv (deriv u) x|) (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)))
    (hInt3 : IntegrableOn (fun x => |deriv (deriv (deriv u)) x|)
      (Set.Icc (Real.pi / 8) (3 * Real.pi / 8))) :
    (deriv (deriv u) (Real.pi / 4)) ^ 2
      ≤ 8 * ((∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8), |deriv (deriv u) x|) ^ 2
          + (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
              |deriv (deriv (deriv u)) x|) ^ 2) := by
  set K := Set.Icc (Real.pi / 8) (3 * Real.pi / 8) with hK
  have ha : Real.pi / 8 < 3 * Real.pi / 8 := by linarith [Real.pi_pos]
  have hmem : ∀ x ∈ K, x ∈ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [hK, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hcont2 : ContinuousOn (deriv (deriv u)) (Set.uIcc (Real.pi / 8) (3 * Real.pi / 8)) := by
    rw [Set.uIcc_of_le ha.le]
    exact ((hu.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num)).mono (fun x hx => hmem x hx)
  obtain ⟨c, hc, hcd⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (f := deriv (deriv u)) (g := fun _ : ℝ => (1 : ℝ)) (μ := MeasureTheory.volume) hcont2
    intervalIntegrable_const (fun x hx => zero_le_one)
  have hcK : c ∈ K := by simpa only [hK, Set.uIcc_of_le ha.le] using hc
  have hcIoo : c ∈ Set.Ioo 0 (Real.pi / 2) := hmem c hcK
  have hπ4 : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hπ4K : Real.pi / 4 ∈ K := by
    rw [hK, Set.mem_Icc]; exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- the mean value step
  have hMVT : |deriv (deriv u) c| ≤ 2 * ∫ x in K, |deriv (deriv u) x| := by
    have hvol : (∫ x in (Real.pi / 8)..(3 * Real.pi / 8), (1 : ℝ)) = Real.pi / 4 := by
      rw [intervalIntegral.integral_const]; ring
    have hEq : deriv (deriv u) c * (Real.pi / 4)
        = ∫ x in (Real.pi / 8)..(3 * Real.pi / 8), deriv (deriv u) x := by
      rw [← hvol]
      simpa only [mul_one] using hcd.symm
    have h1 : |deriv (deriv u) c| * (Real.pi / 4)
        = |∫ x in (Real.pi / 8)..(3 * Real.pi / 8), deriv (deriv u) x| := by
      rw [← hEq]
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < Real.pi / 4 by linarith [Real.pi_pos])]
    have h2 : |∫ x in (Real.pi / 8)..(3 * Real.pi / 8), deriv (deriv u) x|
        ≤ ∫ x in (Real.pi / 8)..(3 * Real.pi / 8), |deriv (deriv u) x| :=
      abs_intervalIntegral_le _ ha.le
    have h3 : ∫ x in (Real.pi / 8)..(3 * Real.pi / 8), |deriv (deriv u) x|
        ≤ ∫ x in K, |deriv (deriv u) x| := by
      rw [intervalIntegral.integral_of_le ha.le]
      exact MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hInt2
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
    have h4 : |deriv (deriv u) c| * (Real.pi / 4) ≤ ∫ x in K, |deriv (deriv u) x| := by
      rw [h1]; exact le_trans h2 h3
    have h5 : (0 : ℝ) ≤ ∫ x in K, |deriv (deriv u) x| :=
      MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => abs_nonneg _)
    nlinarith [Real.pi_gt_three, abs_nonneg (deriv (deriv u) c), h4, h5]
  -- FTC between `c` and `π/4`
  have hcv : ContDiffOn ℝ 1 (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    (hu.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 1) (by norm_num)
  have hsub : Set.uIcc c (Real.pi / 4) ⊆ K := by
    intro x hx
    rw [Set.uIcc, Set.mem_Icc] at hx
    rw [hK, Set.mem_Icc]
    exact ⟨le_trans (le_min hcK.1 hπ4K.1) hx.1, le_trans hx.2 (max_le hcK.2 hπ4K.2)⟩
  have hstep : |deriv (deriv u) (Real.pi / 4) - deriv (deriv u) c|
      ≤ ∫ x in K, |deriv (deriv (deriv u)) x| :=
    abs_sub_le_integral_abs_on (v := deriv (deriv u)) hcv hInt3 (fun x hx => hmem x hx) hcIoo hπ4
      hsub
  have htri : |deriv (deriv u) (Real.pi / 4)|
      ≤ |deriv (deriv u) (Real.pi / 4) - deriv (deriv u) c| + |deriv (deriv u) c| := by
    have := abs_add_le (deriv (deriv u) (Real.pi / 4) - deriv (deriv u) c) (deriv (deriv u) c)
    rwa [sub_add_cancel] at this
  have hfin : |deriv (deriv u) (Real.pi / 4)| ≤ (2 * (∫ x in K, |deriv (deriv u) x|))
      + ∫ x in K, |deriv (deriv (deriv u)) x| := by
    linarith [htri, hstep, hMVT]
  have hnn1 : (0 : ℝ) ≤ ∫ x in K, |deriv (deriv u) x| :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => abs_nonneg _)
  have hnn2 : (0 : ℝ) ≤ ∫ x in K, |deriv (deriv (deriv u)) x| :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => abs_nonneg _)
  rw [show (deriv (deriv u) (Real.pi / 4)) ^ 2 = |deriv (deriv u) (Real.pi / 4)| ^ 2 from
    (sq_abs _).symm]
  calc |deriv (deriv u) (Real.pi / 4)| ^ 2
      ≤ (2 * (∫ x in K, |deriv (deriv u) x|) + ∫ x in K, |deriv (deriv (deriv u)) x|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hfin 2
    _ ≤ 8 * ((∫ x in K, |deriv (deriv u) x|) ^ 2
          + (∫ x in K, |deriv (deriv (deriv u)) x|) ^ 2) := by
        nlinarith [sq_nonneg ((∫ x in K, |deriv (deriv u) x|)
          - ∫ x in K, |deriv (deriv (deriv u)) x|), hnn1, hnn2]
end PointBounds

/-! ## The two half-interval bounds -/

section Halves

/-- Cauchy–Schwarz over a set, in the form `(∫_s |f|)² ≤ (∫_s f²)(∫_s 1)`. -/
private lemma cs_interval {f : ℝ → ℝ} {s : Set ℝ}
    (hfi : IntegrableOn (fun x => f x ^ 2) s)
    (hfm : AEStronglyMeasurable (fun x => |f x|) (MeasureTheory.volume.restrict s))
    (hfin : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s) :
    (∫ x in s, |f x|) ^ 2 ≤ (∫ x in s, f x ^ 2) * (∫ x in s, (1 : ℝ)) := by
  have hmem1 : MeasureTheory.MemLp (fun x => |f x|) 2 (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hfm).mpr
      (hfi.congr (Filter.Eventually.of_forall fun x => (sq_abs (f x)).symm))
  have hmem2 : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) 2 (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_const).mpr
      (hfin.congr (Filter.Eventually.of_forall fun x => by rw [one_pow]))
  have h := Work.Spaces.cs_integral hmem1 hmem2
  simpa only [mul_one, one_pow, sq_abs] using h

/-- `volume` of an open/closed-open interval is finite. -/
private lemma volume_Ioc_ne_top (a b : ℝ) : MeasureTheory.volume (Set.Ioc a b) ≠ ⊤ := by
  rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

private lemma volume_Ioo_ne_top (a b : ℝ) : MeasureTheory.volume (Set.Ioo a b) ≠ ⊤ := by
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

/-- `∫_s 1 = volume.real s` on an interval. -/
private lemma integral_one_Ioo (a b : ℝ) (hab : a ≤ b) :
    (∫ _ in Set.Ioo a b, (1 : ℝ)) = b - a := by
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo_of_le hab]
  simp

/-- Weighted bound on the right half `(π/4, π/2)`. -/
private lemma half_right {σ φ : ℝ → ℝ}
    (hσle : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), σ θ ≤ 1)
    (hσpos : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), 0 < σ θ)
    (hσanti : AntitoneOn σ (Set.Icc (Real.pi / 4) (Real.pi / 2)))
    (hσint : IntegrableOn σ (Set.Ioo (Real.pi / 4) (Real.pi / 2)))
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioo 0 (Real.pi / 2)))
    (hD : IntegrableOn (fun t => (deriv φ t) ^ 2 * σ t) (Set.Ioo (Real.pi / 4) (Real.pi / 2)))
    (hmeas : AEStronglyMeasurable (fun θ => (φ θ) ^ 2 * σ θ)
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2)))) :
    IntegrableOn (fun θ => (φ θ) ^ 2 * σ θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) ∧
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (φ θ) ^ 2 * σ θ)
      ≤ 4 * ((φ (Real.pi / 4)) ^ 2
          + ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t) := by
  have hπ4 : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hIsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  -- ### the pointwise core
  have hcore : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (φ θ - φ (Real.pi / 4)) ^ 2 * σ θ ≤ (θ - Real.pi / 4)
        * ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t := by
    intro θ hθ
    have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      rw [Set.uIcc, Set.mem_Icc] at hx
      exact ⟨lt_of_lt_of_le (lt_min hπ4.1 (by linarith [hθ.1, Real.pi_pos])) hx.1,
        lt_of_le_of_lt hx.2 (max_lt hπ4.2 hθ.2)⟩
    have hcont : ContinuousOn (deriv φ) (Set.uIcc (Real.pi / 4) θ) :=
      (hφ.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono (fun x hx => hsub hx)
    have hFTC : ∫ t in (Real.pi / 4)..θ, deriv φ t = φ θ - φ (Real.pi / 4) :=
      intervalIntegral.integral_deriv_eq_sub
        (fun x hx => (hφ.differentiableOn (by norm_num)).differentiableAt
          (isOpen_Ioo.mem_nhds (hsub hx))) hcont.intervalIntegrable
    have h1 : |φ θ - φ (Real.pi / 4)| ≤ ∫ t in Set.Ioc (Real.pi / 4) θ, |deriv φ t| := by
      have h := abs_intervalIntegral_le (deriv φ) hθ.1.le
      rwa [hFTC, intervalIntegral.integral_of_le hθ.1.le] at h
    have hIocsub : Set.Ioc (Real.pi / 4) θ ⊆ Set.Ioo (Real.pi / 4) (Real.pi / 2) :=
      fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hθIcc : θ ∈ Set.Icc (Real.pi / 4) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hσmono : ∀ t ∈ Set.Ioc (Real.pi / 4) θ, σ θ ≤ σ t := by
      intro t ht
      exact hσanti (a := t) (b := θ) ⟨le_of_lt (hIocsub ht).1, le_of_lt (hIocsub ht).2⟩ hθIcc
        ht.2
    have hDloc : IntegrableOn (fun t => (deriv φ t) ^ 2 * σ t) (Set.Ioc (Real.pi / 4) θ) :=
      hD.mono_set hIocsub
    have hInt_sq : IntegrableOn (fun t => (deriv φ t) ^ 2) (Set.Ioc (Real.pi / 4) θ) := by
      refine (hDloc.const_mul (1 / σ θ)).mono'
        (((measurable_deriv φ).pow_const 2).aestronglyMeasurable) ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hle : σ θ ≤ σ t := hσmono t ht
      have hsq : (0 : ℝ) ≤ (deriv φ t) ^ 2 := sq_nonneg _
      calc (deriv φ t) ^ 2 = (1 / σ θ) * ((deriv φ t) ^ 2 * σ θ) := by
            field_simp [ne_of_gt (hσpos θ hθ)]
        _ ≤ (1 / σ θ) * ((deriv φ t) ^ 2 * σ t) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hsq)
              (le_of_lt (one_div_pos.mpr (hσpos θ hθ)))
    have hfin : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (Real.pi / 4) θ) :=
      integrableOn_const (s := Set.Ioc (Real.pi / 4) θ)
        (volume_Ioc_ne_top _ _)
    have h2 : (∫ t in Set.Ioc (Real.pi / 4) θ, |deriv φ t|) ^ 2
        ≤ (θ - Real.pi / 4) * ∫ t in Set.Ioc (Real.pi / 4) θ, (deriv φ t) ^ 2 := by
      have h := cs_interval (f := deriv φ) hInt_sq
        (by simpa only [Real.norm_eq_abs, abs_abs] using
          ((measurable_deriv φ).norm).aestronglyMeasurable) hfin
      have hvol : (∫ t in Set.Ioc (Real.pi / 4) θ, (1 : ℝ)) = θ - Real.pi / 4 := by
        rw [← intervalIntegral.integral_of_le hθ.1.le, intervalIntegral.integral_const]
        ring
      rw [hvol] at h
      simpa only [mul_comm] using h
    have hC : σ θ * (∫ t in Set.Ioc (Real.pi / 4) θ, (deriv φ t) ^ 2)
        ≤ ∫ t in Set.Ioc (Real.pi / 4) θ, (deriv φ t) ^ 2 * σ t := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t => mul_nonneg (le_of_lt (hσpos θ hθ)) (sq_nonneg _))
        hDloc ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t ht
      calc σ θ * (deriv φ t) ^ 2 ≤ σ t * (deriv φ t) ^ 2 :=
            mul_le_mul_of_nonneg_right (hσmono t ht) (sq_nonneg _)
        _ = (deriv φ t) ^ 2 * σ t := by ring
    have hDle : (∫ t in Set.Ioc (Real.pi / 4) θ, (deriv φ t) ^ 2 * σ t)
        ≤ ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t := by
      refine MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hD ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact mul_nonneg (sq_nonneg _) (le_of_lt (hσpos t ht))
      · exact Filter.Eventually.of_forall fun t ht => hIocsub ht
    have hSq : (φ θ - φ (Real.pi / 4)) ^ 2 ≤ (∫ t in Set.Ioc (Real.pi / 4) θ, |deriv φ t|) ^ 2 := by
      rw [← sq_abs (φ θ - φ (Real.pi / 4))]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc (φ θ - φ (Real.pi / 4)) ^ 2 * σ θ
        ≤ (∫ t in Set.Ioc (Real.pi / 4) θ, |deriv φ t|) ^ 2 * σ θ :=
          mul_le_mul_of_nonneg_right hSq (le_of_lt (hσpos θ hθ))
      _ ≤ ((θ - Real.pi / 4) * ∫ t in Set.Ioc (Real.pi / 4) θ, (deriv φ t) ^ 2) * σ θ :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt (hσpos θ hθ))
      _ = (θ - Real.pi / 4) * (σ θ * ∫ t in Set.Ioc (Real.pi / 4) θ, (deriv φ t) ^ 2) := by ring
      _ ≤ (θ - Real.pi / 4) * (∫ t in Set.Ioc (Real.pi / 4) θ, (deriv φ t) ^ 2 * σ t) :=
          mul_le_mul_of_nonneg_left hC (by linarith [hθ.1])
      _ ≤ (θ - Real.pi / 4) * (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2),
            (deriv φ t) ^ 2 * σ t) :=
          mul_le_mul_of_nonneg_left hDle (by linarith [hθ.1])
  -- ### pointwise domination by the model function
  have hpt : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (φ θ) ^ 2 * σ θ ≤ 2 * (φ (Real.pi / 4)) ^ 2 * σ θ
        + (2 * (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t))
          * (θ - Real.pi / 4) := by
    intro θ hθ
    have h1 : (φ θ) ^ 2 ≤ 2 * (φ (Real.pi / 4)) ^ 2 + 2 * (φ θ - φ (Real.pi / 4)) ^ 2 := by
      nlinarith [sq_nonneg (φ (Real.pi / 4) - (φ θ - φ (Real.pi / 4)))]
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (hσpos θ hθ))
    have h3 := hcore θ hθ
    nlinarith [h2, h3]
  -- ### integrability of the model function
  have hint2 : IntegrableOn (fun θ : ℝ => θ - Real.pi / 4) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    (((continuousOn_id.sub continuousOn_const).integrableOn_compact isCompact_Icc).mono_set
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  have hmodel : IntegrableOn (fun θ => 2 * (φ (Real.pi / 4)) ^ 2 * σ θ
      + (2 * (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t))
          * (θ - Real.pi / 4)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    (hσint.const_mul (2 * (φ (Real.pi / 4)) ^ 2)).add (hint2.const_mul (2 * _))
  have hInt : IntegrableOn (fun θ => (φ θ) ^ 2 * σ θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine hmodel.mono' hmeas ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (hσpos θ hθ)))]
    exact hpt θ hθ
  refine ⟨hInt, ?_⟩
  -- ### the integral estimate
  have hcmp : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (φ θ) ^ 2 * σ θ)
      ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (2 * (φ (Real.pi / 4)) ^ 2 * σ θ
          + (2 * (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t))
              * (θ - Real.pi / 4)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hmodel ?_
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hσpos θ hθ))
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact hpt θ hθ
  have hsplit : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (2 * (φ (Real.pi / 4)) ^ 2 * σ θ
        + (2 * (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t))
            * (θ - Real.pi / 4)))
      = 2 * (φ (Real.pi / 4)) ^ 2 * (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), σ θ)
        + (2 * (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t))
            * (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), θ - Real.pi / 4) := by
    rw [MeasureTheory.integral_add (hσint.const_mul _) (hint2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hσbd : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), σ θ) ≤ Real.pi / 4 := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2)))
      (f := σ) (g := fun _ : ℝ => (1 : ℝ))
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact le_of_lt (hσpos θ hθ))
      (integrableOn_const (s := Set.Ioo (Real.pi / 4) (Real.pi / 2))
        (volume_Ioo_ne_top _ _))
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact hσle θ hθ)
    rw [integral_one_Ioo (Real.pi / 4) (Real.pi / 2) (by linarith [Real.pi_pos])] at h
    linarith [Real.pi_pos]
  have hlin : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), θ - Real.pi / 4) ≤ Real.pi / 4 := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2)))
      (f := fun θ : ℝ => θ - Real.pi / 4) (g := fun _ : ℝ => Real.pi / 4)
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact sub_nonneg.mpr (le_of_lt hθ.1))
      (integrableOn_const (s := Set.Ioo (Real.pi / 4) (Real.pi / 2))
        (volume_Ioo_ne_top _ _))
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          have := hθ.2; linarith [Real.pi_pos])
    have hc : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (Real.pi / 4 : ℝ))
        = Real.pi / 4 * (Real.pi / 4) := by
      rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
      simp only [smul_eq_mul, mul_one]
      ring
    rw [hc] at h
    nlinarith [Real.pi_pos, Real.pi_lt_four, h]
  have hσnn : (0 : ℝ) ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), σ θ :=
    MeasureTheory.integral_nonneg_of_ae
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact le_of_lt (hσpos θ hθ))
  have hDnn : (0 : ℝ) ≤ ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv φ t) ^ 2 * σ t :=
    MeasureTheory.integral_nonneg_of_ae
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
          exact mul_nonneg (sq_nonneg _) (le_of_lt (hσpos t ht)))
  rw [hsplit] at hcmp
  nlinarith [hcmp, hσbd, hlin, hσnn, hDnn, Real.pi_lt_four, sq_nonneg (φ (Real.pi / 4))]

/-- Weighted bound on the left half `(0, π/4)`. -/
private lemma half_left {σ φ : ℝ → ℝ}
    (hσle : ∀ θ ∈ Set.Ioo 0 (Real.pi / 4), σ θ ≤ 1)
    (hσpos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 4), 0 < σ θ)
    (hσmono : MonotoneOn σ (Set.Icc 0 (Real.pi / 4)))
    (hσint : IntegrableOn σ (Set.Ioo 0 (Real.pi / 4)))
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioo 0 (Real.pi / 2)))
    (hD : IntegrableOn (fun t => (deriv φ t) ^ 2 * σ t) (Set.Ioo 0 (Real.pi / 4)))
    (hmeas : AEStronglyMeasurable (fun θ => (φ θ) ^ 2 * σ θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 4)))) :
    IntegrableOn (fun θ => (φ θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 4)) ∧
    (∫ θ in Set.Ioo 0 (Real.pi / 4), (φ θ) ^ 2 * σ θ)
      ≤ 4 * ((φ (Real.pi / 4)) ^ 2
          + ∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t) := by
  have hπ4 : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hIsub : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  -- ### the pointwise core
  have hcore : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (φ θ - φ (Real.pi / 4)) ^ 2 * σ θ ≤ (Real.pi / 4 - θ)
        * ∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t := by
    intro θ hθ
    have hθIcc : θ ∈ Set.Icc 0 (Real.pi / 4) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      rw [Set.uIcc, Set.mem_Icc] at hx
      exact ⟨lt_of_lt_of_le (lt_min hθ.1 (by linarith [Real.pi_pos])) hx.1,
        lt_of_le_of_lt hx.2 (max_lt (by linarith [hθ.2, Real.pi_pos]) hπ4.2)⟩
    have hcont : ContinuousOn (deriv φ) (Set.uIcc θ (Real.pi / 4)) :=
      (hφ.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono (fun x hx => hsub hx)
    have hFTC : ∫ t in θ..(Real.pi / 4), deriv φ t = φ (Real.pi / 4) - φ θ :=
      intervalIntegral.integral_deriv_eq_sub
        (fun x hx => (hφ.differentiableOn (by norm_num)).differentiableAt
          (isOpen_Ioo.mem_nhds (hsub hx))) hcont.intervalIntegrable
    have h1 : |φ θ - φ (Real.pi / 4)| ≤ ∫ t in Set.Ioo θ (Real.pi / 4), |deriv φ t| := by
      have h := abs_intervalIntegral_le (deriv φ) hθ.2.le
      have h2 : φ θ - φ (Real.pi / 4) = -(∫ t in θ..(Real.pi / 4), deriv φ t) := by
        rw [hFTC]; ring
      rw [h2, abs_neg, intervalIntegral.integral_of_le hθ.2.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      simp only [intervalIntegral.integral_of_le hθ.2.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
      exact h
    have hIoosub : Set.Ioo θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 4) :=
      fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
    have hσmono : ∀ t ∈ Set.Ioo θ (Real.pi / 4), σ θ ≤ σ t := by
      intro t ht
      exact hσmono (a := θ) (b := t) hθIcc
        ⟨le_of_lt (lt_trans hθ.1 ht.1), le_of_lt (hIoosub ht).2⟩ (le_of_lt ht.1)
    have hDloc : IntegrableOn (fun t => (deriv φ t) ^ 2 * σ t) (Set.Ioo θ (Real.pi / 4)) :=
      hD.mono_set hIoosub
    have hInt_sq : IntegrableOn (fun t => (deriv φ t) ^ 2) (Set.Ioo θ (Real.pi / 4)) := by
      refine (hDloc.const_mul (1 / σ θ)).mono'
        (((measurable_deriv φ).pow_const 2).aestronglyMeasurable) ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hle : σ θ ≤ σ t := hσmono t ht
      have hsq : (0 : ℝ) ≤ (deriv φ t) ^ 2 := sq_nonneg _
      calc (deriv φ t) ^ 2 = (1 / σ θ) * ((deriv φ t) ^ 2 * σ θ) := by
            field_simp [ne_of_gt (hσpos θ hθ)]
        _ ≤ (1 / σ θ) * ((deriv φ t) ^ 2 * σ t) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hsq)
              (le_of_lt (one_div_pos.mpr (hσpos θ hθ)))
    have hfin : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo θ (Real.pi / 4)) :=
      integrableOn_const (s := Set.Ioo θ (Real.pi / 4)) (volume_Ioo_ne_top _ _)
    have h2 : (∫ t in Set.Ioo θ (Real.pi / 4), |deriv φ t|) ^ 2
        ≤ (Real.pi / 4 - θ) * ∫ t in Set.Ioo θ (Real.pi / 4), (deriv φ t) ^ 2 := by
      have h := cs_interval (f := deriv φ) hInt_sq
        (by simpa only [Real.norm_eq_abs, abs_abs] using
          ((measurable_deriv φ).norm).aestronglyMeasurable) hfin
      have hvol : (∫ t in Set.Ioo θ (Real.pi / 4), (1 : ℝ)) = Real.pi / 4 - θ :=
        integral_one_Ioo θ (Real.pi / 4) hθ.2.le
      rw [hvol] at h
      simpa only [mul_comm] using h
    have hC : σ θ * (∫ t in Set.Ioo θ (Real.pi / 4), (deriv φ t) ^ 2)
        ≤ ∫ t in Set.Ioo θ (Real.pi / 4), (deriv φ t) ^ 2 * σ t := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t => mul_nonneg (le_of_lt (hσpos θ hθ)) (sq_nonneg _))
        hDloc ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
      calc σ θ * (deriv φ t) ^ 2 ≤ σ t * (deriv φ t) ^ 2 :=
            mul_le_mul_of_nonneg_right (hσmono t ht) (sq_nonneg _)
        _ = (deriv φ t) ^ 2 * σ t := by ring
    have hDle : (∫ t in Set.Ioo θ (Real.pi / 4), (deriv φ t) ^ 2 * σ t)
        ≤ ∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t := by
      refine MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hD ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact mul_nonneg (sq_nonneg _) (le_of_lt (hσpos t ht))
      · exact Filter.Eventually.of_forall fun t ht => hIoosub ht
    have hSq : (φ θ - φ (Real.pi / 4)) ^ 2
        ≤ (∫ t in Set.Ioo θ (Real.pi / 4), |deriv φ t|) ^ 2 := by
      rw [← sq_abs (φ θ - φ (Real.pi / 4))]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc (φ θ - φ (Real.pi / 4)) ^ 2 * σ θ
        ≤ (∫ t in Set.Ioo θ (Real.pi / 4), |deriv φ t|) ^ 2 * σ θ :=
          mul_le_mul_of_nonneg_right hSq (le_of_lt (hσpos θ hθ))
      _ ≤ ((Real.pi / 4 - θ) * ∫ t in Set.Ioo θ (Real.pi / 4), (deriv φ t) ^ 2) * σ θ :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt (hσpos θ hθ))
      _ = (Real.pi / 4 - θ) * (σ θ * ∫ t in Set.Ioo θ (Real.pi / 4), (deriv φ t) ^ 2) := by
          ring
      _ ≤ (Real.pi / 4 - θ) * (∫ t in Set.Ioo θ (Real.pi / 4), (deriv φ t) ^ 2 * σ t) :=
          mul_le_mul_of_nonneg_left hC (by linarith [hθ.2])
      _ ≤ (Real.pi / 4 - θ) * (∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t) :=
          mul_le_mul_of_nonneg_left hDle (by linarith [hθ.2])
  -- ### pointwise domination by the model function
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 4),
      (φ θ) ^ 2 * σ θ ≤ 2 * (φ (Real.pi / 4)) ^ 2 * σ θ
        + (2 * (∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t))
          * (Real.pi / 4 - θ) := by
    intro θ hθ
    have h1 : (φ θ) ^ 2 ≤ 2 * (φ (Real.pi / 4)) ^ 2 + 2 * (φ θ - φ (Real.pi / 4)) ^ 2 := by
      nlinarith [sq_nonneg (φ (Real.pi / 4) - (φ θ - φ (Real.pi / 4)))]
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (hσpos θ hθ))
    have h3 := hcore θ hθ
    nlinarith [h2, h3]
  -- ### integrability of the model function
  have hint2 : IntegrableOn (fun θ : ℝ => Real.pi / 4 - θ) (Set.Ioo 0 (Real.pi / 4)) :=
    (((continuousOn_const.sub continuousOn_id).integrableOn_compact isCompact_Icc).mono_set
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  have hmodel : IntegrableOn (fun θ => 2 * (φ (Real.pi / 4)) ^ 2 * σ θ
      + (2 * (∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t))
          * (Real.pi / 4 - θ)) (Set.Ioo 0 (Real.pi / 4)) :=
    (hσint.const_mul (2 * (φ (Real.pi / 4)) ^ 2)).add (hint2.const_mul (2 * _))
  have hInt : IntegrableOn (fun θ => (φ θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 4)) := by
    refine hmodel.mono' hmeas ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (hσpos θ hθ)))]
    exact hpt θ hθ
  refine ⟨hInt, ?_⟩
  -- ### the integral estimate
  have hcmp : (∫ θ in Set.Ioo 0 (Real.pi / 4), (φ θ) ^ 2 * σ θ)
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 4), (2 * (φ (Real.pi / 4)) ^ 2 * σ θ
          + (2 * (∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t))
              * (Real.pi / 4 - θ)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hmodel ?_
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hσpos θ hθ))
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact hpt θ hθ
  have hsplit : (∫ θ in Set.Ioo 0 (Real.pi / 4), (2 * (φ (Real.pi / 4)) ^ 2 * σ θ
        + (2 * (∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t))
            * (Real.pi / 4 - θ)))
      = 2 * (φ (Real.pi / 4)) ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 4), σ θ)
        + (2 * (∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t))
            * (∫ θ in Set.Ioo 0 (Real.pi / 4), Real.pi / 4 - θ) := by
    rw [MeasureTheory.integral_add (hσint.const_mul _) (hint2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hσbd : (∫ θ in Set.Ioo 0 (Real.pi / 4), σ θ) ≤ Real.pi / 4 := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 4)))
      (f := σ) (g := fun _ : ℝ => (1 : ℝ))
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact le_of_lt (hσpos θ hθ))
      (integrableOn_const (s := Set.Ioo 0 (Real.pi / 4)) (volume_Ioo_ne_top _ _))
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact hσle θ hθ)
    rw [integral_one_Ioo 0 (Real.pi / 4) (by linarith [Real.pi_pos])] at h
    linarith [h]
  have hlin : (∫ θ in Set.Ioo 0 (Real.pi / 4), Real.pi / 4 - θ) ≤ Real.pi / 4 := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 4)))
      (f := fun θ : ℝ => Real.pi / 4 - θ) (g := fun _ : ℝ => Real.pi / 4)
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact sub_nonneg.mpr (le_of_lt hθ.2))
      (integrableOn_const (s := Set.Ioo 0 (Real.pi / 4)) (volume_Ioo_ne_top _ _))
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          have := hθ.1; linarith [Real.pi_pos])
    have hc : (∫ θ in Set.Ioo 0 (Real.pi / 4), (Real.pi / 4 : ℝ))
        = Real.pi / 4 * (Real.pi / 4) := by
      rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
      simp only [smul_eq_mul, mul_one]
      ring
    rw [hc] at h
    nlinarith [Real.pi_pos, Real.pi_lt_four, h]
  have hσnn : (0 : ℝ) ≤ ∫ θ in Set.Ioo 0 (Real.pi / 4), σ θ :=
    MeasureTheory.integral_nonneg_of_ae
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact le_of_lt (hσpos θ hθ))
  have hDnn : (0 : ℝ) ≤ ∫ t in Set.Ioo 0 (Real.pi / 4), (deriv φ t) ^ 2 * σ t :=
    MeasureTheory.integral_nonneg_of_ae
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
          exact mul_nonneg (sq_nonneg _) (le_of_lt (hσpos t ht)))
  rw [hsplit] at hcmp
  nlinarith [hcmp, hσbd, hlin, hσnn, hDnn, Real.pi_lt_four, sq_nonneg (φ (Real.pi / 4))]

end Halves

/-- `Lzero1 u` is `C¹` on the open interval when `u` is `C³` there. -/
private lemma contDiffOn_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 1 (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  have htanC : ContDiffOn ℝ 3 Real.tan (Set.Ioo 0 (Real.pi / 2)) := by
    have htan_eq : Real.tan = fun x => Real.sin x * (Real.cos x)⁻¹ :=
      funext fun x => by rw [Real.tan_eq_sin_div_cos, div_eq_mul_inv]
    rw [htan_eq]
    exact Real.contDiff_sin.contDiffOn.mul
      (Real.contDiff_cos.contDiffOn.inv (fun x hx => cos_ne_zero_of_Ioo hx))
  have h1 : ContDiffOn ℝ 1 (fun t => -(deriv (deriv u) t)) (Set.Ioo 0 (Real.pi / 2)) :=
    ((hu.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 1) (by norm_num)).neg
  have h2 : ContDiffOn ℝ 1 (fun t => deriv (fun s => Real.tan s * u s) t)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (htanC.mul (hu.of_le (by norm_num))).deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have h3 : ContDiffOn ℝ 1 (fun t => 6 * u t) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.mul (hu.of_le (by norm_num))
  exact (h1.add h2).sub h3


end

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.wsSliceRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The right-end limit of an angular slice with honest `Lzero1`-source.**

A single integration of `Lzero1 u = -u'' + (tan θ · u)' - 6u` over `(π/4, b)` gives

  `tan b · u b = ∫_{π/4}^b Lzero1 u + u'(b) - u'(π/4) + tan(π/4)·u(π/4) + 6∫_{π/4}^b u`,

whose right hand side is bounded uniformly in `b < π/2`: the first term by the total mass of
`|Lzero1 u|` on `Iθ` (hypothesis `hL`), the second by writing `u'(b) - u'(π/4)` as the integral
of `u''` (hypothesis `h2`, whose weight `sEta ≥ 1` makes `|u''|` integrable), and the last by the
total mass of `|u|` (hypothesis `hu`).  Hence `|tan b · u b| ≤ K`, so
`|u θ| ≤ K·cos θ / sin θ → 0` as `θ → (π/2)⁻`. -/
theorem wsSliceRight {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hu : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have h4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- ### a.e. strong measurability of the three functions
  have huaesm : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hsm.continuousOn.aemeasurable measurableSet_Ioo).aestronglyMeasurable
  have h2aesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => deriv (fun t => deriv u t) θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (measurable_deriv (fun t => deriv u t)).aestronglyMeasurable
  have hLaesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    show MeasureTheory.AEStronglyMeasurable
      (fun θ => -(deriv (fun t => deriv u t) θ) + deriv (fun t => Real.tan t * u t) θ
        - 6 * u θ) _
    exact (((measurable_deriv (fun t => deriv u t)).neg.aestronglyMeasurable).add
      ((measurable_deriv (fun t => Real.tan t * u t)).aestronglyMeasurable)).sub
      (huaesm.const_mul 6)
  -- ### the three absolute-value integrabilities on the open interval
  have huabs : MeasureTheory.IntegrableOn (fun θ => |u θ|)
      (Set.Ioo 0 (Real.pi / 2)) := SourceBound.absIntegrableOfSq huaesm hu
  have h2abs : MeasureTheory.IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) := SourceBound.absIntegrableOfSqMulSeta h2aesm h2
  have hLabs : MeasureTheory.IntegrableOn (fun θ => |Work.FTS.EllipticEst.Lzero1 u θ|)
      (Set.Ioo 0 (Real.pi / 2)) := SourceBound.absIntegrableOfSqMulSeta hLaesm hL
  -- ### the constant `K`
  set A : ℝ := ∫ x in Set.Ioo 0 (Real.pi / 2), |Work.FTS.EllipticEst.Lzero1 u x| with hA
  set B : ℝ := ∫ x in Set.Ioo 0 (Real.pi / 2), |deriv (fun t => deriv u t) x| with hB
  set C : ℝ := ∫ x in Set.Ioo 0 (Real.pi / 2), |u x| with hC
  have hAnn : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun x => abs_nonneg _)
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun x => abs_nonneg _)
  have hCnn : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun x => abs_nonneg _)
  set K : ℝ := |Real.tan (Real.pi / 4) * u (Real.pi / 4)| + A + B + 6 * C with hK
  refine SourceBound.tendstoOfAbsLeCosDivSin (K := K) ?_
  intro θ hθ
  have hθπ : Real.pi / 4 < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  have hsubIcc : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hpi4 hx.1, lt_of_le_of_lt hx.2 hθ2⟩
  -- ### the fundamental theorem of calculus for `u''`
  have hdu_c : ContinuousOn (deriv u) (Set.Icc (Real.pi / 4) θ) :=
    ((hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn).mono hsubIcc
  have hd2_c : ContinuousOn (fun x => deriv (fun t => deriv u t) x)
      (Set.Icc (Real.pi / 4) θ) := by
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
      hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    have h0 : ContDiffOn ℝ 0 (fun x => deriv (fun t => deriv u t) x)
        (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
    exact h0.continuousOn.mono hsubIcc
  have hderiv2 : ∀ x ∈ Set.Ioo (Real.pi / 4) θ,
      HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hsubIcc ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have h2x : ContDiffAt ℝ 2 u x := hsm.contDiffAt (isOpen_Ioo.mem_nhds hx')
    have h1x : ContDiffAt ℝ 1 (deriv u) x := h2x.derivWithin (by norm_num)
    exact (h1x.differentiableAt (by norm_num)).hasDerivAt
  have hIint2 : IntervalIntegrable (fun x => deriv (fun t => deriv u t) x) volume
      (Real.pi / 4) θ := by
    have hc : ContinuousOn (fun x => deriv (fun t => deriv u t) x)
        (Set.uIcc (Real.pi / 4) θ) := by
      rw [Set.uIcc_of_le hθπ.le]; exact hd2_c
    exact hc.intervalIntegrable
  have hftc2 : ∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x
      = deriv u θ - deriv u (Real.pi / 4) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθπ.le hdu_c hderiv2 hIint2
  -- ### the combined identity
  have hid := SourceBound.tanuIdentity hsm hpi4 hθπ hθ2
  have hcomb : Real.tan θ * u θ
      = (∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
        + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
        + Real.tan (Real.pi / 4) * u (Real.pi / 4)
        + 6 * (∫ x in (Real.pi / 4)..θ, u x) := by
    linarith [hid, hftc2]
  -- ### bound each of the three interval integrals by its total mass
  have hIocJ : Set.Ioc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_trans hpi4 hx.1, lt_of_le_of_lt hx.2 hθ2⟩
  have hbL : |∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x| ≤ A := by
    rw [hA]
    have h1 : |∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x|
        ≤ ∫ x in (Real.pi / 4)..θ, |Work.FTS.EllipticEst.Lzero1 u x| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun x => Work.FTS.EllipticEst.Lzero1 u x) hθπ.le
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le hθπ.le]
    exact setIntegral_mono_set hLabs (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hIocJ hx))
  have hb2 : |∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x| ≤ B := by
    rw [hB]
    have h1 : |∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x|
        ≤ ∫ x in (Real.pi / 4)..θ, |deriv (fun t => deriv u t) x| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun x => deriv (fun t => deriv u t) x) hθπ.le
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le hθπ.le]
    exact setIntegral_mono_set h2abs (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hIocJ hx))
  have hbC : |∫ x in (Real.pi / 4)..θ, u x| ≤ C := by
    rw [hC]
    have h1 : |∫ x in (Real.pi / 4)..θ, u x| ≤ ∫ x in (Real.pi / 4)..θ, |u x| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := u) hθπ.le
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le hθπ.le]
    exact setIntegral_mono_set huabs (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hIocJ hx))
  -- ### the resulting bound on `tan θ · u θ`
  have hbound : |Real.tan θ * u θ| ≤ K := by
    rw [hK]
    have htri : |(∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
        + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
        + Real.tan (Real.pi / 4) * u (Real.pi / 4)
        + 6 * (∫ x in (Real.pi / 4)..θ, u x)| ≤
        |∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x|
        + |∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x|
        + |Real.tan (Real.pi / 4) * u (Real.pi / 4)|
        + |6 * (∫ x in (Real.pi / 4)..θ, u x)| := by
      have h1 := abs_add_le ((∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
          + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
          + Real.tan (Real.pi / 4) * u (Real.pi / 4))
        (6 * (∫ x in (Real.pi / 4)..θ, u x))
      have h2 := abs_add_le ((∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
          + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x))
        (Real.tan (Real.pi / 4) * u (Real.pi / 4))
      have h3 := abs_add_le (∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
        (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
      linarith
    have h6 : |6 * (∫ x in (Real.pi / 4)..θ, u x)| = 6 * |∫ x in (Real.pi / 4)..θ, u x| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    rw [hcomb]
    have h6le : |6 * (∫ x in (Real.pi / 4)..θ, u x)| ≤ 6 * C := by
      rw [h6]; exact mul_le_mul_of_nonneg_left hbC (by norm_num)
    linarith [hbL, hb2, h6le]
  -- ### pass from `tan θ · u θ` to `u θ`
  have htan : 0 < Real.tan θ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (lt_trans hpi4 hθπ) hθ2
  have hKey : |u θ| = |Real.tan θ * u θ| / Real.tan θ := by
    rw [abs_mul, abs_of_pos htan]
    field_simp
  rw [hKey]
  calc |Real.tan θ * u θ| / Real.tan θ
      ≤ K / Real.tan θ := div_le_div_of_nonneg_right hbound htan.le
    _ = K * (Real.cos θ / Real.sin θ) := by
        rw [div_eq_mul_inv, Real.tan_eq_sin_div_cos, inv_div]

end

end Work.FTS.EllipticEst.remov
end
