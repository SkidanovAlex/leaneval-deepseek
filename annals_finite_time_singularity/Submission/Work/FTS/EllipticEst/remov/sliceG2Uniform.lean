import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.SliceG2Defs
import Submission.Work.Spaces.cs_integral

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

/-- `σ` is bounded below on the compact `[π/8, 3π/8]`. -/
private lemma sigG_ge_on_K (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8), c ≤ sigG γ θ := by
  have hmem : ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hKsub : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨le_of_lt (hmem x hx).1, le_of_lt (hmem x hx).2⟩
  have hcont : ContinuousOn (fun θ => (sigG γ θ)⁻¹) (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
    ((sigG_continuousOn γ hγ1 hγ2).mono hKsub).inv₀
      (fun θ hθ => ne_of_gt (sigG_pos γ hγ1 hγ2 θ (hmem θ hθ)))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := Real.pi / 8) (b := 3 * Real.pi / 8)).bddAbove_image
    hcont
  refine ⟨(max M 1)⁻¹, inv_pos.mpr (lt_max_of_lt_right zero_lt_one), fun θ hθ => ?_⟩
  have hM1 : 0 < max M 1 := lt_max_of_lt_right zero_lt_one
  have hpos : 0 < sigG γ θ := sigG_pos γ hγ1 hγ2 θ (hmem θ hθ)
  refine (inv_le_comm₀ hpos hM1).mp ?_
  exact le_trans (hM ⟨θ, hθ, rfl⟩) (le_max_left _ _)


/-- **Uniform** lower bound for `σ = sigG γ` on the fixed compact `[π/8, 3π/8]`: the constant
is independent of `γ ∈ [1, 3/2]`.  There `2θ ∈ [π/4, 3π/4]`, so `sin(2θ) ≥ 1/2`, and since
`2 - γ ≤ 1` and `0 < sin(2θ) ≤ 1` we have `sin(2θ)^{2-γ} ≥ sin(2θ) ≥ 1/2`. -/
private lemma sigG_ge_on_K_u :
    ∃ c : ℝ, 0 < c ∧ ∀ (γ : ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8), c ≤ sigG γ θ := by
  refine ⟨1 / 2, by norm_num, fun γ hγ1 hγ2 θ hθ => ?_⟩
  rw [Set.mem_Icc] at hθ
  have h2θ1 : Real.pi / 4 ≤ 2 * θ := by linarith [hθ.1, Real.pi_pos]
  have h2θ2 : 2 * θ ≤ 3 * Real.pi / 4 := by linarith [hθ.2, Real.pi_pos]
  have hsin_half : (1 : ℝ) / 2 ≤ Real.sin (2 * θ) := by
    by_cases hle : 2 * θ ≤ Real.pi / 2
    · have h := Real.mul_le_sin (by linarith [Real.pi_pos]) hle
      have h' : (2 / Real.pi) * (Real.pi / 4) ≤ (2 / Real.pi) * (2 * θ) :=
        mul_le_mul_of_nonneg_left h2θ1 (by positivity)
      have h2 : (2 / Real.pi) * (Real.pi / 4) = 1 / 2 := by field_simp; ring
      linarith [h, h', h2.symm.le]
    · have hsub : Real.sin (2 * θ) = Real.sin (Real.pi - 2 * θ) := by
        rw [Real.sin_pi_sub]
      rw [hsub]
      have h1 : (0 : ℝ) ≤ Real.pi - 2 * θ := by linarith
      have h2 : Real.pi - 2 * θ ≤ Real.pi / 2 := by linarith
      have h := Real.mul_le_sin h1 h2
      have h3 : Real.pi - 2 * θ ≥ Real.pi / 4 := by linarith
      have h' : (2 / Real.pi) * (Real.pi / 4) ≤ (2 / Real.pi) * (Real.pi - 2 * θ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h4 : (2 / Real.pi) * (Real.pi / 4) = 1 / 2 := by field_simp; ring
      linarith [h, h', h4.symm.le]
  have hpos : 0 < Real.sin (2 * θ) := by linarith
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : 2 - γ ≤ 1 := by linarith [hγ2]
  have hmono := Real.rpow_le_rpow_of_exponent_ge hpos hle1 hexp
  rw [Real.rpow_one] at hmono
  have hsig : Real.sin (2 * θ) ≤ sigG γ θ := by
    rw [sigG_eq]
    exact hmono
  linarith

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

/-- **The `∫g²σ`-bound.**  For `σ = sin(2θ)^{2-γ}`, `1 ≤ γ ≤ 3/2`:
`∫ g²σ ≤ C (∫ (g')²σ + ∫ (u'')²sEta + ∫ (u')² + ∫ u²)`.

Proof route.  Take a fixed interior point, say `x₀ = π/4`, and the fixed compact
`K = [π/8, 3π/8]`.  On `K`, `σ`, `sEta` and the coefficients `tan θ, sec²θ` are bounded above
and below, and `u''' = (tan θ · u)'' - 6u' - g'` with bounded coefficients, so
`∫_K (u''')² ≤ C(∫_K (u'')² + ∫_K (u')² + ∫_K u² + ∫_K (g')²) ≤ C(B + C₁ + C₀ + D)`.
The mean-value/Sobolev argument (choose `ξ ∈ K` with `u''(ξ) = (1/|K|)∫_K u''`) gives
`|u''(x₀)| ≤ C(∫_K|u''| + ∫_K|u'''|)`, and Cauchy–Schwarz bounds this by
`C(B+C₁+C₀+D)^{1/2}`; similarly for `u'(x₀)` and `u(x₀)`.  Hence `g(x₀)² ≤ C(B+C₁+C₀+D)`.
Then split `Iθ` at `x₀`: on `(x₀, π/2)`, `|g(θ)| ≤ |g(3π/8)| + ∫_θ^{3π/8}|g'|`, and
`∫_θ^{3π/8} σ(θ')(θ'-θ) dθ' ≤ C σ(θ)` for `θ' ≥ θ` since `σ` is decreasing there; swapping
the order of integration gives `∫_{(x₀,π/2)} g²σ ≤ C(g(3π/8)² + ∫ g'²σ)`.  The left half is the
same with the reference point `x₀`.  (Note `g(π/2) ≠ 0` is possible, e.g. `u = c(π/4)²... `, so
no Hardy inequality with `g(π/2) = 0` may be invoked.)
-/
theorem sliceG2Uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  obtain ⟨Ct, hCt0, hCt⟩ := u_triple_bound_K
  obtain ⟨c, hc0, hcge⟩ := sigG_ge_on_K_u
  refine ⟨8 * (1000 * (1 + Ct) * (1 + 1 / c)) + 4, by positivity, ?_⟩
  intro γ u g hγ1 hγ2 hu huc h0 h1 hg hB hC1 hC0 hD
  set K := Set.Icc (Real.pi / 8) (3 * Real.pi / 8) with hK
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * sEta θ with hBdef
  set C1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hC1def
  set C0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hC0def
  set D : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * sigG γ θ with hDdef
  -- ### basic facts
  have hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ sigG γ θ := sigG_nonneg γ hγ1 hγ2
  have hσle : ∀ θ ∈ Work.Spaces.Iθ, sigG γ θ ≤ 1 := sigG_le_one γ hγ1 hγ2
  have hσpos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < sigG γ θ := sigG_pos γ hγ1 hγ2
  have hσmonoL : MonotoneOn (sigG γ) (Set.Icc 0 (Real.pi / 4)) := sigG_monoOn γ hγ1 hγ2
  have hσantiR : AntitoneOn (sigG γ) (Set.Icc (Real.pi / 4) (Real.pi / 2)) :=
    sigG_antitoneOn γ hγ1 hγ2
  have hSeta1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (1 : ℝ) ≤ sEta θ := fun θ hθ => one_le_sEta hθ
  have honeIθ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (s := Work.Spaces.Iθ) (by
      rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have honeIoo : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_const (s := Set.Ioo 0 (Real.pi / 2)) (volume_Ioo_ne_top _ _)
  have honeK : IntegrableOn (fun _ : ℝ => (1 : ℝ)) K :=
    integrableOn_const (s := K) (by rw [hK, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hKsubIθ : K ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [hK, Set.mem_Icc] at hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hKsubIoo : K ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [hK, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _))
  have hC1nn : (0 : ℝ) ≤ C1 := by
    rw [hC1def]
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  have hC0nn : (0 : ℝ) ≤ C0 := by
    rw [hC0def]
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  have hDnn : (0 : ℝ) ≤ D := by
    rw [hDdef]
    exact MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  -- ### Step 1: the point bound at `π/4`
  have hB1 : (u (Real.pi / 4)) ^ 2 ≤ (Real.pi / 2) * C1 := by
    have := u_sq_le hu huc h0 honeIθ hC1
    rwa [← hC1def] at this
  have hB2 : (deriv u (Real.pi / 4)) ^ 2 ≤ (Real.pi / 2) * B := by
    have := u'_sq_le hu huc h0 h1 honeIoo hB
    rwa [← hBdef] at this
  have hB_K : IntegrableOn (fun x => (deriv (deriv u) x) ^ 2 * sEta x) K := hB.mono_set hKsubIθ
  have hInt2_K : IntegrableOn (fun x => (deriv (deriv u) x) ^ 2) K := by
    refine hB_K.mono' (((measurable_deriv (deriv u)).pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (hSeta1 x (hKsubIoo hx))
  have hIntAbs2_K : IntegrableOn (fun x => |deriv (deriv u) x|) K :=
    integrableOn_abs_of_sq (by simpa only [Real.norm_eq_abs] using
      ((measurable_deriv (deriv u)).norm).aestronglyMeasurable) honeK hInt2_K
  have hD_K : IntegrableOn (fun x => (deriv g x) ^ 2 * sigG γ x) K := hD.mono_set hKsubIθ
  have hDg2_K : IntegrableOn (fun x => (deriv g x) ^ 2) K := by
    refine (hD_K.const_mul (1 / c)).mono'
      (((measurable_deriv g).pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (deriv g x) ^ 2 = (1 / c) * (c * (deriv g x) ^ 2) := by
          field_simp
      _ ≤ (1 / c) * ((deriv g x) ^ 2 * sigG γ x) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc c * (deriv g x) ^ 2 ≤ sigG γ x * (deriv g x) ^ 2 :=
                mul_le_mul_of_nonneg_right (hcge γ hγ1 hγ2 x hx) (sq_nonneg _)
            _ = (deriv g x) ^ 2 * sigG γ x := by ring
  have hRHS_K : IntegrableOn (fun x => Ct * ((deriv (deriv u) x) ^ 2 + (deriv u x) ^ 2
      + (u x) ^ 2 + (deriv g x) ^ 2)) K :=
    (((hInt2_K.add (hC1.mono_set hKsubIθ)).add (hC0.mono_set hKsubIθ)).add hDg2_K).const_mul Ct
  have hInt3sq_K : IntegrableOn (fun x => (deriv (deriv (deriv u)) x) ^ 2) K := by
    refine hRHS_K.mono' (((measurable_deriv (deriv (deriv u))).pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hCt u g hu hg x hx
  have hIntAbs3_K : IntegrableOn (fun x => |deriv (deriv (deriv u)) x|) K :=
    integrableOn_abs_of_sq (by simpa only [Real.norm_eq_abs, abs_abs] using
      ((measurable_deriv (deriv (deriv u))).norm).aestronglyMeasurable) honeK hInt3sq_K
  have hKvol : (∫ x in K, (1 : ℝ)) = Real.pi / 4 := by
    rw [hK, MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith [Real.pi_pos])]
    simp only [smul_eq_mul]
    ring
  have hInt2K_le : (∫ x in K, (deriv (deriv u) x) ^ 2) ≤ B := by
    rw [hBdef]
    refine le_trans ?_ (MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hB
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hx) _))
      (Filter.Eventually.of_forall fun x hx => hKsubIθ hx))
    refine MeasureTheory.integral_mono_of_nonneg
      (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
          exact sq_nonneg _) hB_K ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
    exact le_mul_of_one_le_right (sq_nonneg _) (hSeta1 x (hKsubIoo hx))
  have hDg2K_le : (∫ x in K, (deriv g x) ^ 2) ≤ (1 / c) * D := by
    have h1 : (∫ x in K, (deriv g x) ^ 2) ≤ (1 / c) * ∫ x in K, (deriv g x) ^ 2 * sigG γ x := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg
        (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
            exact sq_nonneg _) (hD_K.const_mul _) ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
      calc (deriv g x) ^ 2 = (1 / c) * (c * (deriv g x) ^ 2) := by field_simp
        _ ≤ (1 / c) * ((deriv g x) ^ 2 * sigG γ x) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc c * (deriv g x) ^ 2 ≤ sigG γ x * (deriv g x) ^ 2 :=
                  mul_le_mul_of_nonneg_right (hcge γ hγ1 hγ2 x hx) (sq_nonneg _)
              _ = (deriv g x) ^ 2 * sigG γ x := by ring
    have h2 : (∫ x in K, (deriv g x) ^ 2 * sigG γ x) ≤ D := by
      rw [hDdef]
      exact MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hD
        (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
            exact mul_nonneg (sq_nonneg _) (hσnn x hx))
        (Filter.Eventually.of_forall fun x hx => hKsubIθ hx)
    calc (∫ x in K, (deriv g x) ^ 2) ≤ (1 / c) * ∫ x in K, (deriv g x) ^ 2 * sigG γ x := h1
      _ ≤ (1 / c) * D := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hTripleInt : (∫ x in K, (deriv (deriv (deriv u)) x) ^ 2)
      ≤ Ct * (1 + 1 / c) * (B + C1 + C0 + D) := by
    have h1 : (∫ x in K, (deriv (deriv (deriv u)) x) ^ 2)
        ≤ ∫ x in K, Ct * ((deriv (deriv u) x) ^ 2 + (deriv u x) ^ 2 + (u x) ^ 2
            + (deriv g x) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
            exact sq_nonneg _) hRHS_K ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
      exact hCt u g hu hg x hx
    have hI_a : IntegrableOn (fun x => (deriv (deriv u) x) ^ 2 + (deriv u x) ^ 2) K :=
      hInt2_K.add (hC1.mono_set hKsubIθ)
    have hI_b : IntegrableOn (fun x => ((deriv (deriv u) x) ^ 2 + (deriv u x) ^ 2)
        + (u x) ^ 2) K := hI_a.add (hC0.mono_set hKsubIθ)
    have hI_c : IntegrableOn (fun x => (((deriv (deriv u) x) ^ 2 + (deriv u x) ^ 2)
        + (u x) ^ 2) + (deriv g x) ^ 2) K := hI_b.add hDg2_K
    have h2 : (∫ x in K, Ct * (((deriv (deriv u) x) ^ 2 + (deriv u x) ^ 2 + (u x) ^ 2)
            + (deriv g x) ^ 2))
        = Ct * ((∫ x in K, (deriv (deriv u) x) ^ 2) + (∫ x in K, (deriv u x) ^ 2)
            + (∫ x in K, (u x) ^ 2) + (∫ x in K, (deriv g x) ^ 2)) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add hI_b hDg2_K,
        MeasureTheory.integral_add hI_a (hC0.mono_set hKsubIθ),
        MeasureTheory.integral_add hInt2_K (hC1.mono_set hKsubIθ)]
    rw [h2] at h1
    have h3 : (∫ x in K, (deriv u x) ^ 2) ≤ C1 := by
      rw [hC1def]
      exact MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hC1
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hKsubIθ hx)
    have h4 : (∫ x in K, (u x) ^ 2) ≤ C0 := by
      rw [hC0def]
      exact MeasureTheory.setIntegral_mono_set (μ := MeasureTheory.volume) hC0
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hKsubIθ hx)
    have hpc : (0 : ℝ) ≤ 1 / c := by positivity
    have hBC : (0 : ℝ) ≤ B + C1 + C0 := by linarith
    have h5 : Ct * ((∫ x in K, (deriv (deriv u) x) ^ 2) + (∫ x in K, (deriv u x) ^ 2)
        + (∫ x in K, (u x) ^ 2) + (∫ x in K, (deriv g x) ^ 2))
        ≤ Ct * ((1 + 1 / c) * (B + C1 + C0 + D)) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCt0)
      nlinarith [hInt2K_le, h3, h4, hDg2K_le, hpc, hBC, hBnn, hC1nn, hC0nn, hDnn,
        mul_nonneg hpc hBC, mul_nonneg hpc hDnn]
    linarith [h1, h5]
  have hA2sq : (∫ x in K, |deriv (deriv u) x|) ^ 2 ≤ B * (Real.pi / 4) := by
    have h := cs_interval (f := deriv (deriv u)) hInt2_K
      (by simpa only [Real.norm_eq_abs, abs_abs] using
        ((measurable_deriv (deriv u)).norm).aestronglyMeasurable) honeK
    rw [hKvol] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hInt2K_le (by positivity))
  have hA3sq : (∫ x in K, |deriv (deriv (deriv u)) x|) ^ 2
      ≤ Ct * (1 + 1 / c) * (B + C1 + C0 + D) * (Real.pi / 4) := by
    have h := cs_interval (f := deriv (deriv (deriv u))) hInt3sq_K
      (by simpa only [Real.norm_eq_abs, abs_abs] using
        ((measurable_deriv (deriv (deriv u))).norm).aestronglyMeasurable) honeK
    rw [hKvol] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hTripleInt (by positivity))
  have hB3 := u''_sq_le hu hIntAbs2_K hIntAbs3_K
  have hpt : (Work.FTS.EllipticEst.Lzero1 u (Real.pi / 4)) ^ 2
      ≤ 1000 * (1 + Ct) * (1 + 1 / c) * (B + C1 + C0 + D) := by
    have hval : Work.FTS.EllipticEst.Lzero1 u (Real.pi / 4)
        = -deriv (deriv u) (Real.pi / 4) + deriv u (Real.pi / 4) - 4 * u (Real.pi / 4) := by
      rw [Work.FTS.EllipticEst.Lzero1]
      have htan : deriv (fun t => Real.tan t * u t) (Real.pi / 4)
          = 2 * u (Real.pi / 4) + 1 * deriv u (Real.pi / 4) := by
        rw [deriv_tan_mul (θ := Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          (diffAt_of_contDiffOn hu ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩),
          Real.tan_pi_div_four, Real.cos_pi_div_four]
        have hc2 : (1 : ℝ) / (Real.sqrt 2 / 2) ^ 2 = 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        rw [hc2]
      rw [htan]
      ring
    rw [hval]
    have h1 : (-deriv (deriv u) (Real.pi / 4) + deriv u (Real.pi / 4)
        - 4 * u (Real.pi / 4)) ^ 2
        ≤ 3 * ((deriv (deriv u) (Real.pi / 4)) ^ 2 + (deriv u (Real.pi / 4)) ^ 2
            + (4 * u (Real.pi / 4)) ^ 2) := by
      have h := sum_three_sq_le (-deriv (deriv u) (Real.pi / 4)) (deriv u (Real.pi / 4))
        (-(4 * u (Real.pi / 4)))
      rw [neg_sq] at h
      linarith [h]
    set W : ℝ := Ct * (1 + 1 / c) with hW
    set Y : ℝ := B + C1 + C0 + D with hY
    have hW0 : (0 : ℝ) ≤ W := by rw [hW]; positivity
    have hY0 : (0 : ℝ) ≤ Y := by rw [hY]; linarith
    have hA2' : (∫ x in K, |deriv (deriv u) x|) ^ 2 ≤ (Real.pi / 4) * Y := by
      have hY' : B ≤ Y := by rw [hY]; linarith [hBnn, hC1nn, hC0nn, hDnn]
      calc (∫ x in K, |deriv (deriv u) x|) ^ 2 ≤ B * (Real.pi / 4) := hA2sq
        _ ≤ Y * (Real.pi / 4) :=
            mul_le_mul_of_nonneg_right hY' (by linarith [Real.pi_pos])
        _ = (Real.pi / 4) * Y := by ring
    have hA3' : (∫ x in K, |deriv (deriv (deriv u)) x|) ^ 2 ≤ (Real.pi / 4) * (W * Y) := by
      have heq : W * Y * (Real.pi / 4) = (Real.pi / 4) * (W * Y) := by ring
      simpa only [heq] using hA3sq
    have hB1' : (u (Real.pi / 4)) ^ 2 ≤ (Real.pi / 2) * Y := by
      have hY' : C1 ≤ Y := by rw [hY]; linarith [hBnn, hC1nn, hC0nn, hDnn]
      calc (u (Real.pi / 4)) ^ 2 ≤ (Real.pi / 2) * C1 := hB1
        _ ≤ (Real.pi / 2) * Y := mul_le_mul_of_nonneg_left hY' (by linarith [Real.pi_pos])
    have hB2' : (deriv u (Real.pi / 4)) ^ 2 ≤ (Real.pi / 2) * Y := by
      have hY' : B ≤ Y := by rw [hY]; linarith [hBnn, hC1nn, hC0nn, hDnn]
      calc (deriv u (Real.pi / 4)) ^ 2 ≤ (Real.pi / 2) * B := hB2
        _ ≤ (Real.pi / 2) * Y := mul_le_mul_of_nonneg_left hY' (by linarith [Real.pi_pos])
    have hB3' : (deriv (deriv u) (Real.pi / 4)) ^ 2
        ≤ 8 * ((Real.pi / 4) * Y + (Real.pi / 4) * (W * Y)) := by
      refine le_trans hB3 ?_
      linarith [hA2', hA3']
    have h4u : (4 * u (Real.pi / 4)) ^ 2 ≤ 16 * ((Real.pi / 2) * Y) := by
      rw [mul_pow]
      nlinarith [hB1', hY0]
    have hfin : 3 * ((deriv (deriv u) (Real.pi / 4)) ^ 2 + (deriv u (Real.pi / 4)) ^ 2
        + (4 * u (Real.pi / 4)) ^ 2) ≤ (100 + 100 * W) * Y := by
      nlinarith [hB3', hB2', hB1', h4u, hW0, hY0, Real.pi_pos, Real.pi_lt_four,
        mul_nonneg hW0 hY0]
    have hcoef : 100 + 100 * W ≤ 1000 * ((1 + Ct) * (1 + 1 / c)) := by
      have h1c : (0 : ℝ) ≤ 1 / c := by positivity
      have hV1 : (1 : ℝ) ≤ (1 + Ct) * (1 + 1 / c) := by nlinarith [le_of_lt hCt0]
      have hVW : W ≤ (1 + Ct) * (1 + 1 / c) := by
        rw [hW]; nlinarith [le_of_lt hCt0]
      nlinarith [hV1, hVW]
    have h2 : 3 * ((deriv (deriv u) (Real.pi / 4)) ^ 2 + (deriv u (Real.pi / 4)) ^ 2
        + (4 * u (Real.pi / 4)) ^ 2) ≤ 1000 * (1 + Ct) * (1 + 1 / c) * (B + C1 + C0 + D) := by
      refine le_trans hfin (le_trans (mul_le_mul_of_nonneg_right hcoef hY0) (le_of_eq ?_))
      rw [← hY]
      ring
    linarith [h1, h2]
  -- ### Step 2: the two halves
  have hderivId : ∀ θ ∈ Work.Spaces.Iθ, (deriv g θ) ^ 2 * sigG γ θ
      = (deriv (Work.FTS.EllipticEst.Lzero1 u) θ) ^ 2 * sigG γ θ := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [← hθ0, sigG_zero_left γ hγ1 hγ2]; ring
    · rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
      · rw [hθ1, sigG_zero_right γ hγ1 hγ2]; ring
      · rw [deriv_g_eq hg ⟨hθ0, hθ1⟩]
  have hvalId : ∀ θ ∈ Work.Spaces.Iθ, (g θ) ^ 2 * sigG γ θ
      = (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [← hθ0, sigG_zero_left γ hγ1 hγ2]; ring
    · rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
      · rw [hθ1, sigG_zero_right γ hγ1 hγ2]; ring
      · rw [hg θ ⟨hθ0, hθ1⟩]
  have hvalInt : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      = ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hvalId θ hθ)
  have hDΦ : D = ∫ θ in Work.Spaces.Iθ, (deriv (Work.FTS.EllipticEst.Lzero1 u) θ) ^ 2 * sigG γ θ := by
    rw [hDdef]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hderivId θ hθ)
  have hDΦ_int : IntegrableOn (fun θ => (deriv (Work.FTS.EllipticEst.Lzero1 u) θ) ^ 2 * sigG γ θ)
      Work.Spaces.Iθ :=
    hD.congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      exact (hderivId θ hθ))
  have hΦ : ContDiffOn ℝ 1 (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_Lzero1 hu
  have hmeasΦ : AEStronglyMeasurable
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (((hΦ.continuousOn.pow 2).mul ((sigG_continuousOn γ hγ1 hγ2).mono
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))).aestronglyMeasurable measurableSet_Ioo)
  have hsubLIθ : Set.Ioo 0 (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt (lt_trans hx.2 (by linarith [Real.pi_pos]))⟩
  have hsubRIθ : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt (lt_trans (by linarith [Real.pi_pos]) hx.1), le_of_lt hx.2⟩
  have hsubLIoo : Set.Ioo 0 (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hsubRIoo : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans (by linarith [Real.pi_pos]) hx.1, hx.2⟩
  obtain ⟨hIntL, hbL⟩ := half_left (σ := sigG γ) (φ := Work.FTS.EllipticEst.Lzero1 u)
    (fun θ hθ => hσle θ ⟨le_of_lt hθ.1, le_of_lt (lt_trans hθ.2 (by linarith [Real.pi_pos]))⟩)
    (fun θ hθ => hσpos θ ⟨hθ.1, lt_trans hθ.2 (by linarith [Real.pi_pos])⟩)
    hσmonoL (sigG_integrableOn_Ioo γ hγ1 hγ2 (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
    hΦ (hDΦ_int.mono_set hsubLIθ)
    (hmeasΦ.mono_set hsubLIoo)
  obtain ⟨hIntR, hbR⟩ := half_right (σ := sigG γ) (φ := Work.FTS.EllipticEst.Lzero1 u)
    (fun θ hθ => hσle θ ⟨le_of_lt (lt_trans (by linarith [Real.pi_pos]) hθ.1), le_of_lt hθ.2⟩)
    (fun θ hθ => hσpos θ ⟨lt_trans (by linarith [Real.pi_pos]) hθ.1, hθ.2⟩)
    hσantiR (sigG_integrableOn_Ioo γ hγ1 hγ2 (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
    hΦ (hDΦ_int.mono_set hsubRIθ)
    (hmeasΦ.mono_set hsubRIoo)
  -- ### Step 3: assembly
  have hI1 : IntervalIntegrable (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
      MeasureTheory.volume 0 (Real.pi / 4) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith [Real.pi_pos])]
    exact hIntL.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hI2 : IntervalIntegrable (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
      MeasureTheory.volume (Real.pi / 4) (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith [Real.pi_pos])]
    exact hIntR.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hSplit : (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 4), (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
        + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
            (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ) := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 4),
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi / 2),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hDl_eq : (∫ t in Set.Ioo 0 (Real.pi / 4),
        (deriv (Work.FTS.EllipticEst.Lzero1 u) t) ^ 2 * sigG γ t)
      = ∫ t in Set.Ioo 0 (Real.pi / 4), (deriv g t) ^ 2 * sigG γ t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    exact (hderivId t ⟨le_of_lt ht.1, le_of_lt (lt_trans ht.2 (by linarith [Real.pi_pos]))⟩).symm
  have hDr_eq : (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (deriv (Work.FTS.EllipticEst.Lzero1 u) t) ^ 2 * sigG γ t)
      = ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv g t) ^ 2 * sigG γ t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    exact (hderivId t ⟨le_of_lt (lt_trans (by linarith [Real.pi_pos]) ht.1), le_of_lt ht.2⟩).symm
  have hI3 : IntervalIntegrable (fun θ => (deriv g θ) ^ 2 * sigG γ θ)
      MeasureTheory.volume 0 (Real.pi / 4) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith [Real.pi_pos])]
    exact (hD.mono_set hsubLIθ).congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hI4 : IntervalIntegrable (fun θ => (deriv g θ) ^ 2 * sigG γ θ)
      MeasureTheory.volume (Real.pi / 4) (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith [Real.pi_pos])]
    exact (hD.mono_set hsubRIθ).congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hDsum : (∫ t in Set.Ioo 0 (Real.pi / 4),
        (deriv (Work.FTS.EllipticEst.Lzero1 u) t) ^ 2 * sigG γ t)
      + (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          (deriv (Work.FTS.EllipticEst.Lzero1 u) t) ^ 2 * sigG γ t) = D := by
    have hbridge : (∫ t in Set.Ioo 0 (Real.pi / 4), (deriv g t) ^ 2 * sigG γ t)
        + (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv g t) ^ 2 * sigG γ t) = D := by
      rw [hDdef, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
      rw [← intervalIntegral.integral_add_adjacent_intervals hI3 hI4]
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 4),
        MeasureTheory.integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi / 2),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [hDl_eq, hDr_eq]
    exact hbridge
  refine ⟨?_, ?_⟩
  · -- integrability of `g²σ`
    have hL : IntegrableOn (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
        (Set.Ioc 0 (Real.pi / 4)) := hIntL.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
    have hR : IntegrableOn (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
        (Set.Ioc (Real.pi / 4) (Real.pi / 2)) := hIntR.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
    have hun := hL.union hR
    rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at hun
    have hun2 := hun.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc.symm)
    exact hun2.congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      exact (hvalId θ hθ).symm)
  · -- the bound
    rw [hvalInt]
    rw [hSplit]
    have hsum : (∫ θ in Set.Ioo 0 (Real.pi / 4), (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
        + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
            (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * sigG γ θ)
        ≤ (8 * (1000 * (1 + Ct) * (1 + 1 / c)) + 4) * (D + B + C1 + C0) := by
      nlinarith [hbL, hbR, hpt, hDsum, hBnn, hC1nn, hC0nn, hDnn, hCt0, hc0]
    exact hsum

end

end Work.FTS.EllipticEst.remov
