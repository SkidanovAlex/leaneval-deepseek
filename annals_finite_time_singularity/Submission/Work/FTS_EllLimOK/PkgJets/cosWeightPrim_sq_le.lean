import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_EllLimOK.PkgJets.CosWeightDefs
import Submission.Work.FTS_EllLimOK.PkgJets.cw_hasDerivAt
import Submission.Work.FTS_EllLimOK.PkgJets.cw_integrable
import Submission.Work.FTS_EllLimOK.PkgJets.cw_Phi_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Bounding the primitive of `sin(2θ)^{-η}/cos(θ)^4`

The goal is the single-`θ` estimate
`(∫_0^θ sin(2s)^{-η}/cos(s)^4 ds)^2 ≤ C · sin(2θ)^{-2η}/cos(θ)^6`.

The whole proof rests on the explicit comparison function
`Φ(θ) = 50 · sin(2θ)^{1-η} / cos(θ)^4`, whose derivative
`Φ'(θ) = 50 · sin(2θ)^{-η} · (2(1-η)cos(2θ) + 8 sin²θ) / cos(θ)^4`
dominates the integrand `g(θ) = sin(2θ)^{-η}/cos(θ)^4` pointwise on `(0, π/2)`, because
`2(1-η)cos(2θ) + 8 sin²θ = 2(1-η) + 4(1+η) sin²θ ≥ 2(1-η) = 1/50` (using `η = 99/100`).
Hence `∫_0^θ g ≤ Φ(θ) - Φ(0) = Φ(θ)`, and `Φ(θ)^2 ≤ 10^4 · sin(2θ)^{-2η}/cos(θ)^6`
since `Φ(θ)^2 = 10^4 sin²θ · sin(2θ)^{-2η}/cos(θ)^6` and `sin²θ ≤ 1`.
-/

/-- `1 - η ≠ 0`, used to evaluate `0 ^ (1 - η)`. -/
lemma cw_one_sub_eta_ne : (1 - Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]

/-- `1 - η ≥ 0`, used for continuity of the `rpow`. -/
lemma cw_one_sub_eta_nonneg : 0 ≤ 1 - Work.Spaces.eta := by norm_num [Work.Spaces.eta]

/-- `Φ(0) = 0`. -/
lemma cwPhi_zero : cwPhi 0 = 0 := by
  unfold cwPhi
  simp [cw_one_sub_eta_ne]

/-- The integrand is nonnegative on the open quadrant. -/
lemma cwG_nonneg {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : 0 ≤ cwG x := by
  have hs : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hc : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], by linarith [hx.2]⟩
  unfold cwG
  exact div_nonneg (Real.rpow_nonneg hs.le _) (pow_nonneg hc.le 4)

/-- `Φ ≥ 0` on the open quadrant. -/
lemma cwPhi_nonneg {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : 0 ≤ cwPhi x := by
  have hs : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hc : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], by linarith [hx.2]⟩
  unfold cwPhi
  positivity

/-- The key pointwise domination `g ≤ Φ'` on the open quadrant. -/
lemma cwG_le_cwPhiD {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : cwG x ≤ cwPhiD x := by
  have hs : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hc : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], by linarith [hx.2]⟩
  have hGnn : 0 ≤ cwG x := cwG_nonneg hx
  have hbracket : (1 : ℝ) ≤
      50 * (2 * (1 - Work.Spaces.eta) * Real.cos (2 * x) + 8 * (Real.sin x) ^ 2) := by
    have hcos2 : Real.cos (2 * x) = 1 - 2 * (Real.sin x) ^ 2 := by
      rw [Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq x]
    have h2 : 2 * (1 - Work.Spaces.eta) * Real.cos (2 * x) + 8 * (Real.sin x) ^ 2
        = 2 * (1 - Work.Spaces.eta) + 4 * (1 + Work.Spaces.eta) * (Real.sin x) ^ 2 := by
      rw [hcos2]; ring
    rw [h2, show Work.Spaces.eta = 99 / 100 from rfl]
    nlinarith [sq_nonneg (Real.sin x)]
  rw [show cwPhiD x =
      (50 * (2 * (1 - Work.Spaces.eta) * Real.cos (2 * x) + 8 * (Real.sin x) ^ 2)) * cwG x by
    unfold cwPhiD cwG; ring]
  calc cwG x = 1 * cwG x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbracket hGnn

/-- `Φ` is continuous on `[0, θ]` for `0 ≤ θ < π/2`. -/
lemma continuousOn_cwPhi {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π / 2) :
    ContinuousOn cwPhi (Set.Icc 0 θ) := by
  have hnum : Continuous (fun t : ℝ => 50 * (Real.sin (2 * t)) ^ (1 - Work.Spaces.eta)) := by
    apply Continuous.const_mul
    apply Continuous.rpow_const
    · exact Real.continuous_sin.comp (continuous_const.mul continuous_id)
    · intro x; right; exact cw_one_sub_eta_nonneg
  have hden : ContinuousOn (fun t : ℝ => (Real.cos t) ^ (4 : ℕ)) (Set.Icc 0 θ) :=
    (Real.continuous_cos.pow 4).continuousOn
  have hnz : ∀ t ∈ Set.Icc 0 θ, (Real.cos t) ^ (4 : ℕ) ≠ 0 := by
    intro t ht
    have : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, ht.1], by linarith [ht.2, h1]⟩
    positivity
  unfold cwPhi
  exact hnum.continuousOn.div hden hnz

/-- Fundamental theorem of calculus for `Φ` on `[0, θ]`. -/
lemma cw_ftc (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (∫ s in (0 : ℝ)..θ, cwPhiD s) = cwPhi θ := by
  have hle : (0 : ℝ) ≤ θ := le_of_lt hθ.1
  have hcont : ContinuousOn cwPhi (Set.Icc 0 θ) := continuousOn_cwPhi hle hθ.2
  have hderiv : ∀ x ∈ Set.Ioo 0 θ, HasDerivAt cwPhi (cwPhiD x) x :=
    fun x hx => cw_hasDerivAt x ⟨hx.1, lt_trans hx.2 hθ.2⟩
  have hint : IntervalIntegrable cwPhiD volume 0 θ := by
    rw [intervalIntegrable_iff, uIoc_of_le hle]
    exact (cw_integrable θ hθ).2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint
  rw [h, cwPhi_zero, sub_zero]

/-- The main estimate: the primitive of `g` is bounded by `Φ`. -/
lemma cw_integral_le (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (∫ s in (0 : ℝ)..θ, cwG s) ≤ cwPhi θ := by
  have hle : (0 : ℝ) ≤ θ := le_of_lt hθ.1
  have hG : IntervalIntegrable cwG volume 0 θ := by
    rw [intervalIntegrable_iff, uIoc_of_le hle]
    exact (cw_integrable θ hθ).1
  have hD : IntervalIntegrable cwPhiD volume 0 θ := by
    rw [intervalIntegrable_iff, uIoc_of_le hle]
    exact (cw_integrable θ hθ).2
  have hle' : (∫ s in (0 : ℝ)..θ, cwG s) ≤ (∫ s in (0 : ℝ)..θ, cwPhiD s) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hle hG hD
      (fun x hx => cwG_le_cwPhiD ⟨hx.1, lt_trans hx.2 hθ.2⟩)
  rwa [cw_ftc θ hθ] at hle'

theorem cosWeightPrim_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      (∫ s in (0 : ℝ)..θ,
          (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) / (Real.cos s) ^ 4) ^ 2
        ≤ C * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / (Real.cos θ) ^ 4)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / (Real.cos θ) ^ 2) := by
  refine ⟨10 ^ 4, by norm_num, ?_⟩
  intro θ hθ
  change (∫ s in (0 : ℝ)..θ, cwG s) ^ 2 ≤ (10 : ℝ) ^ 4 * cwG θ * cwB θ
  have h1 : (∫ s in (0 : ℝ)..θ, cwG s) ≤ cwPhi θ := cw_integral_le θ hθ
  have h0 : 0 ≤ (∫ s in (0 : ℝ)..θ, cwG s) := by
    rw [intervalIntegral.integral_of_le (le_of_lt hθ.1)]
    exact setIntegral_nonneg measurableSet_Ioc
      (fun x hx => cwG_nonneg ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
  calc (∫ s in (0 : ℝ)..θ, cwG s) ^ 2 ≤ (cwPhi θ) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ (10 : ℝ) ^ 4 * cwG θ * cwB θ := cw_Phi_sq_le θ hθ

end Work.FTS_EllLimOK.PkgJets
