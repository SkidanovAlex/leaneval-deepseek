import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.integrableOn_exp_comp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The logarithmic window `|log z - t| ≤ δ`

The `z`-integration of the project is carried out on `Iz = [0,∞)` with the weight `w(z)²`, and
the logarithmic (mollification) estimates are stated in the variable `t = log z`, where the
weight window becomes `|log z - t| ≤ δ`, i.e. `t ∈ [log z - δ, log z + δ]`.

This file proves the integrability of the two `ttIntS`-type windowed quantities.  The key point
is that the window is a *compact* interval in `t`, so on it the factor `exp t` (the Jacobian of
`z = exp t`) is comparable to `z`, and the two `z`-integrals that occur (`w(z)²·∫_θ (∂_θ²G)²σθ`
and the *unweighted* angular integral) are equivalent to each other up to a bounded factor. -/

/-- The radial weight `w` is positive on the positive half-line. -/
private lemma w_pos {u : ℝ} (hu : 0 < u) : 0 < Work.Spaces.w u := by
  have h1 : (0 : ℝ) < (1 + u) ^ 2 := by positivity
  have h2 : (0 : ℝ) < u ^ 2 := by positivity
  have h : Work.Spaces.w u = (1 + u) ^ 2 / u ^ 2 := rfl
  rw [h]
  exact div_pos h1 h2

/-- The radial weight along the substitution `z = exp t` is continuous. -/
private lemma continuous_w_exp : Continuous (fun t : ℝ => Work.Spaces.w (Real.exp t)) := by
  have h : (fun t : ℝ => Work.Spaces.w (Real.exp t))
      = fun t : ℝ => (1 + Real.exp t) ^ 2 / (Real.exp t) ^ 2 := by
    funext t
    rfl
  rw [h]
  exact ((continuous_const.add Real.continuous_exp).pow 2).div (Real.continuous_exp.pow 2)
    (fun t => pow_ne_zero 2 (Real.exp_ne_zero t))

/-- The logarithmic window is the interval `[log z - δ, log z + δ]`. -/
private lemma window_eq_Icc {δ z : ℝ} :
    {t : ℝ | |Real.log z - t| ≤ δ} = Set.Icc (Real.log z - δ) (Real.log z + δ) := by
  ext t
  rw [Set.mem_ofPred_eq, abs_le, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- On the window, the weight `w²` is bounded below: for `0 < u ≤ v`,
`(w u ^ 2)⁻¹ ≤ v ^ 4`. -/
private lemma w_sq_inv_le_pow_four (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    ((Work.Spaces.w u) ^ 2)⁻¹ ≤ v ^ 4 := by
  have hw : (Work.Spaces.w u) ^ 2 = (1 + u) ^ 4 / u ^ 4 := by
    have h : Work.Spaces.w u = (1 + u) ^ 2 / u ^ 2 := rfl
    rw [h, div_pow]
    ring
  rw [hw, inv_div]
  calc u ^ 4 / (1 + u) ^ 4 ≤ u ^ 4 :=
        div_le_self (le_of_lt (pow_pos hu 4)) (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + u))
    _ ≤ v ^ 4 := pow_le_pow_left₀ hu.le huv 4

/-- The `θ`-part of `ttIntS`, recovered from `ttIntS` by dividing out the weight `w²`. -/
private lemma inv_w_sq_mul_ttIntS (G : ℝ → ℝ → ℝ) (u : ℝ) (hu : 0 < u) :
    ((Work.Spaces.w u) ^ 2)⁻¹ * Work.EllipticEst.Core.ttIntS G u
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
  have h : Work.EllipticEst.Core.ttIntS G u
      = (Work.Spaces.w u) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := rfl
  rw [h, inv_mul_cancel_left₀ (pow_ne_zero 2 (ne_of_gt (w_pos hu)))]

/-- The windowed `exp`-pullback of a datum integrable on `Iz = [0,∞)` is integrable: the window
is compact, and `t ↦ F (exp t)` is integrable on every compact interval. -/
private lemma window_comp_integrable (F : ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F Work.Spaces.Iz) (δ z : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => if |Real.log z - t| ≤ δ then F (Real.exp t) else 0) := by
  have hFcd : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn F (Set.Icc a b) :=
    fun a b ha _ => hF.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le ha hx.1))
  have hII : MeasureTheory.IntegrableOn (fun t : ℝ => F (Real.exp t))
      (Set.Icc (Real.log z - δ) (Real.log z + δ)) :=
    integrableOn_exp_comp hFcd (Real.log z - δ) (Real.log z + δ)
  have hfun : (fun t : ℝ => if |Real.log z - t| ≤ δ then F (Real.exp t) else 0)
      = Set.indicator {t : ℝ | |Real.log z - t| ≤ δ} (fun t : ℝ => F (Real.exp t)) := by
    funext t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [if_pos h, Set.indicator_of_mem (show t ∈ {u : ℝ | |Real.log z - u| ≤ δ} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show t ∉ {u : ℝ | |Real.log z - u| ≤ δ} from h)]
  rw [hfun, window_eq_Icc]
  exact hII.integrable_indicator measurableSet_Icc

theorem window_ttIntS_integrable (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ z : ℝ) (hδ : 0 < δ) (hz : 0 < z) :
    MeasureTheory.Integrable (fun t : ℝ =>
        if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) ∧
      MeasureTheory.Integrable (fun t : ℝ =>
        if |Real.log z - t| ≤ δ then
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) else 0) := by
  have hTt : MeasureTheory.IntegrableOn (Work.EllipticEst.Core.ttIntS G) Work.Spaces.Iz := hF.2.2.1
  have hf₁ : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) :=
    window_comp_integrable (Work.EllipticEst.Core.ttIntS G) hTt δ z
  refine ⟨hf₁, ?_⟩
  -- the target function factors as a bounded weight times the already integrable one
  have hpt : ∀ t : ℝ,
      (if |Real.log z - t| ≤ δ then
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) else 0)
        = (if |Real.log z - t| ≤ δ then ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹ else 0)
          * (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) := by
    intro t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [if_pos h, if_pos h, if_pos h, inv_w_sq_mul_ttIntS G (Real.exp t) (Real.exp_pos t)]
    · rw [if_neg h, if_neg h, if_neg h, mul_zero]
  refine MeasureTheory.Integrable.mono' (hf₁.norm.const_mul ((z * Real.exp δ) ^ 4)) ?_ ?_
  · have hmeasA : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => if |Real.log z - t| ≤ δ then ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹ else 0)
        MeasureTheory.volume := by
      have hset : MeasurableSet {t : ℝ | |Real.log z - t| ≤ δ} :=
        measurableSet_le (continuous_abs.comp
          (continuous_const.sub continuous_id : Continuous fun t : ℝ => Real.log z - t)).measurable
          measurable_const
      have hcont : Measurable (fun t : ℝ => ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹) :=
        (continuous_w_exp.pow 2).measurable.inv
      exact (Measurable.ite hset hcont measurable_const).aestronglyMeasurable
    exact MeasureTheory.AEStronglyMeasurable.congr
      (hmeasA.mul hf₁.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => (hpt t).symm)
  · filter_upwards with t
    rw [hpt t, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases h : |Real.log z - t| ≤ δ
    · rw [if_pos h, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
      have ht : Real.exp t ≤ z * Real.exp δ := by
        calc Real.exp t ≤ Real.exp (Real.log z + δ) :=
              Real.exp_le_exp.mpr (by linarith [(abs_le.mp h).1])
          _ = z * Real.exp δ := by rw [Real.exp_add, Real.exp_log hz]
      exact w_sq_inv_le_pow_four (Real.exp t) (z * Real.exp δ) (Real.exp_pos t) ht
    · rw [if_neg h, abs_zero]
      positivity

end Work.FTS.EllSol.EllPkgAux.MollDom
