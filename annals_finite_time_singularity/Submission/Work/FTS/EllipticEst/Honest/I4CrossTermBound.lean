import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs
import Submission.Work.FTS.EllipticEst.Honest.I4CrossCont
import Submission.Work.FTS.EllipticEst.Honest.I4SubInterval

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The cross term of the honest `I₄` slice estimate, integrated.**

With `ψ = I4psi Φ = Φ/cos θ`, `σ = I4sig` and `Σ = I4Sig`, the pointwise AM–GM bound `hpt`
(read with `q = ψ'` and `Ψv = Φ`) says
`|sin θ · σ · ψ' · Φ| ≤ ½ Σ σ (ψ')² + 50 σ (Φ/cos θ)²`
on `(0, π/2)`.  Integrating it over the sub-interval `[δ, θ₁] ⊂ (0, π/2)` gives the crossed-out
term of `I4SliceBound`; the second term is upgraded from `∫_δ^{θ₁}` to `∫_{Iθ}` because `I4sig`
is nonnegative on `Iθ = [0, π/2]` and `I4psi Φ ^ 2 * I4sig` is integrable there (`hA`). -/
theorem I4CrossTermBound (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ)
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ q Ψv : ℝ,
        |Real.sin θ * I4sig θ * q * Ψv|
          ≤ (1 / 2) * I4Sig θ * I4sig θ * q ^ 2
            + 50 * I4sig θ * (Ψv / Real.cos θ) ^ 2)
    {δ θ₁ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ < Real.pi / 2) :
    |∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|
      ≤ (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
        + 50 * (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ) := by
  obtain ⟨hΦc, hψc, hqc, hσc, hSc⟩ := I4CrossCont Φ hsm hδ hδθ hθ₁
  -- continuity of the three integrands on `[δ, θ₁]`
  have hfc : ContinuousOn (fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
      (Set.Icc δ θ₁) :=
    ((Real.continuous_sin.continuousOn.mul hσc).mul hqc).mul hΦc
  have hg1c : ContinuousOn (fun θ => I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
      (Set.Icc δ θ₁) := (hSc.mul hσc).mul (hqc.pow 2)
  have hg2c : ContinuousOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) (Set.Icc δ θ₁) :=
    (hψc.pow 2).mul hσc
  have hfI : IntervalIntegrable (fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
      volume δ θ₁ := hfc.intervalIntegrable_of_Icc hδθ
  have hg1I : IntervalIntegrable (fun θ => I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
      volume δ θ₁ := hg1c.intervalIntegrable_of_Icc hδθ
  have hg2I : IntervalIntegrable (fun θ => I4psi Φ θ ^ 2 * I4sig θ) volume δ θ₁ :=
    hg2c.intervalIntegrable_of_Icc hδθ
  have hgI : IntervalIntegrable
      (fun θ => (1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
        + 50 * (I4psi Φ θ ^ 2 * I4sig θ)) volume δ θ₁ :=
    (hg1I.const_mul (1 / 2)).add (hg2I.const_mul 50)
  -- the pointwise AM–GM bound, on the open interval `(δ, θ₁)`
  have hpt' : ∀ θ ∈ Set.Ioo δ θ₁,
      |Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|
        ≤ (1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (I4psi Φ θ ^ 2 * I4sig θ) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_lt_of_le hδ (le_of_lt hθ.1), lt_of_le_of_lt (le_of_lt hθ.2) hθ₁⟩
    have h := hpt θ hθ' (deriv (I4psi Φ) θ) (Φ θ)
    calc |Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|
        ≤ (1 / 2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2
          + 50 * I4sig θ * (Φ θ / Real.cos θ) ^ 2 := h
      _ = (1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (I4psi Φ θ ^ 2 * I4sig θ) := by rw [I4psi]; ring
  -- the `∫_θ`-integral over the sub-interval is at most the one over all of `Iθ`
  have hsub : (∫ θ in δ..θ₁, I4psi Φ θ ^ 2 * I4sig θ)
      ≤ (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ) :=
    I4SubInterval (fun θ => I4psi Φ θ ^ 2 * I4sig θ) hA
      (fun θ hθ => mul_nonneg (sq_nonneg _) (I4sig_nonneg hθ)) (le_of_lt hδ) hδθ (le_of_lt hθ₁)
  calc |∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|
      ≤ ∫ θ in δ..θ₁, |Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ| :=
        intervalIntegral.abs_integral_le_integral_abs
          (f := fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ) hδθ
    _ ≤ ∫ θ in δ..θ₁, ((1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (I4psi Φ θ ^ 2 * I4sig θ)) :=
        intervalIntegral.integral_mono_on_of_le_Ioo
          (f := fun θ => |Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|)
          (g := fun θ => (1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
            + 50 * (I4psi Φ θ ^ 2 * I4sig θ))
          hδθ hfI.abs hgI (fun θ hθ => hpt' θ hθ)
    _ = (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (∫ θ in δ..θ₁, I4psi Φ θ ^ 2 * I4sig θ) := by
        rw [intervalIntegral.integral_add (hg1I.const_mul (1 / 2)) (hg2I.const_mul 50),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsub (by norm_num))

end Work.FTS.EllipticEst.Honest
