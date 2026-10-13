/-
# `Work.StabilityFar.Decay.timeDeriv_timeHolder` — the far-field time-Hölder bound for `∂ₜu`

This is the *second block* of the joint `C^{1,α}` far-field estimate of `St4`: the sibling file
`Work.StabilityFar.Decay.fderiv_timeHolder` handles the spatial block `Dₓu`, and this file
handles the time block

  `‖∂ₜu(x,t) - ∂ₜu(x,τ)‖ ≤ Atu · |t - τ|^α`   for `2R < ‖x‖`, `t, τ ∈ window T`.

## The mathematics

By hypothesis `u` is the Biot–Savart field of `ω` slice by slice and the Biot–Savart
reconstruction commutes with `∂ₜ` (`IsTimeBiotSavartSlice`), so

  `∂ₜu(x,t) = BS(∂ₜω(·,t))(x)`.

Biot–Savart is *linear* (`Work.StabilityFar.Decay.biotSavart_sub`, which only needs the two
integrands `bsK (∂ₜω(·,t)) x` and `bsK (∂ₜω(·,τ)) x` to be Bochner-integrable — supplied by the
support, the bound `M₁` and the measurability of the slices of `∂ₜω`), hence

  `∂ₜu(x,t) - ∂ₜu(x,τ) = BS(∂ₜω(·,t) - ∂ₜω(·,τ))(x)`.

The difference field `g = ∂ₜω(·,t) - ∂ₜω(·,τ)` is supported in `B(0,R)` (both summands are:
**the support of `∂ₜω` is the same ball as that of `ω`**, which is
`Work.StabilityFar.Decay.slicesSupported_timeDeriv_window`, imported here) and bounded by
`H₁ |t - τ|^α` (on the ball by `TimeHolderOnBall`, off it because both slices vanish there).
The explicit far-field decay of the Biot–Savart field of a bounded, supported vorticity
(`Work.LWP.BiotSavart.farField_decay_const`),

  `‖BS g x‖ ≤ (4/3) · ‖g‖_∞ · R³ / ‖x‖²`   for `2R ≤ ‖x‖`,

together with `R³/‖x‖² ≤ R/4` (from `2R < ‖x‖`) yields the constant `Atu = H₁·R/3`:

  `‖∂ₜu(x,t) - ∂ₜu(x,τ)‖ ≤ (4/3) · H₁|t-τ|^α · R/4 = (H₁R/3)·|t-τ|^α`.

## An endpoint subtlety

`∂ₜω = deriv (ω y)` is a *two-sided* derivative, while `SlicesSupported ω R T` constrains the
slices only on the closed window `[-1, T+1]`.  The support of `∂ₜω` therefore needs a one-sided
argument at the endpoints of the window, and at the *right* endpoint `t = T+1` one needs a left
neighbourhood `(T+1-ε, T+1] ⊆ window T`, i.e. `T > -2`.  This is why this file carries no
hypothesis `0 ≤ T`: the conclusion is stated for the closed window `window T`, and it is proved
here for every `T` (for `T ≤ -2` the window is empty or the single point `{-1}` and the claim is
trivial).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Basic
import Submission.Work.StabilityFar.Decay.biotSavart_sub
import Submission.Work.StabilityFar.Decay.slicesSupported_timeDeriv_window
import Submission.Work.LWP.FarField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open MeasureTheory

set_option linter.unusedVariables false

/-! ## The far-field bound on the difference of two time slices of `BS(∂ₜω)` -/

/-- **The far-field `α`-Hölder bound for `BS(∂ₜω)`.**  Let the slices of `∂ₜω` be supported in
`B(0,R)` and let them be `α`-Hölder in time with constant `H₁` on that ball.  Then for
`2R < ‖x‖` and `t, τ` in the window the Biot–Savart fields of the two slices differ by at most
`(H₁R/3)|t-τ|^α`:

`‖BS(∂ₜω(·,t)) x - BS(∂ₜω(·,τ)) x‖ = ‖BS(∂ₜω(·,t) - ∂ₜω(·,τ)) x‖ ≤ (H₁R/3)|t-τ|^α`.

The difference field is supported in `B(0,R)` and bounded by `H₁|t-τ|^α`, so the explicit
`‖x‖⁻²` far-field decay of the Biot–Savart field applies, and `R³/‖x‖² ≤ R/4`. -/
theorem biotSavart_timeDeriv_sub_le {α : NNReal} {ω : R3 → ℝ → R3} {R H₁ T : ℝ}
    (hR : 0 < R) (hH₁ : 0 ≤ H₁)
    (hsuppD : SlicesSupported (FiniteTimeSingularity.timeDeriv ω) R T)
    (hthDt : TimeHolderOnBall (α : ℝ) (FiniteTimeSingularity.timeDeriv ω) R T H₁)
    {x : R3} (hx : 2 * R < ‖x‖) {t τ : ℝ} (ht : t ∈ window T) (hτ : τ ∈ window T) :
    ‖Work.LWP.biotSavart ((fun y => FiniteTimeSingularity.timeDeriv ω y t)
        - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) x‖
      ≤ (H₁ * R / 3) * |t - τ| ^ (α : ℝ) := by
  have hs : 0 ≤ |t - τ| ^ (α : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
  -- off the support ball both slices of `∂ₜω` vanish
  have hzero : ∀ s ∈ window T, ∀ y : R3,
      y ∉ Metric.closedBall 0 R → FiniteTimeSingularity.timeDeriv ω y s = 0 := by
    intro s hss y hy
    by_contra hne
    exact hy (hsuppD s hss y hne)
  -- the difference field is bounded by `H₁ |t-τ|^α` ...
  have hbddF : ∀ y : R3,
      ‖((fun y => FiniteTimeSingularity.timeDeriv ω y t)
        - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) y‖
        ≤ H₁ * |t - τ| ^ (α : ℝ) := by
    intro y
    rw [Pi.sub_apply]
    by_cases hy : y ∈ Metric.closedBall 0 R
    · exact hthDt y hy t ht τ hτ
    · rw [hzero t ht y hy, hzero τ hτ y hy, sub_zero, norm_zero]
      exact mul_nonneg hH₁ hs
  -- ... and supported in the ball
  have hsuppF : ∀ y : R3,
      ((fun y => FiniteTimeSingularity.timeDeriv ω y t)
        - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) y ≠ 0 →
      y ∈ Metric.closedBall 0 R := by
    intro y hy
    by_contra hcon
    exact hy (by rw [Pi.sub_apply, hzero t ht y hcon, hzero τ hτ y hcon, sub_zero])
  have hfar := Work.LWP.BiotSavart.farField_decay_const
    (ω := (fun y => FiniteTimeSingularity.timeDeriv ω y t)
      - (fun y => FiniteTimeSingularity.timeDeriv ω y τ))
    (R := R) (M := H₁ * |t - τ| ^ (α : ℝ)) hR.le (mul_nonneg hH₁ hs) hbddF hsuppF x
    (le_of_lt hx)
  -- `R³/‖x‖² ≤ R/4`
  have hkey : R ^ 3 / ‖x‖ ^ 2 ≤ R / 4 := by
    have hXpos : 0 < ‖x‖ ^ 2 := pow_pos (by linarith) 2
    rw [div_le_iff₀ hXpos]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have h2 : (2 * R) ^ 2 ≤ ‖x‖ ^ 2 := by
      have h1 : 0 ≤ 2 * R := by linarith
      simpa using pow_le_pow_left₀ h1 hx.le 2
    nlinarith [h2]
  refine hfar.trans ?_
  have hstep : (4 / 3) * (H₁ * |t - τ| ^ (α : ℝ)) * R ^ 3 / ‖x‖ ^ 2
      = (4 / 3) * (H₁ * |t - τ| ^ (α : ℝ)) * (R ^ 3 / ‖x‖ ^ 2) := by ring
  rw [hstep]
  calc (4 / 3) * (H₁ * |t - τ| ^ (α : ℝ)) * (R ^ 3 / ‖x‖ ^ 2)
      ≤ (4 / 3) * (H₁ * |t - τ| ^ (α : ℝ)) * (R / 4) :=
        mul_le_mul_of_nonneg_left hkey (by nlinarith [hH₁, hs])
    _ = (H₁ * R / 3) * |t - τ| ^ (α : ℝ) := by ring

/-! ## The target: the far-field time-Hölder bound for `∂ₜu` -/

theorem timeDeriv_timeHolder {α : NNReal}
    {ω u : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {R M₁ H₁ T : ℝ} (hR : 0 < R) (hM₁ : 0 ≤ M₁) (hH₁ : 0 ≤ H₁) (hα : 0 < (α : ℝ))
    (hbsDt : Work.StabilityFar.IsTimeBiotSavartSlice u ω T)
    (hbddDt : Work.StabilityFar.SlicesBounded (FiniteTimeSingularity.timeDeriv ω) M₁ T)
    (hsupp : Work.StabilityFar.SlicesSupported ω R T)
    (hmeasDt : Work.StabilityFar.SlicesMeasurable (FiniteTimeSingularity.timeDeriv ω) T)
    (hthDt : Work.StabilityFar.TimeHolderOnBall (α : ℝ) (FiniteTimeSingularity.timeDeriv ω) R T H₁) :
    ∃ Atu : ℝ, 0 ≤ Atu ∧ ∀ x : Work.StabilityFar.R3, 2 * R < ‖x‖ →
      ∀ t ∈ Work.StabilityFar.window T, ∀ τ ∈ Work.StabilityFar.window T,
      ‖FiniteTimeSingularity.timeDeriv u x t - FiniteTimeSingularity.timeDeriv u x τ‖
        ≤ Atu * |t - τ| ^ (α : ℝ) := by
  have hAtu : 0 ≤ H₁ * R / 3 := div_nonneg (mul_nonneg hH₁ hR.le) (by norm_num)
  by_cases hT : -2 < T
  · -- the window is non-degenerate: `∂ₜω` is supported in the ball
    have hsuppD : SlicesSupported (FiniteTimeSingularity.timeDeriv ω) R T := slicesSupported_timeDeriv_window hT hsupp
    refine ⟨H₁ * R / 3, hAtu, ?_⟩
    intro x hx t ht τ hτ
    by_cases htτ : t = τ
    · -- the diagonal: the left side is `0`
      subst htτ
      simp only [sub_self, norm_zero]
      exact mul_nonneg hAtu (Real.rpow_nonneg (abs_nonneg _) _)
    · -- linearity of Biot–Savart turns the difference of the two fields into a single integral
      have hDiff : FiniteTimeSingularity.timeDeriv u x t - FiniteTimeSingularity.timeDeriv u x τ
          = Work.LWP.biotSavart ((fun y => FiniteTimeSingularity.timeDeriv ω y t) - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) x := by
        rw [hbsDt t ht x, hbsDt τ hτ x]
        exact (biotSavart_sub (f := fun y => FiniteTimeSingularity.timeDeriv ω y t) (g := fun y => FiniteTimeSingularity.timeDeriv ω y τ)
          hR.le hM₁ (hbddDt t ht) (hbddDt τ hτ) (hsuppD t ht) (hsuppD τ hτ)
          (hmeasDt t ht) (hmeasDt τ hτ) x).symm
      rw [hDiff]
      exact biotSavart_timeDeriv_sub_le hR hH₁ hsuppD hthDt hx ht hτ
  · -- `T ≤ -2`: the window is empty or the single point `-1`, and the claim is trivial
    rw [not_lt] at hT
    refine ⟨0, le_refl 0, ?_⟩
    intro x hx t ht τ hτ
    have ht1 : t = -1 := le_antisymm (by linarith [ht.2, hT]) ht.1
    have hτ1 : τ = -1 := le_antisymm (by linarith [hτ.2, hT]) hτ.1
    rw [ht1, hτ1]
    simp only [sub_self, norm_zero, abs_zero, zero_mul]
    exact le_refl 0

end Work.StabilityFar.Decay
