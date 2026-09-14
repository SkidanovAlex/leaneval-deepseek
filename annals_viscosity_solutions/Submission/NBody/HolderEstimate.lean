import Submission.NBody.ActionTau
import Submission.Commons.Analysis.Real.sqrt_four_mul
import Submission.Commons.Analysis.Real.exists_mul_sqrt_add_le
import Mathlib

/-!
# Reducing the Hölder estimate to Maderna's fixed-time estimate

The paper's `thm-phih.estim` states that there are `α, β > 0` with
`φ_h(x,y) ≤ (α‖x-y‖ + hβ‖x-y‖²)^{1/2}`.  The paper deduces it from Maderna's estimate for the
*fixed-time* action potential `φ(x,y,τ)`:

  for all `r > ‖x-y‖` and all `τ > 0`,  `φ(x,y,τ) ≤ α₁ r²/τ + β₁ τ/r`.

Here we formalise that reduction: given the fixed-time bound, the minimisation over `τ` of
`α₁ r²/τ + β₁ τ/r + hτ` (whose value is `2√(α₁ r²(β₁/r + h))`) gives the Hölder estimate with
`α = 4 α₁ β₁` and `β = 4 α₁`.  This isolates the single deep input (Maderna's estimate) from the
elementary part of the argument.

Everything here is fully proved (the fixed-time estimate enters as an explicit hypothesis).
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- `A/τ + Bτ` attains its minimum `2√(A B)` at `τ = √A/√B`. -/
private lemma exists_div_add_mul_le_sqrt' {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ τ : ℝ, 0 < τ ∧ A / τ + B * τ ≤ 2 * Real.sqrt (A * B) := by
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  refine ⟨Real.sqrt A / Real.sqrt B, div_pos hsA hsB, ?_⟩
  have h1 : A / (Real.sqrt A / Real.sqrt B) = Real.sqrt A * Real.sqrt B := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hA.le]
  have h2 : B * (Real.sqrt A / Real.sqrt B) = Real.sqrt A * Real.sqrt B := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hB.le]
  rw [h1, h2, Real.sqrt_mul hA.le]
  linarith

/-- **`thm-phih.estim` from Maderna's fixed-time estimate.** -/
theorem actionPot_le_holder_of_actionPotTau_bound {m : Fin N → ℝ} {h : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h) {α₁ β₁ : ℝ} (hα₁ : 0 < α₁) (hβ₁ : 0 < β₁)
    (hbound : ∀ x y : EN E N, ∀ r : ℝ, ‖x - y‖ < r → ∀ τ : ℝ, 0 < τ →
      actionPotTau m x y τ ≤ ENNReal.ofReal (α₁ * r ^ 2 / τ + β₁ * τ / r))
    (x y : EN E N) :
    actionPot m h x y ≤ ENNReal.ofReal (Real.sqrt (4 * α₁ * β₁ * ‖x - y‖
      + 4 * α₁ * h * ‖x - y‖ ^ 2)) := by
  -- `φ_h(x,y) ≤ α₁ r²/τ + β₁ τ/r + hτ` for every `r > ‖x-y‖` and `τ > 0`
  have hA : ∀ (p q : EN E N) (τ : ℝ), 0 < τ → ∀ r : ℝ, ‖p - q‖ < r →
      actionPot m h p q ≤ ENNReal.ofReal (α₁ * r ^ 2 / τ + β₁ * τ / r + h * τ) := by
    intro p q τ hτ r hr
    have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr
    have hnn : 0 ≤ α₁ * r ^ 2 / τ + β₁ * τ / r := by positivity
    have hhτ : 0 ≤ h * τ := mul_nonneg hh hτ.le
    have hle : actionPot m h p q
        ≤ actionPotTau m p q τ + ENNReal.ofReal h * ENNReal.ofReal τ := by
      rw [actionPot_eq_iInf_actionPotTau hm hh]
      exact iInf_le (f := fun σ : {σ : ℝ // 0 < σ} =>
        actionPotTau m p q σ.1 + ENNReal.ofReal h * ENNReal.ofReal σ.1) ⟨τ, hτ⟩
    refine hle.trans ?_
    have h2 : ENNReal.ofReal (α₁ * r ^ 2 / τ + β₁ * τ / r)
        + ENNReal.ofReal h * ENNReal.ofReal τ
        = ENNReal.ofReal (α₁ * r ^ 2 / τ + β₁ * τ / r + h * τ) := by
      rw [← ENNReal.ofReal_mul hh, ENNReal.ofReal_add hnn hhτ]
    calc actionPotTau m p q τ + ENNReal.ofReal h * ENNReal.ofReal τ
        ≤ ENNReal.ofReal (α₁ * r ^ 2 / τ + β₁ * τ / r) + ENNReal.ofReal h * ENNReal.ofReal τ :=
          add_le_add (hbound p q r hr τ hτ) le_rfl
      _ = ENNReal.ofReal (α₁ * r ^ 2 / τ + β₁ * τ / r + h * τ) := h2
  by_cases hxy : x = y
  · -- `x = y`: take `r = τ/2`-style; here `τ = r√r` and let `r → 0`
    subst hxy
    have htarget : Real.sqrt (4 * α₁ * β₁ * ‖x - x‖ + 4 * α₁ * h * ‖x - x‖ ^ 2) = 0 := by simp
    rw [htarget, ENNReal.ofReal_zero]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨r, hr, hrle⟩ := Commons.Analysis.Real.exists_mul_sqrt_add_le
      (a := α₁ + β₁) (b := h) (add_nonneg hα₁.le hβ₁.le) hh
      (show (0 : ℝ) < (ε : ℝ) from hε)
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hrr : 0 < r * Real.sqrt r := mul_pos hr hs
    have hb := hA x x (r * Real.sqrt r) hrr r (by rw [sub_self, norm_zero]; exact hr)
    have hval : α₁ * r ^ 2 / (r * Real.sqrt r) + β₁ * (r * Real.sqrt r) / r
        + h * (r * Real.sqrt r) = (α₁ + β₁) * Real.sqrt r + h * (r * Real.sqrt r) := by
      have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
      field_simp
      rw [hsq]
      ring
    rw [hval] at hb
    refine hb.trans ?_
    rw [zero_add]
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hrle
  · -- `x ≠ y`
    have hρ : 0 < ‖x - y‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hxy
    -- take `r ↓ ‖x-y‖`
    have hstep : ∀ τ : ℝ, 0 < τ →
        actionPot m h x y
          ≤ ENNReal.ofReal (α₁ * ‖x - y‖ ^ 2 / τ + β₁ * τ / ‖x - y‖ + h * τ) := by
      intro τ hτ
      have hcont : ContinuousAt (fun r : ℝ => ENNReal.ofReal
          (α₁ * r ^ 2 / τ + β₁ * τ / r + h * τ)) ‖x - y‖ := by
        refine ENNReal.continuous_ofReal.continuousAt.comp ?_
        refine ContinuousAt.add (ContinuousAt.add ?_ ?_) continuousAt_const
        · exact ((continuous_const.mul (continuous_id.pow 2)).continuousAt).div_const τ
        · exact (continuousAt_const.mul continuousAt_const).div continuousAt_id (ne_of_gt hρ)
      have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal
          (α₁ * r ^ 2 / τ + β₁ * τ / r + h * τ)) (𝓝[>] ‖x - y‖) (𝓝 (ENNReal.ofReal
            (α₁ * ‖x - y‖ ^ 2 / τ + β₁ * τ / ‖x - y‖ + h * τ))) :=
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hA x y τ hτ r hr
    -- minimise over `τ`
    have hApos : 0 < α₁ * ‖x - y‖ ^ 2 := mul_pos hα₁ (pow_pos hρ 2)
    have hBpos : 0 < β₁ / ‖x - y‖ + h := by
      have : 0 < β₁ / ‖x - y‖ := div_pos hβ₁ hρ
      linarith
    obtain ⟨τ, hτ, hτle⟩ := exists_div_add_mul_le_sqrt' hApos hBpos
    have hb := hstep τ hτ
    have hrewrite : α₁ * ‖x - y‖ ^ 2 / τ + β₁ * τ / ‖x - y‖ + h * τ
        = α₁ * ‖x - y‖ ^ 2 / τ + (β₁ / ‖x - y‖ + h) * τ := by ring
    have hAB : α₁ * ‖x - y‖ ^ 2 * (β₁ / ‖x - y‖ + h)
        = α₁ * β₁ * ‖x - y‖ + α₁ * h * ‖x - y‖ ^ 2 := by
      field_simp
      try ring
    have hsqrt : 2 * Real.sqrt (α₁ * β₁ * ‖x - y‖ + α₁ * h * ‖x - y‖ ^ 2)
        = Real.sqrt (4 * α₁ * β₁ * ‖x - y‖ + 4 * α₁ * h * ‖x - y‖ ^ 2) := by
      rw [show (4 * α₁ * β₁ * ‖x - y‖ + 4 * α₁ * h * ‖x - y‖ ^ 2)
          = 4 * (α₁ * β₁ * ‖x - y‖ + α₁ * h * ‖x - y‖ ^ 2) from by ring,
        Commons.Analysis.Real.sqrt_four_mul (by positivity)]
      try ring
    rw [hAB, hsqrt] at hτle
    refine hb.trans ?_
    rw [hrewrite]
    exact ENNReal.ofReal_le_ofReal hτle

end Submission.NBody
