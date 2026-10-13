import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts` — elementary facts about the weight `wfun`

The quotient `wfun θ / sin 2θ = sin θ cos²θ / 2` is *unconditional* (Lean's `x / 0 = 0`
convention agrees with the trigonometric value at the zeros of `sin 2θ`), whence `gwt A C` is
continuous on all of `ℝ`.  We also record the abbreviations `u1fun`, `Gfun` used throughout the
ODE bound.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `wfun θ / sin 2θ = sin θ cos²θ / 2`, with no side condition (both sides vanish where
`sin 2θ` does, and Lean's `x / 0 = 0` convention makes this an equality everywhere). -/
lemma wfun_div_s2_eq (θ : ℝ) : wfun θ / Real.sin (2 * θ) = Real.sin θ * Real.cos θ ^ 2 / 2 := by
  rw [wfun, Real.sin_two_mul]
  rcases eq_or_ne (Real.sin θ) 0 with hs | hs
  · simp [hs]
  rcases eq_or_ne (Real.cos θ) 0 with hc | hc
  · simp [hc]
  · field_simp

/-- `gwt A C` is continuous: it equals `A · sin θ cos²θ / 2 + C · sin²θ cos³θ`. -/
lemma continuous_gwt (A C : ℝ) : Continuous (gwt A C) := by
  have h : gwt A C = fun t : ℝ =>
      A * (Real.sin t * Real.cos t ^ 2 / 2)
        + C * (Real.sin t ^ 2 * Real.cos t ^ 3) := by
    funext t
    rw [gwt_def, wfun_div_s2_eq t, wfun]
  rw [h]
  fun_prop

/-- `gwt A C ≥ 0` on `(0, π/2)`. -/
lemma gwt_nonneg {A C θ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ gwt A C θ := by
  have hs : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hc : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  rw [gwt_def, wfun_div_s2_eq]
  have h1 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 / 2 := by
    have := sq_nonneg (Real.cos θ); positivity
  have h2 : 0 ≤ wfun θ := by
    rw [wfun]
    have hc2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
    have hc3 : 0 ≤ Real.cos θ ^ 3 := by
      rw [show Real.cos θ ^ 3 = Real.cos θ * Real.cos θ ^ 2 by ring]
      exact mul_nonneg hc hc2
    exact mul_nonneg (sq_nonneg _) hc3
  exact add_nonneg (mul_nonneg hA h1) (mul_nonneg hC h2)

/-- `gwt A C ≥ 0` on `[0, π/2]`. -/
lemma gwt_nonneg_Icc {A C θ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ gwt A C θ := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2]⟩
  rw [gwt_def, wfun_div_s2_eq]
  have h1 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 / 2 := by
    have := sq_nonneg (Real.cos θ); positivity
  have h2 : 0 ≤ wfun θ := by
    rw [wfun]
    have hc2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
    have hc3 : 0 ≤ Real.cos θ ^ 3 := by
      rw [show Real.cos θ ^ 3 = Real.cos θ * Real.cos θ ^ 2 by ring]
      exact mul_nonneg hc hc2
    exact mul_nonneg (sq_nonneg _) hc3
  exact add_nonneg (mul_nonneg hA h1) (mul_nonneg hC h2)

/-- The `θ`-slice derivative `u'(θ) = ∂_θ u z θ`, as a function of `θ`. -/
def u1fun (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ := fun θ => deriv (fun θ' => u z θ') θ

/-- `G = wfun · u'`, the quantity whose derivative is `wfun · H`. -/
def Gfun (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ := fun θ => wfun θ * u1fun u z θ

@[simp] lemma u1fun_apply (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    u1fun u z θ = deriv (fun θ' => u z θ') θ := rfl

@[simp] lemma Gfun_apply (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Gfun u z θ = wfun θ * deriv (fun θ' => u z θ') θ := rfl

end Work.FTS_StreamBdry.SB6.UprimeAux
