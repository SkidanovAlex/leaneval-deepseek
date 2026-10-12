import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.LGW.deriv_smoothTransition
import Submission.Work.BoseFixR.LGW.exp_ratio_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LGW

open Filter
open scoped Topology

/-- The derivative vanishes left of `0`. -/
lemma deriv_smoothTransition_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0:ℝ)) := by
    filter_upwards [Iic_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy
  rw [h.deriv_eq]
  simp

/-- The derivative vanishes right of `1`. -/
lemma deriv_smoothTransition_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1:ℝ)) := by
    filter_upwards [Ici_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy
  rw [h.deriv_eq]
  simp

/-- `deriv Real.smoothTransition` is continuous, since `smoothTransition` is `C^∞`. -/
lemma continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) := by
  have h := ContDiff.continuous_iteratedDeriv' 1 (Real.smoothTransition.contDiff (n := (1:ℕ∞)))
  rwa [iteratedDeriv_one] at h

/-- The derivative vanishes at the left junction point `0`: it vanishes on `(-∞,0)` and
`deriv smoothTransition` is continuous. -/
lemma deriv_smoothTransition_zero : deriv Real.smoothTransition 0 = 0 := by
  have hcont : ContinuousAt (deriv Real.smoothTransition) (0:ℝ) :=
    continuous_deriv_smoothTransition.continuousAt
  have h1 : Tendsto (deriv Real.smoothTransition) (𝓝[<] (0:ℝ)) (𝓝 (0:ℝ)) :=
    Tendsto.congr' (f₁ := (fun _ => (0:ℝ))) (f₂ := deriv Real.smoothTransition) (by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (deriv_smoothTransition_of_neg hy).symm) tendsto_const_nhds
  have h2 : Tendsto (deriv Real.smoothTransition) (𝓝[<] (0:ℝ))
      (𝓝 (deriv Real.smoothTransition 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h2 h1

/-- The derivative vanishes at the right junction point `1`. -/
lemma deriv_smoothTransition_one : deriv Real.smoothTransition 1 = 0 := by
  have hcont : ContinuousAt (deriv Real.smoothTransition) (1:ℝ) :=
    continuous_deriv_smoothTransition.continuousAt
  have h1 : Tendsto (deriv Real.smoothTransition) (𝓝[>] (1:ℝ)) (𝓝 (0:ℝ)) :=
    Tendsto.congr' (f₁ := (fun _ => (0:ℝ))) (f₂ := deriv Real.smoothTransition) (by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (deriv_smoothTransition_of_one_lt hy).symm) tendsto_const_nhds
  have h2 : Tendsto (deriv Real.smoothTransition) (𝓝[>] (1:ℝ))
      (𝓝 (deriv Real.smoothTransition 1)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h2 h1

/-- On `(0,1)` the derivative is at most `45/16` in absolute value.  The chain is
`e^t/(1+e^t)^2 · (1/x^2+1/(1-x)^2) ≤ (1/(4+t^2)) · (c/u^2) = 1/c ≤ 2 ≤ 45/16`. -/
lemma abs_deriv_smoothTransition_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    |deriv Real.smoothTransition x| ≤ 45/16 := by
  set t : ℝ := 1/x - 1/(1-x) with ht
  have hxn : x ≠ 0 := ne_of_gt hx0
  have hm : (1 - x) ≠ 0 := by linarith
  have hidA : 1/x^2 + 1/(1-x)^2 = (2*x^2-2*x+1)/(x^2*(1-x)^2) := by
    field_simp; ring
  have hidC : 4 + t^2 = (2*x^2-2*x+1)^2/(x^2*(1-x)^2) := by
    rw [ht]; field_simp; ring
  have hcpos : 0 < 2*x^2-2*x+1 := by nlinarith [sq_nonneg (x - 1/2)]
  have hmid : 0 ≤ (2*x^2-2*x+1)/(x^2*(1-x)^2) := by positivity
  have hnn : 0 ≤ Real.exp t / (1 + Real.exp t)^2 * (1/x^2 + 1/(1-x)^2) := by positivity
  rw [deriv_smoothTransition hx0 hx1, abs_of_nonneg hnn]
  calc Real.exp t / (1 + Real.exp t)^2 * (1/x^2 + 1/(1-x)^2)
      = Real.exp t / (1 + Real.exp t)^2 * ((2*x^2-2*x+1)/(x^2*(1-x)^2)) := by rw [hidA]
    _ ≤ 1/(4 + t^2) * ((2*x^2-2*x+1)/(x^2*(1-x)^2)) :=
        mul_le_mul_of_nonneg_right (exp_ratio_le t) hmid
    _ = 1/(2*x^2-2*x+1) := by rw [hidC]; field_simp
    _ ≤ 2 := by
        rw [div_le_iff₀ hcpos]
        nlinarith [sq_nonneg (x - 1/2)]
    _ ≤ 45/16 := by norm_num

theorem STDerivBound : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ 45 / 16 := by
  intro x
  rcases lt_trichotomy x 0 with h | h | h
  · rw [deriv_smoothTransition_of_neg h]; norm_num
  · rw [h, deriv_smoothTransition_zero]; norm_num
  · rcases lt_trichotomy x 1 with h1 | h1 | h1
    · exact abs_deriv_smoothTransition_le h h1
    · rw [h1, deriv_smoothTransition_one]; norm_num
    · rw [deriv_smoothTransition_of_one_lt h1]; norm_num

end Work.BoseFixR.LGW
