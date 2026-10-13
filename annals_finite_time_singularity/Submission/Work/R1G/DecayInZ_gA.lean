/-
# `Work.R1G.DecayInZ_gA`

The radial decay of the explicit analytic perturbation `gA z θ = Zf z · Tf θ`
(`Zf z = z²/(1+z²)⁴`, `Tf θ = sin 2θ`): the plain partial derivatives `∂_z^j ∂_θ^i gA`
with `i + j ≤ 2` tend to `0` as `z → +∞`, for every fixed angle `θ ∈ [0,π/2]`.

Since `gA` is a product of a radial and an angular factor, every mixed plain derivative
splits (`pzIter_pthIter_gA`):

  `∂_z^j ∂_θ^i gA (z,θ) = (∂^j Zf)(z) · (∂^i Tf)(θ)`,

and `∂^i Tf θ` is a constant in `z`.  So it remains to see that the radial factor and its
first two derivatives vanish at `+∞`.  Each of these is an explicit rational function

* `Zf z = z²/(1+z²)⁴`,
* `Zf' z = (2z - 6z³)/(1+z²)⁵`,
* `Zf'' z = (2 - 36z² + 42z⁴)/(1+z²)⁶`,

whose numerator has degree `< 2·(degree of the denominator)`: the elementary
monomial estimate `tendsto_mono_div` squeezes each of them against `z^{-(2N-k)} → 0`.

Everything is proved from `Work.R1G.AnG`; no new axioms are used.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.R1G.AnG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Topology

namespace Work.R1G

/-! ## A monomial decay estimate -/

/-- The monomial `z ↦ c·z^k/(1+z²)^N` tends to `0` at `+∞` whenever `k < 2N`: for `z ≥ 1`
the denominator dominates, `(1+z²)^N ≥ z^{2N}`, and `z^k/z^{2N} = z^{-(2N-k)} → 0`. -/
theorem tendsto_mono_div (c : ℝ) (k N : ℕ) (h : k < 2 * N) :
    Tendsto (fun z : ℝ => c * z ^ k / (1 + z ^ 2) ^ N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have hg : Tendsto (fun z : ℝ => |c| * (z ^ k / z ^ (2 * N))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun z : ℝ => z ^ k / z ^ (2 * N)) atTop (𝓝 0) :=
      tendsto_pow_div_pow_atTop_zero h
    simpa using h0.const_mul |c|
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz1
    have hz : 0 ≤ z := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz1
    have hz : 0 ≤ z := by linarith
    have hden : z ^ (2 * N) ≤ (1 + z ^ 2) ^ N := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg z]) N
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ k),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z ^ 2) ^ N), mul_div_assoc']
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-! ## Decay of the radial factor and its first two derivatives -/

/-- The radial factor `Zf` tends to `0` at `+∞` (like `z^{-6}`). -/
theorem tendsto_Zf : Tendsto Zf atTop (𝓝 0) := by
  change Tendsto (fun z : ℝ => z ^ 2 / (1 + z ^ 2) ^ 4) atTop (𝓝 0)
  simpa using tendsto_mono_div 1 2 4 (by norm_num)

/-- The derivative of `Zf` tends to `0` at `+∞` (like `z^{-7}`). -/
theorem tendsto_deriv_Zf : Tendsto (deriv Zf) atTop (𝓝 0) := by
  have h : deriv Zf = fun z : ℝ => (2 * z - 6 * z ^ 3) / (1 + z ^ 2) ^ 5 := by
    funext z; rw [deriv_Zf]
  have heq : (fun z : ℝ => (2 * z - 6 * z ^ 3) / (1 + z ^ 2) ^ 5) =
      fun z : ℝ => 2 * z ^ 1 / (1 + z ^ 2) ^ 5 + (-6) * z ^ 3 / (1 + z ^ 2) ^ 5 := by
    funext z; ring
  rw [h, heq]
  have h1 : Tendsto (fun z : ℝ => 2 * z ^ 1 / (1 + z ^ 2) ^ 5) atTop (𝓝 0) :=
    tendsto_mono_div 2 1 5 (by norm_num)
  have h2 : Tendsto (fun z : ℝ => (-6) * z ^ 3 / (1 + z ^ 2) ^ 5) atTop (𝓝 0) :=
    tendsto_mono_div (-6) 3 5 (by norm_num)
  simpa using h1.add h2

/-- The closed form of the second derivative of the radial factor,
`Zf'' z = (2 - 36z² + 42z⁴)/(1+z²)⁶`. -/
theorem deriv_deriv_Zf (z : ℝ) :
    deriv (deriv Zf) z = (2 - 36 * z ^ 2 + 42 * z ^ 4) / (1 + z ^ 2) ^ 6 := by
  have h1 : deriv Zf = fun y : ℝ => (2 * y - 6 * y ^ 3) / (1 + y ^ 2) ^ 5 := by
    funext y; rw [deriv_Zf]
  rw [h1]
  change deriv ((fun y : ℝ => 2 * y - 6 * y ^ 3) / (fun y : ℝ => (1 + y ^ 2) ^ 5)) z = _
  rw [deriv_div (by fun_prop) (by fun_prop) (by positivity)]
  have hnum : deriv (fun y : ℝ => 2 * y - 6 * y ^ 3) z = 2 - 18 * z ^ 2 := by
    change deriv ((fun y : ℝ => 2 * y) - (fun y : ℝ => 6 * y ^ 3)) z = 2 - 18 * z ^ 2
    rw [deriv_sub (by fun_prop) (by fun_prop), deriv_const_mul 2 (by fun_prop),
      deriv_const_mul 6 (by fun_prop), deriv_fun_pow differentiableAt_id 3]
    simp only [deriv_id'', Nat.reduceSub, mul_one]
    ring
  have hden : deriv (fun y : ℝ => (1 + y ^ 2) ^ 5) z = 10 * z * (1 + z ^ 2) ^ 4 := by
    change deriv ((fun y : ℝ => 1 + y ^ 2) ^ 5) z = 10 * z * (1 + z ^ 2) ^ 4
    rw [deriv_pow (by fun_prop) 5]
    have h2 : deriv (fun y : ℝ => 1 + y ^ 2) z = 2 * z := by
      rw [deriv_const_add]
      change deriv (fun y : ℝ => y ^ 2) z = 2 * z
      rw [deriv_fun_pow differentiableAt_id 2]
      simp only [deriv_id'', Nat.reduceSub, mul_one]
      ring
    rw [h2]
    simp only [Nat.reduceSub]
    ring
  rw [hnum, hden]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The second derivative of `Zf` tends to `0` at `+∞` (like `z^{-8}`). -/
theorem tendsto_deriv2_Zf : Tendsto (fun z : ℝ => deriv (deriv Zf) z) atTop (𝓝 0) := by
  have heq : (fun z : ℝ => deriv (deriv Zf) z) =
      fun z : ℝ => 2 * z ^ 0 / (1 + z ^ 2) ^ 6 + (-36) * z ^ 2 / (1 + z ^ 2) ^ 6
        + 42 * z ^ 4 / (1 + z ^ 2) ^ 6 := by
    funext z; rw [deriv_deriv_Zf]; ring
  rw [heq]
  have h1 : Tendsto (fun z : ℝ => 2 * z ^ 0 / (1 + z ^ 2) ^ 6) atTop (𝓝 0) :=
    tendsto_mono_div 2 0 6 (by norm_num)
  have h2 : Tendsto (fun z : ℝ => (-36) * z ^ 2 / (1 + z ^ 2) ^ 6) atTop (𝓝 0) :=
    tendsto_mono_div (-36) 2 6 (by norm_num)
  have h3 : Tendsto (fun z : ℝ => 42 * z ^ 4 / (1 + z ^ 2) ^ 6) atTop (𝓝 0) :=
    tendsto_mono_div 42 4 6 (by norm_num)
  simpa using (h1.add h2).add h3

/-- The `j`-th plain `z`-derivative of the iterate `(∂_θ^i gA)`. -/
theorem pzIter_pthIter_gA (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pthIter i gA) z θ
      = ((deriv^[j]) Zf) z * ((deriv^[i]) Tf) θ := by
  induction j generalizing z with
  | zero => simp [Work.Spaces.pzIter, pthIter_gA]
  | succ j ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    rw [Function.iterate_succ_apply']
    have h1 : (fun z' : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i gA) z' θ)
        = fun z' => ((deriv^[i]) Tf θ) * (((deriv^[j]) Zf) z') := by
      funext z'; rw [ih z']; ring
    rw [h1, deriv_const_mul _ ((ContDiff.iterate_deriv j contDiff_smooth_Zf).differentiable
      (by simp)).differentiableAt]
    ring

/-- `(deriv^[2]) Zf = deriv (deriv Zf)`. -/
theorem deriv2_eq : (deriv^[2]) Zf = deriv (deriv Zf) := by
  have h : (deriv^[2]) Zf = deriv ((deriv^[1]) Zf) := Function.iterate_succ_apply' deriv 1 Zf
  rw [h, Function.iterate_one]

/-- **The requested decay**: `DecayInZ 2 gA`. -/
theorem DecayInZ_gA : Work.Spaces.DecayInZ 2 Work.R1G.gA := by
  intro j i hij θ hθ
  rw [show (fun z : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i gA) z θ)
      = (fun z : ℝ => ((deriv^[j]) Zf) z * ((deriv^[i]) Tf) θ) from by
        funext z; rw [pzIter_pthIter_gA]]
  have hj : j ≤ 2 := by omega
  interval_cases j
  · simpa [Function.iterate_zero] using tendsto_Zf.mul_const (((deriv^[i]) Tf) θ)
  · simpa [Function.iterate_one] using tendsto_deriv_Zf.mul_const (((deriv^[i]) Tf) θ)
  · have h2 : Tendsto ((deriv^[2]) Zf) atTop (𝓝 0) := by
      rw [deriv2_eq]; exact tendsto_deriv2_Zf
    simpa using h2.mul_const (((deriv^[i]) Tf) θ)

end Work.R1G
