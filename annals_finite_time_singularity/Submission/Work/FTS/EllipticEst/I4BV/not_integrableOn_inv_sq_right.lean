import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Tactic.Have

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
The function `θ ↦ c / (b - θ)²` (`c > 0`) has a non-integrable singularity at the *right*
endpoint `b` of the interval `(b - ε, b)`: it blows up like `(b - θ)^{-2}`, and a positive
power-function singularity of exponent `≤ -1` is not integrable.

The proof avoids any change of variables: it feeds the standard Mathlib criterion
`not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter` the antiderivative
`f x = (b - x)⁻¹`, whose derivative `(b - x)⁻¹ ^ 2` blows up like `(b - x)^{-2}` as `x → b⁻`
(so `‖f x‖ → ∞`), while `deriv f x = c⁻¹ * (c / (b - x)²)` is `O` of the integrand.
-/

namespace Work.FTS.EllipticEst.I4BV

open MeasureTheory Filter Set
open scoped Topology

theorem not_integrableOn_inv_sq_right {c b ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => c / (b - θ) ^ 2) (Set.Ioo (b - ε) b) := by
  set f : ℝ → ℝ := fun x => (b - x)⁻¹ with hf
  -- `f` is differentiable off `b`, with derivative `(b - x)⁻¹ ^ 2`
  have hdAt : ∀ x, x ≠ b → HasDerivAt f (((b - x)⁻¹) ^ 2) x := by
    intro x hx
    have hne : b - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have h1 : HasDerivAt (fun y : ℝ => b - y) (-1) x := (hasDerivAt_id x).const_sub b
    have h3 := h1.inv hne
    convert h3 using 1
    rw [inv_pow, neg_neg, one_div]
  -- `b - x → 0⁺` along `𝓝[<] b`
  have hsub : Tendsto (fun x : ℝ => b - x) (𝓝[<] b) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun x : ℝ => b - x) (𝓝 b) (𝓝 (b - b)) :=
        (continuous_const.sub continuous_id).tendsto b
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio] at hx
      exact sub_pos.mpr hx
  -- hence `‖f x‖ → ∞` along `𝓝[<] b`
  have htop : Tendsto (fun x => ‖f x‖) (𝓝[<] b) atTop := by
    have hbase : Tendsto (fun x : ℝ => (b - x)⁻¹) (𝓝[<] b) atTop :=
      tendsto_inv_nhdsGT_zero.comp hsub
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Iio] at hx
    have hpos : 0 < b - x := sub_pos.mpr hx
    rw [hf]
    simp only
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  have hdiff : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Iio] at hx
    exact (hdAt x (ne_of_lt hx)).differentiableAt
  -- `deriv f` is a constant multiple of the integrand
  have hA : deriv f =ᶠ[𝓝[<] b] fun x => c⁻¹ * (c / (b - x) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Iio] at hx
    have hxb : x ≠ b := ne_of_lt hx
    rw [(hdAt x hxb).deriv, inv_pow, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hc), one_mul]
  have hBigO : deriv f =O[𝓝[<] b] (fun x => c / (b - x) ^ 2) :=
    (hA.isBigO).trans
      (Asymptotics.isBigO_const_mul_self c⁻¹ (fun x => c / (b - x) ^ 2) (𝓝[<] b))
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter (𝓝[<] b)
    (Ioo_mem_nhdsLT (by linarith)) hdiff htop hBigO

end Work.FTS.EllipticEst.I4BV
