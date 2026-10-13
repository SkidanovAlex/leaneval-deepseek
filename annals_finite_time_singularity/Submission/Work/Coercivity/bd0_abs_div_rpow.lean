import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- For `z > 0` the boundary quantity `z (f z θ · w z)²` of the integration-by-parts
hypothesis is exactly the square of `|f z θ| / z^{3/2}` up to the factor `(1+z)⁴`:
`z (f z θ w z)² = (|f z θ| / z^{3/2})² (1+z)⁴`.  Since `w z = (1+z)²/z²`, this is just
`z (f z θ)² (1+z)⁴ / z⁴ = (|f z θ|² / z³) (1+z)⁴`. -/
private theorem zw_sq_eq_abs_div_rpow_sq (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hz : 0 < z) :
    z * (f z θ * Spaces.w z) ^ 2 = (|f z θ| / z ^ (3 / 2 : ℝ)) ^ 2 * (1 + z) ^ 4 := by
  have hz3 : (z ^ (3 / 2 : ℝ)) ^ 2 = z ^ 3 := by
    calc (z ^ (3 / 2 : ℝ)) ^ 2 = z ^ (3 / 2 : ℝ) * z ^ (3 / 2 : ℝ) := by rw [pow_two]
      _ = z ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ)) := (Real.rpow_add hz (3 / 2) (3 / 2)).symm
      _ = z ^ 3 := by norm_num
  have h1 : (|f z θ| / z ^ (3 / 2 : ℝ)) ^ 2 = (f z θ) ^ 2 / z ^ 3 := by
    rw [div_pow, sq_abs, hz3]
  rw [h1, Spaces.w]
  field_simp

/-- **Vanishing of `|f z θ| / z^{3/2}` at `z = 0⁺`.**  The integration-by-parts
hypothesis `IBP f` says that the boundary quantity `z (f z θ · w z)²` of the `z`-by-parts
vanishes at `z = 0⁺`; substituting `w z = (1+z)²/z²` this is the statement that
`(|f z θ| / z^{3/2})² (1+z)⁴ → 0`, and since `(1+z)⁴ → 1 ≠ 0` the square of
`|f z θ| / z^{3/2}` tends to `0`, hence so does `|f z θ| / z^{3/2}` itself. -/
theorem bd0_abs_div_rpow (f : ℝ → ℝ → ℝ) (hf : IBP f) :
    ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => |f z θ| / z ^ (3 / 2 : ℝ))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro θ hθ
  -- the boundary quantity of `IBP` is `(|f z θ| / z^{3/2})² (1+z)⁴` on `z > 0`
  have hev : (fun z => z * (f z θ * Spaces.w z) ^ 2)
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
      (fun z => (|f z θ| / z ^ (3 / 2 : ℝ)) ^ 2 * (1 + z) ^ 4) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact zw_sq_eq_abs_div_rpow_sq f z θ hz
  have h1 : Filter.Tendsto (fun z => (|f z θ| / z ^ (3 / 2 : ℝ)) ^ 2 * (1 + z) ^ 4)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
    (hf.bd0 θ hθ).congr' hev
  -- the factor `(1 + z)⁴` tends to `1 ≠ 0`
  have h2 : Filter.Tendsto (fun z => (1 + z) ^ 4)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hc : Continuous (fun z : ℝ => (1 + z) ^ 4) :=
      (continuous_const.add continuous_id).pow 4
    have hle : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ 𝓝 (0:ℝ) := nhdsWithin_le_nhds
    have := (hc.tendsto 0).mono_left hle
    simpa using this
  -- dividing, the square of `|f z θ| / z^{3/2}` tends to `0`
  have h3 : Filter.Tendsto (fun z => (|f z θ| / z ^ (3 / 2 : ℝ)) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hdiv : Filter.Tendsto
        (fun z => ((|f z θ| / z ^ (3 / 2 : ℝ)) ^ 2 * (1 + z) ^ 4) / (1 + z) ^ 4)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (0 / 1)) :=
      h1.div h2 (by norm_num)
    rw [zero_div] at hdiv
    refine Filter.Tendsto.congr' ?_ hdiv
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzpos : (0:ℝ) < z := hz
    have hz1 : (1 + z) ^ 4 ≠ 0 := pow_ne_zero 4 (by linarith : (1:ℝ) + z ≠ 0)
    exact mul_div_cancel_right₀ _ hz1
  -- taking the square root
  have h4 : Filter.Tendsto (fun z => Real.sqrt ((|f z θ| / z ^ (3 / 2 : ℝ)) ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have := h3.sqrt
    simpa using this
  refine Filter.Tendsto.congr' ?_ h4
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzpos : (0:ℝ) < z := hz
  have hz32 : (0:ℝ) ≤ |f z θ| / z ^ (3 / 2 : ℝ) := by
    exact div_nonneg (abs_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hzpos _))
  exact Real.sqrt_sq hz32

end Work.Coercivity
