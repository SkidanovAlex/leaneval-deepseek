import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Asymptotics

open Filter
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-- If `y t = (c * t) • a + o t` eventually and `o` is a little-`o` of `t` at `+∞`, then the
weighted sum of squared norms `∑ i, m i * ‖y t i‖ ^ 2`, divided by `t ^ 2`, converges to
`∑ i, m i * ‖(c • a) i‖ ^ 2`.

The statement is stated for `y`, `o` and `a` in the product `EuclideanSpace E (Fin N)` of a
finite-dimensional real inner product space `E`; the proof goes through the coordinate
convergence `y t i / t → (c • a) i`. -/
lemma tendsto_sum_norm_sq_div_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (m : Fin N → ℝ) {c : ℝ} (hc : c ≠ 0)
    (a : EuclideanSpace E (Fin N)) {y : ℝ → EuclideanSpace E (Fin N)}
    {o : ℝ → EuclideanSpace E (Fin N)} (ho : o =o[atTop] fun t : ℝ => t)
    (hasym : ∀ᶠ t in atTop, y t = (c * t) • a + o t) :
    Tendsto (fun t : ℝ => (∑ i, m i * ‖y t i‖ ^ 2) / t ^ 2) atTop
      (𝓝 (∑ i, m i * ‖(c • a) i‖ ^ 2)) := by
  -- `o t / t → 0`, as a vector of `EuclideanSpace E (Fin N)`.
  have ho_norm : (fun t : ℝ => ‖o t‖) =o[atTop] (fun t : ℝ => t) := ho.norm_left
  have ho_div : Tendsto (fun t : ℝ => ‖o t‖ / t) atTop (𝓝 0) := ho_norm.tendsto_div_nhds_zero
  have h_inv_smul_o : Tendsto (fun t : ℝ => t⁻¹ • o t) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Tendsto.congr' ?_ ho_div
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_eq_one_div]
    ring
  -- `t⁻¹ • y t → c • a`.
  have h_main : Tendsto (fun t : ℝ => t⁻¹ • y t) atTop (𝓝 (c • a)) := by
    have h_eq : (fun t : ℝ => t⁻¹ • y t)
        =ᶠ[atTop] (fun t : ℝ => c • a + t⁻¹ • o t) := by
      filter_upwards [hasym, eventually_ne_atTop (0 : ℝ)] with t ht ht0
      rw [ht, smul_add, smul_smul]
      have hct : t⁻¹ * (c * t) = c := by
        rw [mul_comm c t, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
      rw [hct]
    have h2 : Tendsto (fun t : ℝ => c • a + t⁻¹ • o t) atTop (𝓝 (c • a)) := by
      have h0 : Tendsto (fun _ : ℝ => c • a) atTop (𝓝 (c • a)) := tendsto_const_nhds
      simpa using h0.add h_inv_smul_o
    exact Tendsto.congr' h_eq.symm h2
  -- coordinate-wise convergence of `‖y t i‖ / t`.
  have hnorm_i : ∀ i : Fin N, Tendsto (fun t : ℝ => ‖y t i‖ / t) atTop (𝓝 ‖(c • a) i‖) := by
    intro i
    have hcoord : Tendsto (fun t : ℝ => (t⁻¹ • y t) i) atTop (𝓝 ((c • a) i)) := by
      have hcont : Continuous (fun z : EuclideanSpace E (Fin N) => z i) :=
        PiLp.continuous_apply 2 (fun _ : Fin N => E) i
      have := (hcont.tendsto (c • a)).comp h_main
      simpa [Function.comp_def] using this
    have h1 : Tendsto (fun t : ℝ => ‖(t⁻¹ • y t) i‖) atTop (𝓝 ‖(c • a) i‖) := hcoord.norm
    refine Tendsto.congr' ?_ h1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [PiLp.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    rw [div_eq_mul_inv, mul_comm]
  -- pass to the finite sum.
  have hsum : Tendsto (fun t : ℝ => ∑ i, m i * (‖y t i‖ / t) ^ 2) atTop
      (𝓝 (∑ i, m i * ‖(c • a) i‖ ^ 2)) := by
    have h := tendsto_finsetSum Finset.univ
      (f := fun i : Fin N => fun t : ℝ => m i * (‖y t i‖ / t) ^ 2)
      (a := fun i : Fin N => m i * ‖(c • a) i‖ ^ 2)
      (fun i _ => ((hnorm_i i).pow 2).const_mul (m i))
    simpa using h
  refine Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_div_assoc, ← div_pow]

end Commons.Analysis.Asymptotics