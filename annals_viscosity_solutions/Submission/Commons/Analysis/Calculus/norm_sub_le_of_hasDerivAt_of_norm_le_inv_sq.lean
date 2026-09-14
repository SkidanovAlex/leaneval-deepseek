import Mathlib

namespace Commons.Analysis.Calculus

open Filter Set MeasureTheory
open scoped Topology

/-- The derivative of `t ↦ K / t` at a nonzero point `x`, written in the exact normal form used
below (`-(K / x ^ 2)`). -/
private lemma hasDerivAt_const_div (K x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => K / t) (-(K / x ^ 2)) x := by
  have h := (hasDerivAt_const x K).mul (hasDerivAt_inv hx)
  have hfun : ((fun _ : ℝ => K) * fun y => y⁻¹) = (fun t : ℝ => K / t) := by
    funext t; simp [div_eq_mul_inv]
  have hval : (0 * x⁻¹ + K * -(x ^ 2)⁻¹) = -(K / x ^ 2) := by ring
  rw [hfun, hval] at h
  exact h

/-- If a differentiable curve `f : ℝ → E` has derivative bounded by `K / t ^ 2` on an interval
`[a, b]` with `a > 0`, then the total displacement is bounded by `K / a`.

This is the variable-coefficient extension of the mean value inequality, obtained by fencing the
function `u ↦ ‖f u - f a‖` against the explicit barrier `u ↦ K / a - K / u`, whose derivative is
`K / u ^ 2`. In particular the proof does not require `E` to be complete. -/
theorem norm_sub_le_of_hasDerivAt_of_norm_le_inv_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f f' : ℝ → E} {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hcont : ContinuousOn f' (Set.Icc a b))
    (hbd : ∀ t ∈ Set.Icc a b, ‖f' t‖ ≤ K / t ^ 2) :
    ‖f b - f a‖ ≤ K / a := by
  have _ : ContinuousOn f' (Set.Icc a b) := hcont
  -- The hypothesis at `t = a` forces `K ≥ 0`.
  have hK : 0 ≤ K := by
    have h0 : 0 ≤ K / a ^ 2 := le_trans (norm_nonneg _) (hbd a (left_mem_Icc.mpr hab))
    have h2 := mul_nonneg h0 (sq_nonneg a)
    rwa [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt ha))] at h2
  -- Fence `u ↦ f u - f a` against the barrier `u ↦ K / a - K / u`.
  have hgcont : ContinuousOn (fun t : ℝ => f t - f a) (Icc a b) :=
    (HasDerivAt.continuousOn hf).sub continuousOn_const
  have hg' : ∀ x ∈ Ico a b, HasDerivWithinAt (fun t : ℝ => f t - f a) (f' x) (Ici x) x := by
    intro x hx
    exact ((hf x (Ico_subset_Icc_self hx)).sub_const (f a)).hasDerivWithinAt
  have haB : ‖(fun t : ℝ => f t - f a) a‖ ≤ (fun t : ℝ => K / a - K / t) a := by
    simp
  have hBcont : ContinuousOn (fun t : ℝ => K / a - K / t) (Icc a b) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hB' : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun t : ℝ => K / a - K / t) (K / x ^ 2) (Ici x) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    have h2 : HasDerivAt (fun t : ℝ => K / a - K / t) (K / x ^ 2) x := by
      have h := (hasDerivAt_const x (K / a)).sub (hasDerivAt_const_div K x hxne)
      have hfun : ((fun _ : ℝ => K / a) - fun t => K / t) =
          (fun t : ℝ => K / a - K / t) := by
        funext t; simp
      have hval : (0 - -(K / x ^ 2)) = K / x ^ 2 := by ring
      rw [hfun, hval] at h
      exact h
    exact h2.hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ (fun t : ℝ => K / t ^ 2) x :=
    fun x hx => hbd x (Ico_subset_Icc_self hx)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      hgcont hg' haB hBcont hB' hbound
  have hbnd : ‖f b - f a‖ ≤ K / a - K / b := by
    have := key (right_mem_Icc.mpr hab)
    simpa using this
  have hKb : 0 ≤ K / b := div_nonneg hK (le_of_lt (lt_of_lt_of_le ha hab))
  linarith

end Commons.Analysis.Calculus
