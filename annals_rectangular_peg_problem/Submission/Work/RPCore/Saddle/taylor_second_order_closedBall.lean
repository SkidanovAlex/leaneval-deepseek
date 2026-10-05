import Mathlib

/-!
# Taylor's theorem, second order, upper bound on a closed ball

`Work.RPCore.Saddle.taylor_second_order_closedBall`: for a `C^2` real-valued function `F` on a
finite-dimensional real normed space and any radius `ρ`, there is a constant `M ≥ 0` with
`F (z + h) ≤ F z + (fderiv ℝ F z) h + M / 2 * ‖h‖ ^ 2`
for all `z`, `h` with `‖z‖ ≤ ρ` and `‖z + h‖ ≤ ρ`.

The proof bounds the derivative of `fderiv ℝ F` on the compact ball `Metric.closedBall 0 ρ`
(using that `fderiv ℝ F` is `C^1`, hence its derivative — the second derivative of `F` — is
bounded on the compact ball), integrates this Lipschitz bound along the segment `[z, z + h]`
via the "fencing" mean value theorem in one dimension, and compares with the parabola
`t ↦ F z + t * (fderiv ℝ F z) h + t^2 * (M / 2 * ‖h‖ ^ 2)`.
-/

namespace Work.RPCore.Saddle

noncomputable section

/-- Derivative of `t ↦ F (z + t • h)` along the line through `z` in direction `h`. -/
private lemma hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (z h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (z + s • h)) ((fderiv ℝ F (z + t • h)) h) t := by
  have hg : HasDerivAt (fun s : ℝ => z + s • h) h t := by
    have h1 : HasDerivAt (fun s : ℝ => s • h) h t := by
      simpa using (hasDerivAt_id t).smul_const h
    simpa using h1.const_add z
  have hFd : HasFDerivAt F (fderiv ℝ F (z + t • h)) (z + t • h) :=
    (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  exact hFd.comp_hasDerivAt t hg

/-- Derivative of the quadratic comparison function `t ↦ A + t * c + t ^ 2 * d`. -/
private lemma hasDerivAt_quad (A c d t : ℝ) :
    HasDerivAt (fun s : ℝ => A + s * c + s ^ 2 * d) (c + 2 * t * d) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * c) c t := by
    simpa using (hasDerivAt_id t).mul_const c
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * d) (2 * t * d) t := by
    have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    simpa using hp.mul_const d
  have h3 : HasDerivAt (fun s : ℝ => A + (s * c + s ^ 2 * d)) (c + 2 * t * d) t := by
    simpa using (h1.add h2).const_add A
  simpa [add_assoc] using h3

/-- On the closed ball of radius `ρ`, `fderiv ℝ F` is Lipschitz (for `F` twice continuously
differentiable on a finite-dimensional space). The constant is a bound for the second derivative
of `F`, which is continuous and the ball is compact. -/
private lemma fderiv_lipschitzOn_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → ℝ) (hF : ContDiff ℝ 2 F) (ρ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ K * ‖x - y‖ := by
  have hG : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hGdiff : Differentiable ℝ (fderiv ℝ F) := hG.differentiable (by norm_num)
  have hcont : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ F) x‖) :=
    (hG.continuous_fderiv (by norm_num)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) ρ).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x y hx hy
  have hx' : x ∈ Metric.closedBall (0 : E) ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hy' : y ∈ Metric.closedBall (0 : E) ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hGdiff.differentiableAt)
    (fun x hxmem => by
      have h1 := hC x hxmem
      rw [Real.norm_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ F) x))] at h1
      exact h1.trans (le_max_left C 0))
    (convex_closedBall 0 ρ) hy' hx'

theorem taylor_second_order_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → ℝ) (hF : ContDiff ℝ 2 F) (ρ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z h : E, ‖z‖ ≤ ρ → ‖z + h‖ ≤ ρ →
      F (z + h) ≤ F z + (fderiv ℝ F z) h + M / 2 * ‖h‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := fderiv_lipschitzOn_closedBall F hF ρ
  refine ⟨K, hK0, ?_⟩
  intro z h hz hzh
  set c : ℝ := (fderiv ℝ F z) h with hc
  set d : ℝ := K / 2 * ‖h‖ ^ 2 with hd
  have hf_cont : ContinuousOn (fun t : ℝ => F (z + t • h)) (Set.Icc 0 1) :=
    hF.continuous.comp_continuousOn (by fun_prop)
  have hB_cont : ContinuousOn (fun t : ℝ => F z + t * c + t ^ 2 * d) (Set.Icc 0 1) := by fun_prop
  have hf'_deriv : ∀ t ∈ Set.Ico 0 1,
      HasDerivWithinAt (fun s : ℝ => F (z + s • h)) ((fderiv ℝ F (z + t • h)) h) (Set.Ici t) t :=
    fun t _ => (hasDerivAt_line F hF z h t).hasDerivWithinAt
  have hB'_deriv : ∀ t ∈ Set.Ico 0 1,
      HasDerivWithinAt (fun s : ℝ => F z + s * c + s ^ 2 * d) (c + 2 * t * d) (Set.Ici t) t :=
    fun t _ => (hasDerivAt_quad (F z) c d t).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico 0 1, (fderiv ℝ F (z + t • h)) h ≤ c + 2 * t * d := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hmem : ‖z + t • h‖ ≤ ρ := by
      have hzht : z + t • h = (1 - t) • z + t • (z + h) := by
        rw [sub_smul, one_smul, smul_add]; abel
      rw [hzht]
      calc ‖(1 - t) • z + t • (z + h)‖ ≤ ‖(1 - t) • z‖ + ‖t • (z + h)‖ := norm_add_le _ _
        _ = (1 - t) * ‖z‖ + t * ‖z + h‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
                Real.norm_of_nonneg ht0]
        _ ≤ (1 - t) * ρ + t * ρ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hz (by linarith [ht.2])
              · exact mul_le_mul_of_nonneg_left hzh ht0
        _ = ρ := by ring
    have hL := hK (z + t • h) z hmem hz
    have hL' : ‖fderiv ℝ F (z + t • h) - fderiv ℝ F z‖ ≤ K * (t * ‖h‖) := by
      have hsub : ‖(z + t • h) - z‖ = t * ‖h‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      rwa [hsub] at hL
    have hstep : (fderiv ℝ F (z + t • h)) h - c ≤ t * K * ‖h‖ ^ 2 := by
      calc (fderiv ℝ F (z + t • h)) h - c
          = (fderiv ℝ F (z + t • h) - fderiv ℝ F z) h := by
              rw [hc, sub_apply]
        _ ≤ ‖(fderiv ℝ F (z + t • h) - fderiv ℝ F z) h‖ := le_abs_self _
        _ ≤ ‖fderiv ℝ F (z + t • h) - fderiv ℝ F z‖ * ‖h‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K * (t * ‖h‖)) * ‖h‖ :=
              mul_le_mul_of_nonneg_right hL' (norm_nonneg _)
        _ = t * K * ‖h‖ ^ 2 := by ring
    have h2d : c + 2 * t * d = c + t * K * ‖h‖ ^ 2 := by rw [hd]; ring
    rw [h2d]; linarith
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1) hf_cont hf'_deriv
    (by simp) hB_cont hB'_deriv hbound
  have h1 := key (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hfin : F (z + h) ≤ F z + c + d := by simpa using h1
  calc F (z + h) ≤ F z + c + d := hfin
    _ = F z + (fderiv ℝ F z) h + K / 2 * ‖h‖ ^ 2 := by rw [hc, hd]

end

end Work.RPCore.Saddle
