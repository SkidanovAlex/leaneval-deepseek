import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Second-order Taylor bound (mean-value form): if `f` has derivative `f'` on the segment
`[u, u+δ]`, `f'` is complex-differentiable there, and `‖deriv f'‖ ≤ M` on the segment, then the
first-order Taylor remainder at `u` is bounded by `M ‖δ‖ ^ 2`. -/
theorem taylor_second_order (f f' : ℂ → ℂ) (u δ : ℂ) (M : ℝ)
    (hd : ∀ w ∈ segment ℝ u (u + δ), HasDerivAt f (f' w) w)
    (hfd : ∀ w ∈ segment ℝ u (u + δ), DifferentiableAt ℂ f' w)
    (hM : ∀ w ∈ segment ℝ u (u + δ), ‖deriv f' w‖ ≤ M) :
    ‖f (u + δ) - f u - δ * f' u‖ ≤ M * ‖δ‖ ^ 2 := by
  have hconv : Convex ℝ (segment ℝ u (u + δ)) := convex_segment u (u + δ)
  have hu : u ∈ segment ℝ u (u + δ) := left_mem_segment ℝ u (u + δ)
  have hy : u + δ ∈ segment ℝ u (u + δ) := right_mem_segment ℝ u (u + δ)
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM u hu)
  -- Step 1: `f'` is `M`-Lipschitz along the segment, so ‖f' z - f' u‖ ≤ M ‖δ‖.
  have step1 : ∀ z ∈ segment ℝ u (u + δ), ‖f' z - f' u‖ ≤ M * ‖δ‖ := by
    intro z hz
    have h1 : ‖f' z - f' u‖ ≤ M * ‖z - u‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le hfd hM hconv hu hz
    have h2 : ‖z - u‖ ≤ ‖δ‖ := by simpa using norm_sub_le_of_mem_segment hz
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hMnn)
  -- Step 2: the mean-value inequality with the constant linear map `φ = (· • f' u)`.
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := f) (f' := fun z => ContinuousLinearMap.toSpanSingleton ℂ (f' z))
      (φ := ContinuousLinearMap.toSpanSingleton ℂ (f' u))
      (C := M * ‖δ‖) (s := segment ℝ u (u + δ)) (x := u) (y := u + δ)
      (fun z hz => (hd z hz).hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => by
        have e : ContinuousLinearMap.toSpanSingleton ℂ (f' z)
              - ContinuousLinearMap.toSpanSingleton ℂ (f' u)
            = ContinuousLinearMap.toSpanSingleton ℂ (f' z - f' u) := by
          have h := ContinuousLinearMap.toSpanSingleton_add ℂ (f' z - f' u) (f' u)
          rw [sub_add_cancel] at h
          rw [h, add_sub_cancel_right]
        rw [e, ContinuousLinearMap.norm_toSpanSingleton]
        exact step1 z hz)
      hconv hu hy
  -- Rewrite the conclusion of the mean-value inequality into the goal.
  have hphi : (ContinuousLinearMap.toSpanSingleton ℂ (f' u)) ((u + δ) - u) = δ * f' u := by
    rw [show (u + δ) - u = δ by ring, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hdist : ‖(u + δ) - u‖ = ‖δ‖ := by rw [show (u + δ) - u = δ by ring]
  rw [hphi, hdist] at key
  calc
    ‖f (u + δ) - f u - δ * f' u‖ ≤ (M * ‖δ‖) * ‖δ‖ := key
    _ = M * ‖δ‖ ^ 2 := by ring

end Work.PARIMPL2.Direct
