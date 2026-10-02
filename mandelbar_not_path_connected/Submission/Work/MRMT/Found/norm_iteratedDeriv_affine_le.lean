import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- The `N`-th derivative of the normalized affine pull-back `u ↦ g (z - u • t)` at the point
`s` is `D^N g (z - s • t)` evaluated on `N` copies of `-t`; in particular its norm is bounded
by the uniform bound `K` on `‖D^N g‖` times `‖t‖^N`. -/
theorem norm_iteratedDeriv_affine_le {g : ℂ → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (N : ℕ) {K : ℝ} (hK : ∀ w : ℂ, ‖iteratedFDeriv ℝ N g w‖ ≤ K) (z t : ℂ) (s : ℝ) :
    ‖iteratedDeriv N (fun u : ℝ => g (z - u • t)) s‖ ≤ K * ‖t‖ ^ N := by
  -- The function is the composite of a shift `w ↦ g (z + w)` with the linear map `u ↦ u • (-t)`.
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => g (z + w)) := by fun_prop
  set L : ℝ →L[ℝ] ℂ := ContinuousLinearMap.toSpanSingleton ℝ (-t) with hL
  have hL_apply : ∀ u : ℝ, L u = u • (-t) := fun u => by
    rw [hL]; exact ContinuousLinearMap.toSpanSingleton_apply ℝ (-t) u
  have hfun : (fun w : ℂ => g (z + w)) ∘ L = (fun u : ℝ => g (z - u • t)) := by
    funext u
    simp only [Function.comp_apply, hL_apply, smul_neg, sub_eq_add_neg]
  -- Chain rule: the iterated derivative descends to the `N`-th Fréchet derivative of `g`,
  -- whose `N` arguments are all the image of `1` under `L`, namely `-t`.
  have key : iteratedDeriv N (fun u : ℝ => g (z - u • t)) s
      = iteratedFDeriv ℝ N g (z - s • t) (fun _ : Fin N => -t) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← hfun]
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hφ s (by simp)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [iteratedFDeriv_comp_add_left]
    simp only [hL_apply, one_smul, smul_neg]
    congr 1
  rw [key]
  calc ‖iteratedFDeriv ℝ N g (z - s • t) (fun _ : Fin N => -t)‖
      ≤ ‖iteratedFDeriv ℝ N g (z - s • t)‖ * ∏ i : Fin N, ‖(fun _ => -t) i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ N g (z - s • t)‖ * ‖t‖ ^ N := by
        simp [Finset.prod_const, norm_neg]
    _ ≤ K * ‖t‖ ^ N :=
        mul_le_mul_of_nonneg_right (hK _) (pow_nonneg (norm_nonneg t) N)

end Work.MRMT.Found
