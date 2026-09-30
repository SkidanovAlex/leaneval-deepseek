import Mathlib.Analysis.ODE.Gronwall

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Set

theorem dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x y x' y' : ℝ → F} {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hx : ∀ t ∈ Set.Icc a b, HasDerivAt x (x' t) t)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (y' t) t)
    (hxy : ∀ t ∈ Set.Icc a b, ‖x' t - y' t‖ ≤ L * ‖x t - y t‖) :
    dist (x b) (y b) ≤ dist (x a) (y a) * Real.exp (L * (b - a)) := by
  have hcont : ContinuousOn (fun t => x t - y t) (Set.Icc a b) := fun t ht =>
    ((hx t ht).continuousAt.sub (hy t ht).continuousAt).continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt (fun t => x t - y t) (x' t - y' t) (Set.Ici t) t :=
    fun t ht => ((hx t (Set.Ico_subset_Icc_self ht)).sub
      (hy t (Set.Ico_subset_Icc_self ht))).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico a b, ‖x' t - y' t‖ ≤ L * ‖x t - y t‖ + 0 := by
    intro t ht
    rw [add_zero]
    exact hxy t (Set.Ico_subset_Icc_self ht)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun t => x t - y t) (f' := fun t => x' t - y' t)
    (δ := ‖x a - y a‖) (K := L) (ε := 0) (a := a) (b := b)
    hcont hderiv (le_refl _) hbound b ⟨hab, le_refl b⟩
  rw [gronwallBound_ε0] at h
  rwa [dist_eq_norm, dist_eq_norm]

end Commons.Analysis.ODE