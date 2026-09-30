import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LeviCivita

open Module

open scoped ContDiff in
/-- A continuous `ℝ`-bilinear form on a finite-dimensional real Banach space whose associated
quadratic form is positive definite is invertible as a map `E → E*`, i.e. it is the forward
direction of a continuous linear equivalence `E ≃L[ℝ] (E →L[ℝ] ℝ)`.

Indeed, `v ↦ g v` is injective: if `g v = 0` then `g v v = 0`, contradicting positivity at `v ≠ 0`.
Since `E` and its continuous dual have the same finite dimension, injectivity implies
surjectivity, and a bijective continuous linear map between Banach spaces has a continuous
inverse. -/
theorem isInvertible_of_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (g : E →L[ℝ] E →L[ℝ] ℝ) (hg : ∀ v, v ≠ 0 → 0 < g v v) :
    g.IsInvertible := by
  -- `E` and its continuous dual `E →L[ℝ] ℝ` have the same dimension.
  have hfin : finrank ℝ E = finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← Subspace.dual_finrank_eq (K := ℝ) (V := E)]
    exact (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (F' := ℝ)).finrank_eq
  -- `g` is injective.
  have hker : (g : E →ₗ[ℝ] (E →L[ℝ] ℝ)).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro u v huv
    have hsub : u - v = 0 := by
      by_contra hne
      have h0 : g (u - v) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr huv
      have hpos := hg (u - v) hne
      rw [h0] at hpos
      simp at hpos
    exact sub_eq_zero.mp hsub
  have hinj : Function.Injective (g : E → (E →L[ℝ] ℝ)) := LinearMap.ker_eq_bot.mp hker
  -- hence `g` is onto.
  have hsurj : Function.Surjective (g : E → (E →L[ℝ] ℝ)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective g hker (LinearMap.range_eq_top.mpr hsurj),
    ContinuousLinearEquiv.coe_ofBijective g hker (LinearMap.range_eq_top.mpr hsurj)⟩

end Work.LeviCivita
