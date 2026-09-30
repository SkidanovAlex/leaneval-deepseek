import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Smoothness of the map `x ↦ (g x).inverse` for a pointwise positive-definite bilinear form

Let `E` be a finite-dimensional real normed space and let `g : X → E →L[ℝ] E →L[ℝ] ℝ` be a family
of continuous bilinear forms on `E`, each of which is positive on the diagonal
(`∀ v ≠ 0, 0 < g x v v`).  The main result of this file,

    `Work.LeviCivita.contDiffAt_inverse_of_posDef`,

states that if `g` is `C^n` at `x₀`, then so is the map `x ↦ (g x).inverse`, where
`ContinuousLinearMap.inverse` sends `g x : E →L[ℝ] E →L[ℝ] ℝ` to its inverse
`(E →L[ℝ] ℝ) →L[ℝ] E`.

## Proof outline

The pointwise `ContinuousLinearMap.inverse` is a *globally defined* function which is `C^n` at
every invertible map (`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`, proved from the
analyticity of `Ring.inverse` on the units of the Banach algebra `E →L[ℝ] E`).  Hence it suffices
to know that `g x₀` is invertible, and then to compose.

That `g x₀` is invertible is `Work.LeviCivita.isInvertible_of_posDef`: positivity on the diagonal
makes `g x₀ : E → E*` injective, and since `finrank ℝ E = finrank ℝ (E →L[ℝ] ℝ)` (as
`E →L[ℝ] ℝ ≃ₗ[ℝ] Module.Dual ℝ E`), injectivity upgrades to bijectivity, i.e. to a continuous
linear equivalence.
-/

open scoped ContDiff

namespace Work.LeviCivita

open Module

/-- **A bilinear form on a finite-dimensional real normed space that is positive on the diagonal
is invertible.**  Positivity on the diagonal forces the associated map `E → E*` to be injective,
and injective endomorphisms of a finite-dimensional space of the same dimension as their target
are bijective; this gives a `ContinuousLinearEquiv` and hence
`ContinuousLinearMap.IsInvertible`. -/
private lemma isInvertible_of_posDef_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, v ≠ 0 → 0 < B v v) :
    B.IsInvertible := by
  -- positivity on the diagonal makes `B` injective: `B u = B v` with `u ≠ v` would give
  -- `B (u - v) (u - v) = 0`, contradicting `0 < B (u - v) (u - v)`
  have hinj : Function.Injective B := by
    intro u v huv
    by_contra hne
    have h1 : u - v ≠ 0 := sub_ne_zero.mpr hne
    have huu : B (u - v) (u - v) = 0 := by
      simp [map_sub, huv]
    exact absurd huu (ne_of_gt (hB (u - v) h1))
  -- the domain and the target have the same dimension
  have hdim : finrank ℝ E = finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq]
    exact (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hker : (B : E →ₗ[ℝ] (E →L[ℝ] ℝ)).ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : (B : E →ₗ[ℝ] (E →L[ℝ] ℝ)).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  exact ⟨ContinuousLinearEquiv.ofBijective B hker hrange,
    ContinuousLinearEquiv.coe_ofBijective B hker hrange⟩

open scoped ContDiff in
theorem contDiffAt_inverse_of_posDef
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {g : X → E →L[ℝ] E →L[ℝ] ℝ} {x₀ : X} {n : ℕ∞ω}
    (hg : ContDiffAt ℝ n g x₀) (hpos : ∀ x, ∀ v, v ≠ 0 → 0 < g x v v) :
    ContDiffAt ℝ n (fun x ↦ (g x).inverse) x₀ := by
  -- `g x₀` is invertible, so `ContinuousLinearMap.inverse` is `C^n` at `g x₀`
  have hI : (g x₀).IsInvertible := isInvertible_of_posDef_aux (g x₀) (hpos x₀)
  have h1 : ContDiffAt ℝ n ContinuousLinearMap.inverse (g x₀) := hI.contDiffAt_map_inverse
  -- compose with `hg`
  simpa only [Function.comp_def] using h1.comp x₀ hg

end Work.LeviCivita
