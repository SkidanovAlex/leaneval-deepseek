import Mathlib
import Submission.Work.Descent.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Descent

universe u

open scoped TensorProduct

/-- For a `k`-basis `c` of `k'` indexed by the Galois group there are, for each `τ₀`, coefficients
`m` with `∑ σ, m σ * σ (c τ)` equal to `1` at `τ = τ₀` and `0` elsewhere. -/
theorem exists_coeffs_right {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (c : Module.Basis (Work.Descent.Gal k k') k k')
    (τ₀ : Work.Descent.Gal k k') : ∃ m : Work.Descent.Gal k k' → k',
      (∑ σ, m σ * σ (c τ₀)) = 1 ∧
        ∀ τ : Work.Descent.Gal k k', τ ≠ τ₀ → ∑ σ, m σ * σ (c τ) = 0 := by
  classical
  -- The `k'`-linear map `m ↦ (τ ↦ ∑ σ, m σ * σ (c τ))`.
  let T : (Gal k k' → k') →ₗ[k'] (Gal k k' → k') :=
    { toFun := fun m τ => ∑ σ, m σ * σ (c τ)
      map_add' := by
        intro m n; ext τ
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro u m; ext τ
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        simp only [RingHom.id_apply]
        ring }
  have hT_apply : ∀ (m : Gal k k' → k') (τ : Gal k k'),
      T m τ = ∑ σ, m σ * σ (c τ) := fun m τ => rfl
  -- Injectivity, via Dedekind's independence of the Galois automorphisms.
  have hT_inj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro m hm
    rw [LinearMap.mem_ker] at hm
    have hm' : ∀ τ : Gal k k', ∑ σ, m σ * σ (c τ) = 0 := by
      intro τ; rw [← hT_apply m τ, hm, Pi.zero_apply]
    have hli : LinearIndependent k' (fun σ : Gal k k' => (σ : k' →ₗ[k] k')) :=
      ((linearIndependent_algHom_toLinearMap k k' k').comp
        (fun σ : Gal k k' => (σ : k' →ₐ[k] k')) AlgEquiv.coe_toAlgHom_injective)
    have hsum : ∑ σ : Gal k k', m σ • (σ : k' →ₗ[k] k') = 0 := by
      refine Module.Basis.ext c (fun τ => ?_)
      rw [LinearMap.sum_apply, LinearMap.zero_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact hm' τ
    funext σ
    exact (Fintype.linearIndependent_iff.mp hli m hsum) σ
  -- Consequently `T` is surjective, since source and target are the same finite-dimensional space.
  have hT_surj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hT_inj
  obtain ⟨m, hm⟩ := hT_surj (Pi.single τ₀ 1)
  refine ⟨m, ?_, ?_⟩
  · have h := congrFun hm τ₀
    rw [hT_apply, Pi.single_eq_same] at h
    exact h
  · intro τ hτ
    have h := congrFun hm τ
    rw [hT_apply, Pi.single_eq_of_ne hτ] at h
    exact h

end Work.Descent
