import Mathlib
import Submission.Work.Descent.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.Descent

/-- Dedekind's independence of characters, scalar case: a `k'`-linear combination of the Galois
automorphisms `σ` that vanishes on all of `k'` is trivial.  (This is Dedekind's lemma for the
multiplicative characters `σ : k' →* k'`, which Mathlib has as
`linearIndependent_algHom_toLinearMap`.) -/
lemma dedekind_field {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (c : Gal k k' → k')
    (h : ∀ x : k', ∑ σ : Gal k k', σ x * c σ = 0) : c = 0 := by
  have hli := linearIndependent_algHom_toLinearMap k k' k'
  have hli' : LinearIndependent k' (fun σ : Gal k k' => AlgHom.toLinearMap (σ : k' →ₐ[k] k')) :=
    hli.comp (fun σ : Gal k k' => (σ : k' →ₐ[k] k')) (fun σ τ hστ => AlgEquiv.ext (fun x => by
      have := DFunLike.congr_fun hστ x
      simpa using this))
  have hsum : ∑ σ : Gal k k', c σ • (AlgHom.toLinearMap (σ : k' →ₐ[k] k')) = 0 := by
    ext x
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    rw [show (∑ σ : Gal k k', (c σ • (AlgHom.toLinearMap (σ : k' →ₐ[k] k'))) x)
        = ∑ σ : Gal k k', σ x * c σ from ?_]
    · exact h x
    · refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [LinearMap.smul_apply, smul_eq_mul, mul_comm]
      rfl
  funext σ
  exact Fintype.linearIndependent_iff.mp hli' c hsum σ

/-- Dedekind's independence of characters with coefficients in a `k'`-module: if a `k'`-linear
combination of the Galois automorphisms vanishes on all of `k'`, then it is trivial. -/
theorem dedekind_module {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [IsGalois k k'] {V : Type u} [AddCommGroup V] [Module k' V] (w : Work.Descent.Gal k k' → V)
    (h : ∀ x : k', ∑ σ : Work.Descent.Gal k k', σ x • w σ = 0) : w = 0 := by
  by_contra hw
  -- some coefficient of `w` is nonzero
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ : Gal k k', w σ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw (funext hc)
  -- separate that nonzero value from `0` by a `k'`-linear functional, and reduce to scalars
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero k' hσ₀
  refine hf ?_
  have hc : ∀ x : k', ∑ σ : Gal k k', σ x * f (w σ) = 0 := by
    intro x
    have := congrArg f (h x)
    simpa using this
  have hzero : (fun σ : Gal k k' => f (w σ)) = 0 := dedekind_field _ hc
  exact congrFun hzero σ₀

end Work.Descent
