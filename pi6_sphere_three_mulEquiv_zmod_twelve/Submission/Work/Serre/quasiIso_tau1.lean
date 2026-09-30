import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.Serre

open CategoryTheory HomologicalComplex ComposableArrows CategoryTheory.Limits

/-- A morphism of short exact sequences of cochain complexes which is a quasi-isomorphism
on the middle and third terms is a quasi-isomorphism on the first term.

This is the `τ₁`-version of Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃`; it
follows from the long exact sequence in homology (five lemma), the only point needing care
being the lowest degree, where there is no incoming connecting map and one uses instead that
`H_0` of the two short exact complexes is a subobject of `H_0` of their middle terms. -/
theorem quasiIso_tau1 {R : Type} [CommRing R]
    {S₁ S₂ : ShortComplex (CochainComplex (ModuleCat R) ℕ)}
    (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₁ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : ∃ k, (ComplexShape.up ℕ).Rel k i
  · -- there is a predecessor: use the five term exact sequence in degrees `k` and `i`
    obtain ⟨k, hk⟩ := hi
    refine Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
      (ComposableArrows.Exact.δ₀ (HomologySequence.composableArrows₅_exact hS₁ k i hk))
      (ComposableArrows.Exact.δ₀ (HomologySequence.composableArrows₅_exact hS₂ k i hk))
      (ComposableArrows.δ₀Functor.map (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ k i hk))
      ?_ ?_ ?_ ?_
    · show Epi (homologyMap φ.τ₂ k); infer_instance
    · show IsIso (homologyMap φ.τ₃ k); infer_instance
    · show IsIso (homologyMap φ.τ₂ i); infer_instance
    · show Mono (homologyMap φ.τ₃ i); infer_instance
  · -- no predecessor: `H_i` is a subobject of `H_i` of the middle terms
    have hmono : Mono (homologyMap φ.τ₁ i) := by
      haveI : Mono S₁.f := hS₁.mono_f
      have hm₁ : Mono (homologyMap S₁.f i) :=
        HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S₁.f i (fun j hj => hi ⟨j, hj⟩)
      apply Preadditive.mono_of_cancel_zero
      intro Z g hg
      have hnat : homologyMap φ.τ₁ i ≫ homologyMap S₂.f i =
          homologyMap S₁.f i ≫ homologyMap φ.τ₂ i := by
        simp only [← homologyMap_comp, φ.comm₁₂]
      have h1 : (g ≫ homologyMap S₁.f i) ≫ homologyMap φ.τ₂ i = 0 := by
        rw [Category.assoc, ← hnat, ← Category.assoc, hg, zero_comp]
      have h2 : g ≫ homologyMap S₁.f i = 0 :=
        (cancel_mono (homologyMap φ.τ₂ i)).1 (by rw [zero_comp]; exact h1)
      exact (cancel_mono (homologyMap S₁.f i)).1 (by rw [zero_comp]; exact h2)
    have hepi : Epi (homologyMap φ.τ₁ i) := by
      haveI : Mono S₂.f := hS₂.mono_f
      have hm₂ : Mono (homologyMap S₂.f i) :=
        HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S₂.f i (fun j hj => hi ⟨j, hj⟩)
      refine Abelian.epi_of_mono_of_epi_of_mono (HomologySequence.mapComposableArrows₂ φ i)
        (HomologySequence.composableArrows₂_exact hS₁ i)
        (HomologySequence.composableArrows₂_exact hS₂ i) hm₂ ?_ ?_
      · show Epi (homologyMap φ.τ₂ i); infer_instance
      · show Mono (homologyMap φ.τ₃ i); infer_instance
    exact isIso_of_mono_of_epi (homologyMap φ.τ₁ i)

end Work.Serre
