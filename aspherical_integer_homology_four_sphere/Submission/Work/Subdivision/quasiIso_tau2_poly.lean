import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The middle map of a morphism of short exact sequences of complexes

If `φ : S₁ ⟶ S₂` is a morphism of short exact short complexes of homological
complexes in an abelian category `C`, and the maps `φ.τ₁` and `φ.τ₃` induced on
the outer terms are quasi-isomorphisms, then so is the middle map `φ.τ₂`.

This is the "two out of three" statement for the *middle* term, the companion of
`HomologicalComplex.HomologySequence.quasiIso_τ₃` in Mathlib (which treats the
case where `φ.τ₁` and `φ.τ₂` are quasi-isomorphisms).

The proof is a diagram chase along the long exact homology sequence.  For each
degree `i` we must show that `Hᵢ(φ.τ₂)` is an isomorphism.

* `Hᵢ(φ.τ₂)` is a monomorphism.  If `i` has no predecessor in the complex shape,
  this follows from the three-lemma applied to the exact sequence
  `Hᵢ(S.X₁) ⟶ Hᵢ(S.X₂) ⟶ Hᵢ(S.X₃)`, using `Mono S₂.f`.  Otherwise, with
  `k` such that `c.Rel k i`, it follows from the four-lemma applied to
  `H_k(S.X₃) ⟶ Hᵢ(S.X₁) ⟶ Hᵢ(S.X₂) ⟶ Hᵢ(S.X₃)`, the last four terms of the
  homology sequence at `(k, i)`.

* `Hᵢ(φ.τ₂)` is an epimorphism.  If `i` has no successor, this follows from the
  dual three-lemma applied to `Hᵢ(S.X₁) ⟶ Hᵢ(S.X₂) ⟶ Hᵢ(S.X₃)`, using
  `Epi S₁.g`.  Otherwise, with `j` such that `c.Rel i j`, it follows from the
  four-lemma applied to `Hᵢ(S.X₁) ⟶ Hᵢ(S.X₂) ⟶ Hᵢ(S.X₃) ⟶ Hⱼ(S.X₁)`, the
  first four terms of the homology sequence at `(i, j)`.
-/

namespace Work.Subdivision

open CategoryTheory
open HomologicalComplex

theorem quasiIso_tau2_poly {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S₁ S₂ : CategoryTheory.ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  have hφ₁e : ∀ k, Epi (homologyMap φ.τ₁ k) := fun k => by
    have := h₁.quasiIsoAt k
    infer_instance
  have hφ₁m : ∀ k, Mono (homologyMap φ.τ₁ k) := fun k => by
    have := h₁.quasiIsoAt k
    infer_instance
  have hφ₃e : ∀ k, Epi (homologyMap φ.τ₃ k) := fun k => by
    have := h₃.quasiIsoAt k
    infer_instance
  have hφ₃m : ∀ k, Mono (homologyMap φ.τ₃ k) := fun k => by
    have := h₃.quasiIsoAt k
    infer_instance
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (homologyMap φ.τ₂ i) := by
    by_cases hk : ∃ k, c.Rel k i
    · obtain ⟨k, hki⟩ := hk
      refine Abelian.mono_of_epi_of_mono_of_mono
        ((ComposableArrows.δ₀Functor ⋙ ComposableArrows.δ₀Functor).map
          (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ k i hki))
        ?_ ?_ ?_ ?_ ?_
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ k i hki).δ₀.δ₀
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ k i hki).δ₀.δ₀
      · exact hφ₃e k
      · exact hφ₁m i
      · exact hφ₃m i
    · refine Abelian.mono_of_mono_of_mono_of_mono
        (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i)
        (HomologicalComplex.HomologySequence.composableArrows₂_exact hS₁ i) ?_ ?_ ?_
      · have : Mono S₂.f := hS₂.mono_f
        have : Mono ((S₂.f).f i) :=
          (inferInstance : Mono ((HomologicalComplex.eval C c i).map S₂.f))
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S₂.f i
          (fun k hk' => hk ⟨k, hk'⟩)
      · exact hφ₁m i
      · exact hφ₃m i
  have hepi : Epi (homologyMap φ.τ₂ i) := by
    by_cases hj : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hj
      refine Abelian.epi_of_epi_of_epi_of_mono
        ((ComposableArrows.δlastFunctor ⋙ ComposableArrows.δlastFunctor).map
          (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i j hij))
        ?_ ?_ ?_ ?_ ?_
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ i j hij).δlast.δlast
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ i j hij).δlast.δlast
      · exact hφ₁e i
      · exact hφ₃e i
      · exact hφ₁m j
    · refine Abelian.epi_of_epi_of_epi_of_epi
        (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i)
        (HomologicalComplex.HomologySequence.composableArrows₂_exact hS₂ i) ?_ ?_ ?_
      · have : Epi S₁.g := hS₁.epi_g
        have : Epi ((S₁.g).f i) :=
          (inferInstance : Epi ((HomologicalComplex.eval C c i).map S₁.g))
        exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S₁.g i
          (fun j hj' => hj ⟨j, hj'⟩)
      · exact hφ₁e i
      · exact hφ₃e i
  exact isIso_of_mono_of_epi _

end Work.Subdivision
