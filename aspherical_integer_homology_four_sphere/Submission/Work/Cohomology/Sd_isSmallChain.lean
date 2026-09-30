import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.SdIter
import Submission.Work.Cohomology.PushChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision of a small chain is small

The small chains `C^{U,V}_*(X)` of a cover `X = U ∪ V` are the chains spanned by the singular
simplices whose image lies in `U` or in `V` (`Submission/Work/Cohomology/SmallChains.lean`).  The
point of the barycentric subdivision is that it *refines*: subdividing a simplex that lies in `U`
produces a sum of simplices that still lie in `U`.  Consequently the subdivision operator `Sd`
preserves the small chains, which is the statement proved here.

## The proof

The technical core is the following descent principle (`isSmallChain_of_gen`): an element of a
simplicial chain module is determined by its values on the generators `genSSet Y n y`, so a linear
map `T : C_n(Y) ⟶ C_n(X)` takes values in the small chains as soon as it does so on every
generator; this is formalised by composing with the quotient projection onto
`C_n(X) / C^{U,V}_n(X)` and applying `SSet.chainComplex_hom_ext`.

From it we obtain

* `pushChain_isSmallChain`: pushing *any* chain forward along a continuous map `f` whose image is
  contained in `U` (or in `V`) produces a small chain — the pushforward of a generator is the
  generator of a simplex whose image is contained in the image of `f`
  (`sdMap_map`: `sdMap n (f.app σ) = sdMap n σ ≫ f`);
* `isSmallChain_sdElem`: hence `sdElem X n σ = pushChain (sdMap n σ) (sdChain n)` is small for a
  small `σ`;
* `smallToSing_gen`: the inclusion of the small chains sends the generator of a small simplex to
  the generator of the same simplex in the singular chains.

The theorem follows by applying the descent principle to `smallToSing ≫ sdHom` on the small
simplicial set: on a generator — a small simplex `σ'` — it evaluates to
`Sd X n (gen X n σ'.1) = sdElem X n σ'.1`, which is small by `isSmallChain_sdElem`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat} {U V : Set X}

/-- **Descent principle for small chains.**  A morphism `T` from the `n`-chains of a simplicial set
`Y` to the singular `n`-chains of `X` takes values in the small chains as soon as it does so on the
generators `genSSet Y n y`. -/
theorem isSmallChain_of_gen {Y : SSet} {n : ℕ}
    (T : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶ (singularChains ℤ X).X n)
    (h : ∀ y : Y _⦋n⦌, IsSmallChain U V (T.hom (genSSet Y n y))) :
    ∀ c, IsSmallChain U V (T.hom c) := by
  intro c
  let S : Submodule ℤ ↥((singularChains ℤ X).X n) := smallChainSubmodule U V n
  letI : Module ℤ (↥((singularChains ℤ X).X n) ⧸ S) := Submodule.Quotient.module S
  let q : (singularChains ℤ X).X n ⟶ ModuleCat.of ℤ (↥((singularChains ℤ X).X n) ⧸ S) :=
    ModuleCat.ofHom (Submodule.mkQ S)
  have hg : T ≫ q = 0 := by
    apply SSet.chainComplex_hom_ext (X := Y) (R := ModuleCat.of ℤ ℤ)
    intro y
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
      LinearMap.zero_apply]
    show Submodule.Quotient.mk ((ModuleCat.Hom.hom T) (genSSet Y n y)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact h y
  have hc : ((ModuleCat.Hom.hom T) c) ∈ S := by
    have h2 : (ModuleCat.Hom.hom (T ≫ q)) c = 0 := by
      rw [hg, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    have h3 : ModuleCat.Hom.hom q = Submodule.mkQ S := rfl
    rw [h3, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  exact hc

/-- Pushing a chain forward along a continuous map whose image lies in `U` (or in `V`) yields a
small chain. -/
theorem pushChain_isSmallChain {A : TopCat} (f : A ⟶ X) {n : ℕ}
    (hf : Set.range f ⊆ U ∨ Set.range f ⊆ V) (c : (singularChains ℤ A).X n) :
    IsSmallChain U V (pushChain A X f n c) := by
  refine isSmallChain_of_gen (Y := TopCat.toSSet.obj A) (n := n) (pushChainHom A X f n) ?_ c
  intro σ
  show IsSmallChain U V (pushChain A X f n (gen A n σ))
  rw [pushChain_gen]
  apply isSmallChain_gen
  rw [isSmall_iff]
  have h1 : Set.range (fun z : (Delta n : TopCat) =>
      sdMap n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) σ) z) ⊆ Set.range (f : A → X) := by
    rw [sdMap_map A X f n σ]
    rintro y ⟨z, rfl⟩
    exact ⟨sdMap n σ z, rfl⟩
  rcases hf with hf | hf
  · exact Or.inl (h1.trans hf)
  · exact Or.inr (h1.trans hf)

/-- The subdivision of a small simplex is a small chain. -/
theorem isSmallChain_sdElem {n : ℕ} {σ : Simplex X n} (hσ : IsSmall U V σ) :
    IsSmallChain U V (sdElem X n σ) := by
  have h := pushChain_isSmallChain (X := X) (U := U) (V := V) (A := Delta n) (f := sdMap n σ)
    (n := n) ((isSmall_iff σ).mp hσ) (sdChain n)
  rw [pushChain, pushChainHom] at h
  rw [sdElem_eq]
  exact h

/-- The inclusion of the small chains into the singular chains sends the generator of a small
simplex to the generator of the same simplex. -/
theorem smallToSing_gen {n : ℕ} (σ' : (smallSSet U V) _⦋n⦌) :
    (smallToSing U V).f n (genSSet (smallSSet U V) n σ') = gen X n σ'.1 := by
  have h := chainComplexMap_ι_apply (smallSubcomplex U V).ι n σ' (1 : ℤ)
  have h2 : (smallSubcomplex U V).ι.app (Opposite.op ⦋n⦌) σ' = σ'.1 := rfl
  rw [h2] at h
  exact h

theorem Sd_isSmallChain {X : TopCat} (U V : Set X) {n : ℕ}
    {c : (singularChains ℤ X).X n} (hc : IsSmallChain U V c) :
    IsSmallChain U V (Sd X n c) := by
  obtain ⟨a, ha⟩ := hc
  rw [← ha]
  change IsSmallChain U V (((smallToSing U V).f n ≫ sdHom X n).hom a)
  apply isSmallChain_of_gen (Y := smallSSet U V) (n := n) ((smallToSing U V).f n ≫ sdHom X n) _ a
  intro σ'
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, smallToSing_gen]
  rw [show (sdHom X n).hom (gen X n σ'.1) = Sd X n (gen X n σ'.1) from rfl, Sd_gen]
  exact isSmallChain_sdElem σ'.2

end

end Work.Cohomology
