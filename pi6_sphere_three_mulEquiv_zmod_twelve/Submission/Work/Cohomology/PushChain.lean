import Mathlib
import Submission.Work.Cohomology.sdChainMap
import Submission.Work.Cohomology.Sd_comm

/-!
# Push-forward of singular chains along a continuous map, and its naturality

`Work.Cohomology.pushChain X Y f n` is the map induced on singular `n`-chains with `ℤ` coefficients
by a continuous map `f : X ⟶ Y`.  It is the degree-`n` component of the chain map
`SSet.chainComplexMap (TopCat.toSSet.map f)`.

The main point of this file is **naturality of the barycentric subdivision operator**:

`Sd Y n (pushChain X Y f n c) = pushChain X Y f n (Sd X n c)`  (`Sd_natural`),

i.e. `Sd` is a natural endomorphism of the singular chain complex.  An immediate corollary is that
the iterates `Sd^N` are natural as well, which is what lets one compute `Sd^N` on an arbitrary
singular simplex from `Sd^N` on the identity simplex of `Δⁿ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The push-forward of singular `n`-chains along a continuous map `f : X ⟶ Y`, as a morphism of
`ℤ`-modules. -/
def pushChainHom (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    (singularChains ℤ X).X n ⟶ (singularChains ℤ Y).X n :=
  (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f n

/-- The push-forward of singular `n`-chains along a continuous map `f : X ⟶ Y`, as a linear map. -/
def pushChain (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    (singularChains ℤ X).X n →ₗ[ℤ] (singularChains ℤ Y).X n :=
  (pushChainHom X Y f n).hom

/-- The push-forward of a generator. -/
theorem pushChain_gen (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    pushChain X Y f n (gen X n σ)
      = gen Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) σ) := by
  have h := chainComplexMap_ι_apply (TopCat.toSSet.map f) n σ (1 : ℤ)
  exact h

/-- The push-forward is functorial. -/
theorem pushChain_comp (X Y Z : TopCat) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (c : (singularChains ℤ X).X n) :
    pushChain Y Z g n (pushChain X Y f n c) = pushChain X Z (f ≫ g) n c :=
  chainComplexMap_toSSet_map_comp f g n c

/-- The continuous map underlying the singular simplex `(TopCat.toSSet.map f).app σ` is
`sdMap n σ ≫ f`. -/
theorem sdMap_map (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    sdMap n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) σ) = sdMap n σ ≫ f := by
  ext z
  exact toSSetObjEquiv_map_apply f (Opposite.op ⦋n⦌) σ z

/-- **Naturality of the barycentric subdivision operator.** -/
theorem Sd_natural (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) (c : (singularChains ℤ X).X n) :
    Sd Y n (pushChain X Y f n c) = pushChain X Y f n (Sd X n c) := by
  have key : ∀ τ : (TopCat.toSSet.obj X) _⦋n⦌,
      Sd Y n (pushChain X Y f n (gen X n τ)) = pushChain X Y f n (Sd X n (gen X n τ)) := by
    intro τ
    rw [pushChain_gen, Sd_gen, Sd_gen, sdElem_eq, sdElem_eq, pushChain, pushChainHom]
    rw [sdMap_map X Y f n τ]
    exact (chainComplexMap_toSSet_map_comp (sdMap n τ) f n (sdChain n)).symm
  have hmain : pushChainHom X Y f n ≫ sdHom Y n = sdHom X n ≫ pushChainHom X Y f n := by
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show (sdHom Y n).hom ((pushChainHom X Y f n).hom ((gen X n σ)))
      = (pushChainHom X Y f n).hom ((sdHom X n).hom (gen X n σ))
    exact key σ
  have h := congrArg (fun (g : (singularChains ℤ X).X n ⟶ (singularChains ℤ Y).X n) =>
    g.hom c) hmain
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, Sd, pushChain] using h

end

end Work.Cohomology
