import Mathlib
import Submission.Work.PieceHomology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Transport of a `HomModel` along a homotopy equivalence

A `HomModel X r` is the data of a chain complex `C`, a quasi-isomorphism `q : C ⟶ C_*(X; ℤ)`
and an identification `H_k(C) ≅ ℤ^{r k}`.  Homotopy invariance of singular homology (Mathlib's
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`) says that the singular chain
complex functor sends homotopic maps to maps inducing the same map on homology; consequently the
chain map induced by a homotopy equivalence is a quasi-isomorphism.

Here we record the consequence used by the Mayer–Vietoris assembly: a model of `Y` transports to a
model of `X` along any homotopy equivalence `X ≃ₕ Y`, by composing the comparison chain map with
the chain map induced by the inverse homotopy equivalence (in the direction `C_*(Y) ⟶ C_*(X)`).

The only formal care needed is that the singular chain complex is *definitionally* the value on
`TopCat` of a functor; we expose this as the reducible abbreviation `singCxFunctor` below, so that
the induced chain maps and their `QuasiIso` instances are recognised up to defeq by the elaborator.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology HomologicalComplex

namespace Work.PieceHomology

noncomputable section

/-- The functor `X ↦ C_*(X; ℤ)` of singular chains with `ℤ` coefficients, i.e. the object part of
`Work.HomologyMV.singCx` upgraded to a functor.  It is a reducible abbreviation so that
`singCxFunctor.obj X` and `Work.HomologyMV.singCx X` are interchangeable definitionally. -/
noncomputable abbrev singCxFunctor : TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- Two homotopic maps of `TopCat` induce the same map on singular homology: the underlying
homotopy-invariance statement in the form of an equality of `homologyMap`s. -/
lemma homologyMap_eq_of_homotopic {X Y : TopCat} {f g : X ⟶ Y}
    (h : (TopCat.Hom.hom f).Homotopic (TopCat.Hom.hom g)) (n : ℕ) :
    homologyMap (singCxFunctor.map f) n = homologyMap (singCxFunctor.map g) n := by
  obtain ⟨H⟩ := h
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H (ModuleCat.of ℤ ℤ) n

/-- **The chain map induced by the inverse of a homotopy equivalence is a quasi-isomorphism.**
It is invertible on homology, with inverse the map induced by the forward direction, because the
two composites are homotopic to the identities. -/
theorem quasiIso_singCxFunctor_map_symm {X Y : TopCat} (e : ContinuousMap.HomotopyEquiv X Y) :
    QuasiIso (singCxFunctor.map (TopCat.ofHom e.invFun)) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hleft : homologyMap (singCxFunctor.map (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun)) k
      = 𝟙 ((singCxFunctor.obj X).homology k) := by
    have hh : (TopCat.Hom.hom (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun)).Homotopic
        (TopCat.Hom.hom (𝟙 X)) := by
      simpa [TopCat.hom_comp] using e.left_inv
    simpa using homologyMap_eq_of_homotopic hh k
  have hright : homologyMap (singCxFunctor.map (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun)) k
      = 𝟙 ((singCxFunctor.obj Y).homology k) := by
    have hh : (TopCat.Hom.hom (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun)).Homotopic
        (TopCat.Hom.hom (𝟙 Y)) := by
      simpa [TopCat.hom_comp] using e.right_inv
    simpa using homologyMap_eq_of_homotopic hh k
  refine IsIso.mk ⟨homologyMap (singCxFunctor.map (TopCat.ofHom e.toFun)) k, ?_, ?_⟩
  · rw [← homologyMap_comp, ← Functor.map_comp]
    exact hright
  · rw [← homologyMap_comp, ← Functor.map_comp]
    exact hleft

/-- **A model of `Y` transports to a model of `X` along a homotopy equivalence.**
The underlying complex and the rank identification are unchanged; the comparison chain map
`C ⟶ C_*(X)` is `q` followed by the (quasi-)isomorphism `C_*(Y) ⟶ C_*(X)` induced by the inverse
homotopy equivalence. -/
theorem HomModel_ofHomotopyEquiv {X Y : TopCat} {r : ℤ → ℕ}
    (M : Work.PieceHomology.HomModel Y r) (e : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (Work.PieceHomology.HomModel X r) := by
  haveI : QuasiIso M.q := M.hq
  haveI : QuasiIso (singCxFunctor.map (TopCat.ofHom e.invFun)) :=
    quasiIso_singCxFunctor_map_symm e
  exact ⟨{ C := M.C
           q := M.q ≫ singCxFunctor.map (TopCat.ofHom e.invFun)
           hq := inferInstance
           e := M.e }⟩

end

end Work.PieceHomology
