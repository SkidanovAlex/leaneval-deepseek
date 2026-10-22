import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.BFun.Prelim

namespace Work.CWIND.BFun

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

open scoped Simplicial

/-!
# CWIND/T1: the comparison map `b : C_sing(X) ⟶ A(X)`

This file proves `Work.CWIND.BFun.exists_bNat`: the existence of the natural transformation of
cochain complexes `b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor` whose level-`n`
component (in cohomological degree `-n`) is `bLevel X n`, transported along the canonical
extension isomorphisms `CXIso` and `AXIso`.

The mathematical content (the compatibility of the levelwise maps `bLevel X n` with the simplicial
structure maps and their naturality in `X`) is established in
`Submission/Work/CWIND/BFun/Prelim.lean`: the crucial point is the compatibility of the canonical
generators `theGen X n x`.
-/

/-- The `ℕ`-graded chain complex of singular chains with discrete coefficients, functorially in the
space (the source of the levelwise comparison maps `bLevel`). -/
noncomputable abbrev CsrcFunctor : TopCat.{0} ⥤ ChainComplex LightCondAb ℕ :=
  Submission.Blueprint.singC ⋙ (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex
    (ComplexShape.down ℕ)

section

set_option backward.isDefEq.respectTransparency false

/-- The comparison map of chain complexes `C_sing(X) ⟶ A(X)` obtained from the levelwise maps
`bLevel X n`. -/
noncomputable def bChain (X : TopCat.{0}) : Csrc X ⟶ Achain X where
  f n := bLevel X n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    exact bLevel_comm X j

/-- The comparison map of chain complexes `C_sing(X) ⟶ A(X)`, natural in the space. -/
noncomputable def bChainNat : CsrcFunctor ⟶ AchainFunctor where
  app X := bChain X
  naturality {X Y} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact bLevel_naturality X Y f n

/-- The comparison map `b` of cochain complexes, obtained from the comparison map of chain
complexes by extension by zero in positive degrees. -/
noncomputable def bNat : singularChainsLightCondAbComplexFunctor ⟶ AFunctor :=
  Functor.whiskerRight bChainNat (ComplexShape.embeddingDownNat.extendFunctor LightCondAb)

/-- **CWIND/T1. The comparison map `b`.**  Build the natural transformation of cochain complexes
`b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor`, where
`singularChainsLightCondAbComplexFunctor X` is the integral singular chain complex of `X` with
discrete coefficients (homological degree `n` placed in cohomological degree `-n`), and
`A(X) = extend (alternatingFaceMapComplex (n ↦ ℤ[X^{Δⁿ}]))` is the mapping-space complex defined in
`Submission/Work/CWIND/Basic.lean`.  The level-`n` component of `b` must be `bLevel X n`, the map
`ℤ[Singₙ X] ⟶ ℤ[X^{Δⁿ}]` induced by the identity from the discrete topology on the set of singular
`n`-simplices (each singular `n`-simplex is a point of the compact-open mapping space `X^{Δⁿ}`);
`bLevel` is defined in `Basic.lean` as the transpose under `discrete ⊣ underlying` of the coproduct
map whose `x`-component classifies the element of `Γ(ℤ[X^{Δⁿ}])` given by the unit of `free ⊣ forget`
at the point `x`.

The conclusion pins `b` down completely: a morphism out of a complex concentrated in degrees `≤ 0`
is determined by all its components, which are prescribed by `bLevel` transported along the canonical
`extend` isomorphisms `CXIso` and `AXIso`.  The mathematical content is that the levelwise maps
`bLevel X n` are compatible with the simplicial face maps of `Sing X` and of `n ↦ X^{Δⁿ}` (so that
they assemble into a morphism of simplicial objects, hence a morphism of complexes) and natural
in `X`. -/
theorem exists_bNat :
    ∃ (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor),
      (∀ (X : TopCat.{0}) (n : ℕ),
        (b.app X).f (-(n : ℤ)) = (CXIso X n).inv ≫ bLevel X n ≫ (AXIso X n).inv) := by
  refine ⟨bNat, fun X n => ?_⟩
  have hcomp : (bNat.app X).f (-(n : ℤ)) =
      (HomologicalComplex.extendMap (bChain X) ComplexShape.embeddingDownNat).f (-(n : ℤ)) := rfl
  rw [hcomp]
  exact (HomologicalComplex.extendMap_f (φ := bChain X) (e := ComplexShape.embeddingDownNat)
    (i := n) (i' := -(n : ℤ)) (h := by simp)).trans (by rfl)

end

end Work.CWIND.BFun
