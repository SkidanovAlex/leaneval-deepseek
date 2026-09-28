import Mathlib
import Submission.Work.Kunneth.ctensAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Flatness of `T q` and the `(p,q)`-Künneth summand

For a cochain complex `A` of `ℤ`-modules and a family `T` of `ℤ`-modules, the `(p,q)`-summand of
the cohomological Künneth computation is the statement that the homology of the complex
`A^• ⊗ T q` in degree `p` is `H^p(A) ⊗ T q`, at least as soon as `T q` is flat over `ℤ`
(equivalently, torsion free).

The file proves this as `Work.Kunneth.flatKerQuotRange`:

* `kerQuotTens A T p q` is the concrete `ker (∂ ⊗ 1) ⧸ im (∂ ⊗ 1)` of the two-term piece
  `A^{p-1} ⊗ T q ⟶ A^p ⊗ T q ⟶ A^{p+1} ⊗ T q`;
* `homologyTensor A T p q = H^p(A) ⊗ T q`.

The two auxiliary lemmas in `Work.Kunneth.FlatKerQuot` identify the homology of a short complex
of `ℤ`-modules with the concrete quotient of the cycles by the boundaries, for which Mathlib only
provides the abstract `ShortComplex.moduleCatHomologyIso` together with the auxiliary
`ShortComplex.moduleCatToCycles`.

The proof then uses that `tensorRight (T q)` preserves homology (`Module.Flat.rTensor_shortComplex_exact`
plus the general `Functor.PreservesHomology` machinery) and the canonical comparison
`HomologicalComplex.homologyFunctorIso'` between the homology of a complex and that of its
three-term piece.

As everywhere in this chapter, the generic `AddCommGroup.toIntModule` instance is removed so that
the `ℤ`-module structures occurring in the tensor products are those of the `ModuleCat` objects at
hand.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct
open MonoidalCategory

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

namespace FlatKerQuot

/-- The range of `ShortComplex.moduleCatToCycles` is the preimage in `ker S.g` of the range of
`S.f`. -/
lemma range_moduleCatToCycles (S : ShortComplex (ModuleCat ℤ)) :
    LinearMap.range S.moduleCatToCycles =
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype := by
  simp only [ShortComplex.moduleCatToCycles]
  exact LinearMap.range_codRestrict _ _ _

/-- The homology of a short complex of `ℤ`-modules is the quotient of the kernel of `S.g` by the
preimage of the image of `S.f`. -/
lemma moduleCatHomologyIsoKerQuot (S : ShortComplex (ModuleCat ℤ)) :
    Nonempty (S.homology ≅ ModuleCat.of ℤ (LinearMap.ker S.g.hom ⧸
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype)) := by
  have h1 := range_moduleCatToCycles S
  refine ⟨S.moduleCatHomologyIso.trans ?_⟩
  rw [show S.moduleCatLeftHomologyData.H = ModuleCat.of ℤ (LinearMap.ker S.g.hom ⧸
      LinearMap.range S.moduleCatToCycles) from rfl]
  rw [h1]

/-- The predecessor of `p` in the cochain shape `ComplexShape.up ℕ`. -/
lemma prev_up (p : ℕ) : (ComplexShape.up ℕ).prev p = p - 1 := by
  rcases p with _ | k
  · refine ComplexShape.prev_eq_self' (ComplexShape.up ℕ) 0 ?_
    intro i hi
    simp [ComplexShape.up, ComplexShape.up'] at hi
  · rw [ComplexShape.prev_eq' (ComplexShape.up ℕ) (ComplexShape.up_mk k (k + 1) rfl)]
    rfl

/-- The successor of `p` in the cochain shape `ComplexShape.up ℕ`. -/
lemma next_up (p : ℕ) : (ComplexShape.up ℕ).next p = p + 1 :=
  ComplexShape.next_eq' (ComplexShape.up ℕ) (ComplexShape.up_mk p (p + 1) rfl)

end FlatKerQuot

/-- **The `(p,q)`-Künneth summand for flat coefficients**: if `T q` is flat over `ℤ`, then
`ker (∂ ⊗ 1) ⧸ im (∂ ⊗ 1)` in degree `p` of the complex `A^• ⊗ T q` is `H^p(A) ⊗ T q`. -/
theorem flatKerQuotRange (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ)
    (q p : ℕ) (hT : Module.Flat ℤ ↥(T q)) :
    Nonempty (CategoryTheory.Iso (kerQuotTens A T p q) (homologyTensor A T p q)) := by
  have e1 : A.homology p ≅ (A.sc' (p - 1) p (p + 1)).homology :=
    (homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.up ℕ) (p - 1) p (p + 1)
      (FlatKerQuot.prev_up p) (FlatKerQuot.next_up p)).app A
  have e2 : homologyTensor A T p q ≅ (A.sc' (p - 1) p (p + 1)).homology ⊗ T q :=
    (tensorRight (T q)).mapIso e1
  have e3 : (A.sc' (p - 1) p (p + 1)).homology ⊗ T q ≅
      ((A.sc' (p - 1) p (p + 1)).map (tensorRight (T q))).homology :=
    (ShortComplex.mapHomologyIso (A.sc' (p - 1) p (p + 1)) (tensorRight (T q))).symm
  have e4 : ((A.sc' (p - 1) p (p + 1)).map (tensorRight (T q))).homology ≅
      kerQuotTens A T p q :=
    (FlatKerQuot.moduleCatHomologyIsoKerQuot _).some
  exact ⟨(e2.trans e3 |>.trans e4).symm⟩

end

end Work.Kunneth
