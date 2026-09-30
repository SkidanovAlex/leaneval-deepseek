import Mathlib
import Submission.Work.Cohomology.relCochain_shortExact

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The long exact sequence of a pair (singular cohomology)

For a topological space `X` and a subset `A ⊆ X`, the relative cochains `C^*(X,A)` are the kernel of
the restriction `C^*(X) ⟶ C^*(A)` (`relComplex`, `relIncl` in
`Submission/Work/Cohomology/relCochain_shortExact.lean`), and

`0 ⟶ C^*(X,A) ⟶ C^*(X) ⟶ C^*(A) ⟶ 0`

is a short exact sequence of cochain complexes (`relCochain_shortExact` proves this degreewise, i.e.
injectivity, surjectivity and `range = ker`).  This file packages it as a `ShortComplex` and proves
that it is short exact, which by the homology sequence gives the long exact sequence of the pair:

`⋯ ⟶ Hⁿ(X,A) ⟶ Hⁿ(X) ⟶ Hⁿ(A) ⟶ Hⁿ⁺¹(X,A) ⟶ ⋯`

## Main results

* `relIncl_comp_restr`, `pairShort` — the short complex of the pair;
* `pairShort_shortExact` — it is short exact;
* `pairδ`, `pairδ_comp`, `pair_comp_δ` — the connecting homomorphism;
* `pair_exact₁`, `pair_exact₂`, `pair_exact₃` — exactness at the three terms.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The composite of the inclusion of the relative cochains and the restriction is zero. -/
theorem relIncl_comp_restr (X : TopCat) (A : Set X) :
    CategoryTheory.CategoryStruct.comp (relIncl R X A) (restr R X A) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, HomologicalComplex.zero_f_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply]
  change ((restr R X A).f n).hom x.1 = 0
  exact x.2

/-- **The short complex of the pair `(X,A)`**: `0 ⟶ C^*(X,A) ⟶ C^*(X) ⟶ C^*(A) ⟶ 0`. -/
def pairShort (X : TopCat) (A : Set X) : ShortComplex (CochainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (relIncl R X A) (restr R X A) (relIncl_comp_restr R X A)

/-- **The short complex of a pair is short exact.** -/
theorem pairShort_shortExact (X : TopCat) (A : Set X) :
    (pairShort R X A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, ShortComplex.map_f, ShortComplex.map_g,
      HomologicalComplex.eval_map, HomologicalComplex.eval_map]
    simp only [pairShort, relIncl_f, ModuleCat.hom_ofHom]
    exact Submodule.range_subtype (relKern R X A n)
  · rw [ModuleCat.mono_iff_injective, ShortComplex.map_f, HomologicalComplex.eval_map]
    simp only [pairShort, relIncl_f, ModuleCat.hom_ofHom]
    intro a b h
    exact Subtype.ext h
  · rw [ModuleCat.epi_iff_surjective, ShortComplex.map_g, HomologicalComplex.eval_map]
    exact surjective_restr R X A n

/-- The connecting homomorphism `Hⁿ(A) ⟶ Hⁿ⁺¹(X,A)` of the long exact sequence of the pair. -/
def pairδ (X : TopCat) (A : Set X) (n : ℕ) :
    (singularCochainComplex R (TopCat.of A)).homology n ⟶ (relComplex R X A).homology (n + 1) :=
  (pairShort_shortExact R X A).δ n (n + 1) (by simp [ComplexShape.up])

/-- The connecting homomorphism followed by the map to `Hⁿ⁺¹(X)` is zero. -/
theorem pairδ_comp (X : TopCat) (A : Set X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (pairδ R X A n)
      (HomologicalComplex.homologyMap (relIncl R X A) (n + 1)) = 0 :=
  (pairShort_shortExact R X A).δ_comp n (n + 1) (by simp [ComplexShape.up])

/-- The restriction `Hⁿ(X) ⟶ Hⁿ(A)` followed by the connecting homomorphism is zero. -/
theorem pair_comp_δ (X : TopCat) (A : Set X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (restr R X A) n)
      (pairδ R X A n) = 0 :=
  (pairShort_shortExact R X A).comp_δ n (n + 1) (by simp [ComplexShape.up])

/-- Exactness of the long exact sequence of the pair at `Hⁿ⁺¹(X,A)`. -/
theorem pair_exact₁ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (pairδ R X A n)
      (HomologicalComplex.homologyMap (relIncl R X A) (n + 1))
      (pairδ_comp R X A n)).Exact :=
  (pairShort_shortExact R X A).homology_exact₁ n (n + 1) (by simp [ComplexShape.up])

/-- Exactness of the long exact sequence of the pair at `Hⁿ(X)`. -/
theorem pair_exact₂ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relIncl R X A) n)
      (HomologicalComplex.homologyMap (restr R X A) n)
      (by rw [← HomologicalComplex.homologyMap_comp, relIncl_comp_restr,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (pairShort_shortExact R X A).homology_exact₂ n

/-- Exactness of the long exact sequence of the pair at `Hⁿ(A)`. -/
theorem pair_exact₃ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (restr R X A) n) (pairδ R X A n)
      (pair_comp_δ R X A n)).Exact :=
  (pairShort_shortExact R X A).homology_exact₃ n (n + 1) (by simp [ComplexShape.up])

end

end Work.Cohomology
