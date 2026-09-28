import Mathlib
import Submission.Work.Cohomology.pd_union_aux
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.mem_range_incl_of_smallOfV_eq

/-!
# The support of a chain, and the preimage of the chains of a subspace

Let `X` be a topological space and `A, V ⊆ X` two subsets, with `V ∩ A = relSubset A V`.
The singular chains of a subspace are free on the singular simplices, so a chain `x` of `V` has a
well defined **support**: the set of simplices of `V` occurring with a nonzero coefficient in `x`.
The content of this file is that the support is visible on the image in `X`: if the image of `x` in
`C_*(X)` is the image of a chain `y` of `A`, then every simplex in the support of `x` has its image
in `X` contained in `A`, so that `x` comes from a chain of `V ∩ A`.

The proof uses the retraction `chainRetract ℤ X V n` of the inclusion of the chains of `V` in the
chains of `X` (a singular simplex of `X` is sent back to the simplex of `V` it comes from, and to
`0` otherwise).  Rewriting `x` with this retraction turns the statement into an elementwise
statement about the map `C_*(A) → C_*(V)`, `y ↦ (chainRetract ℤ X V n) ((inclChains X A) y)`, which
is then checked on the generators of `C_*(A)`: a generator is sent either to `0` or to a generator
of a simplex of `V` whose image in `X` is the image of a simplex of `A`, hence lies in
`relSubset A V`.

## Main results

* `mem_range_inclChains_of_image_aux` — the general support statement;
* `mem_range_inclChains_of_image` — its form used for the gluing square
  (`W ⊆ M`, `S ⊆ M`, `pdTr W S = W ∩ S`).
-/

open Classical

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **Support transfer.**  If a chain `x` of `V` and a chain `y` of `A` have the same image in the
singular chains of `X`, then `x` is the image of a chain of `V ∩ A`. -/
theorem mem_range_inclChains_of_image_aux {X : TopCat} (A V : Set X) (n : ℕ)
    {x : (singularChains ℤ (TopCat.of V)).X n} {y : (singularChains ℤ (TopCat.of A)).X n}
    (hx : (inclChains X V).f n x = (inclChains X A).f n y) :
    x ∈ LinearMap.range ((inclChains (TopCat.of V) (relSubset A V)).f n).hom := by
  classical
  have hspec : (ModuleCat.Hom.hom (chainRetract ℤ X V n)).comp
      (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X V))
        (ModuleCat.of ℤ ℤ)).f n)) = LinearMap.id := by
    have hh := congrArg ModuleCat.Hom.hom (chainRetract_spec ℤ X V n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
    exact hh
  have hcrSSet : (ModuleCat.Hom.hom (chainRetract ℤ X V n))
      ((ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X V))
        (ModuleCat.of ℤ ℤ)).f n)) x) = x := by
    have h2 : ((ModuleCat.Hom.hom (chainRetract ℤ X V n)).comp
        (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X V))
          (ModuleCat.of ℤ ℤ)).f n))) x = x := by
      rw [hspec]
      rfl
    exact h2
  have hcr : (ModuleCat.Hom.hom (chainRetract ℤ X V n)) ((inclChains X V).f n x) = x := hcrSSet
  have hx' : x = (ModuleCat.Hom.hom ((inclChains X A).f n ≫ chainRetract ℤ X V n)) y := by
    rw [← hcr, hx]
    rfl
  let P : Submodule ℤ ((singularChains ℤ (TopCat.of V)).X n) :=
    LinearMap.range (((inclChains (TopCat.of V) (relSubset A V)).f n).hom)
  have hgen : ∀ σ : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌,
      gen (TopCat.of A) n σ ∈ P.comap
        ((inclChains X A).f n ≫ chainRetract ℤ X V n).hom := by
    intro σ
    have hA : (ModuleCat.Hom.hom ((inclChains X A).f n)) (gen (TopCat.of A) n σ)
        = gen X n ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ) :=
      chainComplexMap_ι_apply (TopCat.toSSet.map (subtypeIncl X A)) n σ 1
    have hgoal : (chainRetract ℤ X V n).hom
        (gen X n ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ)) ∈ P := by
      rw [chainRetract_gen_apply V n
        ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ)]
      by_cases hz : ∃ τ : (TopCat.toSSet.obj (TopCat.of V)) _⦋n⦌,
          (TopCat.toSSet.map (subtypeIncl X V)).app (Opposite.op ⦋n⦌) τ
            = (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ
      · rw [dif_pos hz]
        exact gen_mem_range_incl_of_factors A V n σ (Classical.choose hz)
          (Classical.choose_spec hz)
      · rw [dif_neg hz]
        exact Submodule.zero_mem P
    refine Submodule.mem_comap.mpr ?_
    have hcomp : (ModuleCat.Hom.hom ((inclChains X A).f n ≫ chainRetract ℤ X V n))
        (gen (TopCat.of A) n σ)
        = (chainRetract ℤ X V n).hom
            (gen X n ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ)) := by
      rw [← hA]
      rfl
    rw [hcomp]
    exact hgoal
  have hQ : P.comap ((inclChains X A).f n ≫ chainRetract ℤ X V n).hom = ⊤ :=
    mem_of_gen (TopCat.of A) n _ hgen
  have hyQ : y ∈ P.comap ((inclChains X A).f n ≫ chainRetract ℤ X V n).hom := by
    rw [hQ]; exact Submodule.mem_top
  have hy : (ModuleCat.Hom.hom ((inclChains X A).f n ≫ chainRetract ℤ X V n)) y ∈ P := hyQ
  obtain ⟨z, hz⟩ := hy
  exact LinearMap.mem_range.mpr ⟨z, by rw [hz]; exact hx'.symm⟩

/-- **Support transfer, in the form of the gluing square.**  If the image in `M` of a chain `γ` of
`W` is in the range of the inclusion of the chains of `S`, then `γ` lies in the range of the
inclusion of the chains of `W ∩ S = pdTr W S`. -/
theorem mem_range_inclChains_of_image {M : TopCat} {W S : Set M} (n : ℕ)
    {γ : (singularChains ℤ (TopCat.of W)).X n}
    (hγ : (inclChains M W).f n γ ∈ LinearMap.range ((inclChains M S).f n).hom) :
    γ ∈ LinearMap.range ((inclChains (TopCat.of W) (pdTr W S)).f n).hom := by
  obtain ⟨δ, hδ⟩ := hγ
  exact mem_range_inclChains_of_image_aux S W n hδ.symm

end

end Work.Cohomology
