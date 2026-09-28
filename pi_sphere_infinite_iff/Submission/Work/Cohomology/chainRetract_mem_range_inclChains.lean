import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.pd_hatcher_decomp
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.mem_range_incl_of_smallOfV_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The chain retraction respects chains supported in a smaller subset

Let `M` be a topological space and `A, W ⊆ M`.  The retraction `chainRetract ℤ M W n` sends a
singular `n`-chain of `M` to a chain of `W`: a singular simplex of `M` coming from a simplex of `W`
is sent to that simplex, and every other simplex is sent to `0`.

The lemma `chainRetract_comp_inclChains_mem_range` below shows that the composite
`C_*(A) → C_*(M) → C_*(W)` lands in the chains of `W` supported in `W ∩ A = relSubset A W`:
a generator `gen σ` of `C_n(A)` is sent either to `0` or to the generator of the simplex `τ` of `W`
with `incl τ = incl σ`; in the second case the image of `τ` in `M` agrees with the image of `σ`,
which lies in `A`, so `τ` factors through `relSubset A W`.

The target statement `chainRetract_mem_range_inclChains` is then the immediate consequence: the
retraction of a chain of `M` lying in the image of the chains of `A` lies in the image of the
chains of `W ∩ A`.
-/

open Classical
open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

noncomputable section

section ChainRetractSupport

open scoped Simplicial

/-- **Support of the retracted inclusion.**  The composite of the inclusion `C_*(A) → C_*(M)` with
the retraction onto the chains of `V` lands in the range of the inclusion of the chains of
`V ∩ A = relSubset A V`. -/
theorem chainRetract_comp_inclChains_mem_range {X : TopCat} (A V : Set X) (n : ℕ)
    (y : (singularChains ℤ (TopCat.of A)).X n) :
    (chainRetract ℤ X V n).hom (((inclChains X A).f n).hom y) ∈
      LinearMap.range (((inclChains (TopCat.of V) (relSubset A V)).f n).hom) := by
  classical
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
  exact hy

end ChainRetractSupport

theorem chainRetract_mem_range_inclChains {M : TopCat} {A W : Set M} (hAW : A ⊆ W) {n : ℕ} {c : (Work.Cohomology.singularChains ℤ M).X n} (hc : c ∈ LinearMap.range (((Work.Cohomology.inclChains M A).f n).hom)) : (Work.Cohomology.chainRetract ℤ M W n) c ∈ LinearMap.range (((Work.Cohomology.inclChains (TopCat.of W) {y : W | (y : M) ∈ A}).f n).hom) := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hc
  exact chainRetract_comp_inclChains_mem_range A W n y

end

end Work.Cohomology
