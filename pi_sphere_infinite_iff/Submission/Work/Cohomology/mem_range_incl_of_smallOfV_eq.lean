import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.cokerSmallAux
import Submission.Work.Cohomology.excisionAux

open Classical

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The retraction `chainRetract` evaluated on the generator of a simplex `z` of `X`: it is `0`
except when `z` comes from a simplex of `A`, in which case it is the generator of the (unique)
preimage simplex. -/
lemma chainRetract_gen_apply {X : TopCat} (A : Set X) (n : ℕ)
    (z : (TopCat.toSSet.obj X) _⦋n⦌) :
    (chainRetract ℤ X A n).hom (gen X n z) =
      (if h : ∃ x : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌,
          (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) x = z
        then gen (TopCat.of A) n (Classical.choose h) else 0) := by
  classical
  by_cases hz : ∃ x : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌,
      (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) x = z
  · rw [dif_pos hz]
    simp only [gen]
    rw [chainRetract]
    refine (congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
        ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
          g.hom (1 : ℤ))
      (Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
        (fun y => if hy : ∃ x : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌,
            (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) x = y
              then (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Classical.choose hy)
              else 0) z)).trans ?_
    simp only [dif_pos hz]
  · rw [dif_neg hz]
    simp only [gen]
    rw [chainRetract]
    refine (congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
        ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
          g.hom (1 : ℤ))
      (Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
        (fun y => if hy : ∃ x : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌,
            (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) x = y
              then (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Classical.choose hy)
              else 0) z)).trans ?_
    simp only [dif_neg hz, ModuleCat.hom_zero, LinearMap.zero_apply]
    rfl

/-- A singular simplex `τ` of `V` whose image in `X` agrees with the image of a simplex `σ` of `A`
generates a chain of `V` coming from the relative chains of the pair `(V, V ∩ A)`. -/
lemma gen_mem_range_incl_of_factors {X : TopCat} (A V : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌)
    (τ : (TopCat.toSSet.obj (TopCat.of V)) _⦋n⦌)
    (hτ : (TopCat.toSSet.map (subtypeIncl X V)).app (Opposite.op ⦋n⦌) τ
        = (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ) :
    gen (TopCat.of V) n τ ∈
      LinearMap.range (((inclChains (TopCat.of V) (relSubset A V)).f n).hom) := by
  have hrange : Set.range (fun z : stdSimplex ℝ (Fin (n + 1)) =>
      TopCat.toSSetObjEquivT (TopCat.of V) (Opposite.op ⦋n⦌) τ z) ⊆ relSubset A V := by
    rintro w ⟨z, rfl⟩
    have h := congrArg (fun (g : C(stdSimplex ℝ (Fin (n + 1)), X)) => g z)
      (congrArg (TopCat.toSSetObjEquivT X (Opposite.op ⦋n⦌)) hτ)
    rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_map_apply] at h
    change (ConcreteCategory.hom (subtypeIncl X V))
      (TopCat.toSSetObjEquivT (TopCat.of V) (Opposite.op ⦋n⦌) τ z) ∈ A
    rw [h]
    exact (TopCat.toSSetObjEquivT (TopCat.of A) (Opposite.op ⦋n⦌) σ z).2
  obtain ⟨a, ha⟩ :=
    exists_map_inclUX_of_range_subset (relSubset A V) (Opposite.op ⦋n⦌) τ hrange
  refine ⟨gen (TopCat.of (relSubset A V)) n a, ?_⟩
  have h2 : (TopCat.toSSet.map (subtypeIncl (TopCat.of V) (relSubset A V))).app
        (Opposite.op ⦋n⦌) a
      = (TopCat.toSSet.map (inclUX (relSubset A V))).app (Opposite.op ⦋n⦌) a := rfl
  have h1 := chainComplexMap_ι_apply
    (TopCat.toSSet.map (subtypeIncl (TopCat.of V) (relSubset A V))) n a 1
  rw [h2, ha] at h1
  exact h1

/-- **Key elementwise statement for the cokernel identification.**  If a chain `x` of `V` and a chain `y` of `A` (both of degree `n`) have the same image in the small chains of the cover `{A,V}`, then `x` is the image of a chain of `V ∩ A = {x : V | (x : X) ∈ A}`.

Suggested route (the needed functoriality facts are `Work.Cohomology.smallOfU_comp_smallToSing` and `Work.Cohomology.smallOfV_comp_smallToSing`, in `Submission/Work/Cohomology/excisionAux.lean`): apply `smallToSing A V` to the hypothesis to get `(inclChains X V) x = (inclChains X A) y`, then rewrite `x` using the retraction `chainRetract ℤ X V n` (`chainRetract_spec`), giving `x = ρ y` for `ρ := (inclChains X A).f n ≫ (chainRetract ℤ X V n).hom`.  Finally show `range ρ ≤ range ((inclChains (TopCat.of V) (relSubset A V)).f n)` via `Work.Cohomology.mem_of_gen` on the space `TopCat.of A`: on a generator `gen τ` (`τ` a simplex of `A`), `ρ` returns either `0` or the generator of the simplex `τ'` of `V` with `toSSet.map (subtypeIncl X V) τ' = toSSet.map (subtypeIncl X A) τ` (this is `Cofan.IsColimit.fac` for the cofan defining `chainRetract`); in the second case the image of `τ'` in `X` lies in `A`, so `τ'` factors through `relSubset A V` by `Work.Cohomology.exists_map_inclUX_of_range_subset`, and `SSet.ι_chainComplexMap_f` gives the conclusion. -/
theorem mem_range_incl_of_smallOfV_eq {X : TopCat} (A V : Set X) (n : ℕ)
    {x : (singularChains ℤ (TopCat.of V)).X n} {y : (singularChains ℤ (TopCat.of A)).X n}
    (h : (smallOfV A V).f n x = (smallOfU A V).f n y) :
    ∃ z : (singularChains ℤ (TopCat.of (relSubset A V))).X n,
      (inclChains (TopCat.of V) (relSubset A V)).f n z = x := by
  classical
  have hx : (inclChains X V).f n x = (inclChains X A).f n y := by
    have h1 : ((smallOfV A V ≫ smallToSing A V).f n) x
        = ((smallOfU A V ≫ smallToSing A V).f n) y := by
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, h]
    rw [smallOfV_comp_smallToSing, smallOfU_comp_smallToSing] at h1
    exact h1
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
  exact ⟨z, by rw [hz]; exact hx'.symm⟩

end

end Work.Cohomology
