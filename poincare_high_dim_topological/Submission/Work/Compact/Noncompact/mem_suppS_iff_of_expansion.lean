import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.exists_localMap_eq_zero

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

noncomputable section

open scoped BigOperators

variable {X : TopCat}

/-- The singular simplices of `TopCat.of S` regarded as singular simplices of `X`, by pushing
forward along the inclusion `S ⊆ X`. -/
def inclSimplex (X : TopCat) (S : Set X) (k : ℕ) : SimplexT (TopCat.of S) k → SimplexT X k :=
  fun σ => (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)).app
    (Opposite.op (SimplexCategory.mk k)) σ

@[simp]
lemma inclSimplex_apply (X : TopCat) (S : Set X) (k : ℕ) (σ : SimplexT (TopCat.of S) k) :
    inclSimplex X S k σ = (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)).app
      (Opposite.op (SimplexCategory.mk k)) σ := rfl

/-- The generator `ιChainComplex σ` of the simplicial chains, applied to a coefficient `a`, is the
multiple `a • genC` of the corresponding singular chain generator. -/
lemma iota_hom_eq_zsmul_gen (k : ℕ) (σ : SimplexT X k) (a : ℤ) :
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a)
      = a • genC X k σ := by
  conv_lhs => rw [show a = a • (1 : ℤ) by simp]
  exact (map_zsmul _ a 1).trans rfl

/-- The chain map `inclChains X S` on a generator, in the `ιChainComplex` guise. -/
lemma inclChains_f_ι_aux (X : TopCat) (S : Set X) (k : ℕ) (σ : SimplexT (TopCat.of S) k)
    (b : ℤ) :
    ((Work.Cohomology.inclChains X S).f k).hom
        (((TopCat.toSSet.obj (TopCat.of S)).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom b)
      = ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (inclSimplex X S k σ)).hom b := by
  rw [inclSimplex_apply]
  have hkey := SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of S)) (TopCat.toSSet.obj X)
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)) (ModuleCat.of ℤ ℤ) σ
  have h2 := congrArg (fun (g : (ModuleCat.of ℤ ℤ) ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X k) =>
        (ModuleCat.Hom.hom g) b) hkey
  rw [ModuleCat.comp_apply] at h2
  exact h2

/-- The chain map `inclChains X S` on a generator, in the `genC` guise. -/
lemma inclChains_f_ι (X : TopCat) (S : Set X) (k : ℕ) (σ : SimplexT (TopCat.of S) k) (b : ℤ) :
    ((Work.Cohomology.inclChains X S).f k).hom
        (((TopCat.toSSet.obj (TopCat.of S)).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom b)
      = b • genC X k (inclSimplex X S k σ) := by
  rw [inclChains_f_ι_aux, iota_hom_eq_zsmul_gen]

/-- The image of a simplex of the subspace `S` lies in `S`. -/
lemma simplexSet_inclSimplex_subset (X : TopCat) (S : Set X) (k : ℕ)
    (σ : SimplexT (TopCat.of S) k) : SimplexSet (inclSimplex X S k σ) ⊆ S := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  simp only [inclSimplex_apply]
  rw [Work.Homology.toSSetObjEquiv'_map_apply]
  exact (Work.Homology.toSSetObjEquiv' (TopCat.of S)
    (Opposite.op (SimplexCategory.mk k)) σ z).2

/-- A singular simplex whose image lies in `S` generates a chain supported in `S`. -/
lemma genC_mem_suppS_of_simplexSet_subset {k : ℕ} {S : Set X} {σ : SimplexT X k}
    (h : SimplexSet σ ⊆ S) : genC X k σ ∈ suppS X S k := by
  have h' : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk k)) σ z ∈ S := by
    intro z
    have h1 := h (Set.mem_range_self (Work.Homology.stdHomeo k z))
    simp only [Work.Homology.toSSetObjEquiv'_apply, Homeomorph.symm_apply_apply] at h1
    exact h1
  refine ⟨genC (TopCat.of S) k (liftSimplex σ h'), ?_⟩
  rw [show genC (TopCat.of S) k (liftSimplex σ h')
      = ((TopCat.toSSet.obj (TopCat.of S)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (liftSimplex σ h')).hom (1 : ℤ) from rfl]
  rw [inclChains_f_ι]
  rw [inclSimplex_apply, toSSet_map_subtypeIncl_liftSimplex]
  simp

/-- The submodule of chains supported in `S` is closed under multiplication by an integer. -/
lemma suppS_smul {k : ℕ} {S : Set X} (a : ℤ) {c : Ch X k}
    (hc : c ∈ suppS X S k) : a • c ∈ suppS X S k := by
  obtain ⟨y, hy⟩ := hc
  exact ⟨a • y, by rw [map_zsmul, hy]⟩

/-- Regrouping a finite sum of generators over the image of a map: the coefficient at an image point
is the sum of the coefficients of its fibre. -/
lemma sum_image_hom_ι (X : TopCat) (k : ℕ) {α : Type*} [DecidableEq (SimplexT X k)]
    (φ : α → SimplexT X k) (T' : Finset α) (b : α → ℤ) :
    (∑ σ' ∈ T', ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (φ σ')).hom (b σ'))
      = ∑ σ ∈ T'.image φ, ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom
          (∑ σ' ∈ T'.filter (fun σ' => φ σ' = σ), b σ') := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := T') (t := T'.image φ) (g := φ)
    (fun i hi => Finset.mem_image_of_mem φ hi)
    (f := fun σ' => ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (φ σ')).hom
      (b σ'))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ' hσ' => ?_
  rw [(Finset.mem_filter.mp hσ').2]

theorem mem_suppS_iff_of_expansion {X : TopCat} (k : ℕ) (c : Work.Compact.Noncompact.Ch X k)
    (S : Set X) :
    c ∈ Work.Compact.Noncompact.suppS X S k ↔
      ∃ (T : Finset (Work.Compact.Noncompact.SimplexT X k))
        (a : Work.Compact.Noncompact.SimplexT X k → ℤ),
        c = ∑ σ ∈ T, a σ • Work.Compact.Noncompact.genC X k σ ∧
        ∀ σ ∈ T, a σ ≠ 0 → Work.Compact.Noncompact.SimplexSet σ ⊆ S := by
  classical
  constructor
  · intro hc
    rw [suppS, LinearMap.mem_range] at hc
    obtain ⟨c', hc'⟩ := hc
    obtain ⟨T', b, hb⟩ := chain_eq_sum_ιChainComplex (TopCat.toSSet.obj (TopCat.of S)) k c'
    refine ⟨T'.image (inclSimplex X S k),
      (fun σ => ∑ σ' ∈ T'.filter (fun σ' => inclSimplex X S k σ' = σ), b σ'), ?_, ?_⟩
    · have hpush : ((Work.Cohomology.inclChains X S).f k).hom c'
            = ∑ σ' ∈ T', b σ' • genC X k (inclSimplex X S k σ') := by
        rw [hb, map_sum]
        exact Finset.sum_congr rfl fun σ' _ => inclChains_f_ι X S k σ' (b σ')
      have hι₁ : (∑ σ' ∈ T', b σ' • genC X k (inclSimplex X S k σ'))
          = ∑ σ' ∈ T', ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
              (inclSimplex X S k σ')).hom (b σ') := by
        refine Finset.sum_congr rfl fun σ' _ => ?_
        rw [iota_hom_eq_zsmul_gen]
      have hι₂ : (∑ σ ∈ T'.image (inclSimplex X S k),
            (∑ σ' ∈ T'.filter (fun σ' => inclSimplex X S k σ' = σ), b σ') • genC X k σ)
          = ∑ σ ∈ T'.image (inclSimplex X S k),
              ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom
                (∑ σ' ∈ T'.filter (fun σ' => inclSimplex X S k σ' = σ), b σ') := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [iota_hom_eq_zsmul_gen]
      have heq := hι₁.trans ((sum_image_hom_ι X k (inclSimplex X S k) T' b).trans hι₂.symm)
      rw [← hc', hpush, heq]
    · intro σ hσ _
      obtain ⟨σ', _, rfl⟩ := Finset.mem_image.mp hσ
      exact simplexSet_inclSimplex_subset X S k σ'
  · rintro ⟨T, a, hc, hsupp⟩
    rw [hc]
    refine Submodule.sum_mem (suppS X S k) fun σ hσ => ?_
    by_cases ha : a σ = 0
    · rw [ha, zero_smul]
      exact (suppS X S k).zero_mem
    · exact suppS_smul (a σ) (genC_mem_suppS_of_simplexSet_subset (hsupp σ hσ ha))

end

end Work.Compact.Noncompact
