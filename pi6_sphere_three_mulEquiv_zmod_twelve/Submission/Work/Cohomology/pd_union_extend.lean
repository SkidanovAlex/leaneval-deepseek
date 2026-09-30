import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.capRelAux

/-!
# Extending a class of the intersection to the two pieces of a cover

Let `M` be a Hausdorff space, `c ∈ H_N(M)`, `U, V ⊆ M` open and suppose that the duality maps
`D_U`, `D_V`, `D_{U∩V}` are isomorphisms (`Good N c U`, `Good N c V`, `Good N c (U∩V)`).

`Work.Cohomology.pd_union_extend` (at the end of this file) states: for a compact `K₀ ⊆ U ∩ V` and a
class `w ∈ H^k(U∩V, (U∩V)∖K₀)`, there are compact `K₁' ⊆ U`, `K₂' ⊆ V` containing `K₀` and classes
`y₁, y₂ ∈ H^k(U∪V, (U∪V)∖K₁')` whose duality maps on `U` and `V` are the images of `w ⌢ μ`, and
which agree after enlarging the compact set to `K₁' ∪ K₂'`.

## The proof

Both conclusions are obtained with the *same* compact set `K₀` (`K₁' = K₂' = K₀`, `y₁ = y₂ = y`),
where `y ∈ H^k(U∪V, (U∪V)∖K₀)` is constructed so that its restriction to `U ∩ V` is `w`:

* restricting via the ambient space (`pdRestr_comp_subtype_apply`) exhibits the restriction
  `H^k(M, M∖K₀) → H^k(U∩V, (U∩V)∖K₀)` as the composite of `M → U∪V` and `U∪V → U∩V`; both of
  those are isomorphisms by **excision** (`capRel_excision_isIso`);
* hence `y` may be taken to be the image of `w` under the inverse of the excision isomorphism
  `H^k(M, M∖K₀) → H^k(U∩V, (U∩V)∖K₀)` followed by `H^k(M, M∖K₀) → H^k(U∪V, (U∪V)∖K₀)`;
* restricting further to `U` (`pdRestr_comp_apply`) shows that the resulting class in
  `H^k(U∩V, (U∩V)∖K₀)` is still `w`, whence the two duality identities are instances of the
  naturality `pd_goodD_incl` of the duality map in the open set.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Auxiliary functoriality lemmas -/

/-- The pair map on relative cochains does not depend on the proof that the map of pairs carries
`A₁` into `A₂`. -/
theorem pd_relComplexMap_h_congr {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h h' : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ f h' :=
  capRel_relComplexMap_congr ℤ A₁ A₂ rfl h h'

/-- The composite of the two inclusions `V ⊆ U ⊆ W` is the inclusion `V ⊆ W`. -/
theorem pdIncl_comp {M : TopCat} {V U W : Set M} (hVU : V ⊆ U) (hUW : U ⊆ W) :
    pdIncl U V hVU ≫ pdIncl W U hUW = pdIncl W V (hVU.trans hUW) := by
  ext x
  rfl

/-- **Element-level functoriality**: restricting along `W → U → V` is restricting along `W → V`. -/
theorem pdRestr_comp_apply {M : TopCat} {V U W : Set M} {K : Set M} (hVU : V ⊆ U) (hUW : U ⊆ W)
    (k : ℕ) (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub V K) (pdRelSub U K)
        (pdIncl U V hVU) (fun x hx => hx)) k).hom
      ((HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub U K) (pdRelSub W K)
        (pdIncl W U hUW) (fun x hx => hx)) k).hom x)
      = (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub V K) (pdRelSub W K)
        (pdIncl W V (hVU.trans hUW)) (fun x hx => hx)) k).hom x := by
  have hmap : pdIncl U V hVU ≫ pdIncl W U hUW = pdIncl W V (hVU.trans hUW) :=
    pdIncl_comp hVU hUW
  have h2 := capRel_relComplexMap_comp ℤ (pdRelSub V K) (pdRelSub U K) (pdRelSub W K)
    (pdIncl U V hVU) (pdIncl W U hUW) (fun x hx => hx) (fun x hx => hx)
  have hconv := capRel_relComplexMap_congr ℤ (pdRelSub V K) (pdRelSub W K) hmap
    (fun x hx => hx) (fun x hx => hx)
  have h5 := congrArg (fun m : (relComplex ℤ (TopCat.of W) (pdRelSub W K)) ⟶
      (relComplex ℤ (TopCat.of V) (pdRelSub V K)) =>
        (HomologicalComplex.homologyMap m k).hom x) hconv
  have h4 := congrArg (fun m : (relComplex ℤ (TopCat.of W) (pdRelSub W K)) ⟶
      (relComplex ℤ (TopCat.of V) (pdRelSub V K)) =>
        (HomologicalComplex.homologyMap m k).hom x) h2
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h4
  exact h4.symm.trans h5

/-- **Element-level functoriality**: restricting along `M → W → V` is restricting along `M → V`. -/
theorem pdRestr_comp_subtype_apply {M : TopCat} {V W : Set M} {K : Set M} (hVW : V ⊆ W)
    (k : ℕ) (z : (relComplex ℤ M (Kᶜ)).homology k) :
    (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub V K) (pdRelSub W K)
        (pdIncl W V hVW) (fun x hx => hx)) k).hom
      ((HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub W K) Kᶜ (subtypeIncl M W)
        (fun x hx => hx)) k).hom z)
      = (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub V K) Kᶜ (subtypeIncl M V)
        (fun x hx => hx)) k).hom z := by
  have hmap : pdIncl W V hVW ≫ subtypeIncl M W = subtypeIncl M V := by
    ext x
    rfl
  have h2 := capRel_relComplexMap_comp ℤ (pdRelSub V K) (pdRelSub W K) Kᶜ
    (pdIncl W V hVW) (subtypeIncl M W) (fun x hx => hx) (fun x hx => hx)
  have hconv := capRel_relComplexMap_congr ℤ (pdRelSub V K) Kᶜ hmap
    (fun x hx => hx) (fun x hx => hx)
  have h5 := congrArg (fun m : (relComplex ℤ M (Kᶜ)) ⟶
      (relComplex ℤ (TopCat.of V) (pdRelSub V K)) =>
        (HomologicalComplex.homologyMap m k).hom z) hconv
  have h4 := congrArg (fun m : (relComplex ℤ M (Kᶜ)) ⟶
      (relComplex ℤ (TopCat.of V) (pdRelSub V K)) =>
        (HomologicalComplex.homologyMap m k).hom z) h2
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h4
  exact h4.symm.trans h5

/-! ## The named restriction maps -/

/-- The restriction `U ∪ V → U ∩ V`. -/
noncomputable def pdMapInterHom {M : TopCat} (U V K : Set M) (k : ℕ) :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V) K) (pdRelSub (U ∪ V) K)
    (pdIncl (U ∪ V) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left))
    (fun x hx => hx)) k

/-- The restriction `U ∪ V → U`. -/
noncomputable def pdMapWUHom {M : TopCat} (U V K : Set M) (k : ℕ) :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub U K) (pdRelSub (U ∪ V) K)
    (pdIncl (U ∪ V) U Set.subset_union_left) (fun x hx => hx)) k

/-- The restriction `U ∪ V → V`. -/
noncomputable def pdMapWVHom {M : TopCat} (U V K : Set M) (k : ℕ) :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub V K) (pdRelSub (U ∪ V) K)
    (pdIncl (U ∪ V) V Set.subset_union_right) (fun x hx => hx)) k

/-- The restriction `U → U ∩ V`. -/
noncomputable def pdMapIUHom {M : TopCat} (U V K : Set M) (k : ℕ) :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V) K) (pdRelSub U K)
    (pdIncl U (U ∩ V) Set.inter_subset_left) (fun x hx => hx)) k

/-- The restriction `V → U ∩ V`. -/
noncomputable def pdMapIVHom {M : TopCat} (U V K : Set M) (k : ℕ) :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V) K) (pdRelSub V K)
    (pdIncl V (U ∩ V) Set.inter_subset_right) (fun x hx => hx)) k

/-- The restriction `M → U ∩ V`. -/
noncomputable def pdMapMtIHom {M : TopCat} (U V K : Set M) (k : ℕ) :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V) K) Kᶜ
    (subtypeIncl M (U ∩ V)) (fun x hx => hx)) k

/-- The restriction `M → U ∪ V`. -/
noncomputable def pdMapMtWHom {M : TopCat} (U V K : Set M) (k : ℕ) :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∪ V) K) Kᶜ
    (subtypeIncl M (U ∪ V)) (fun x hx => hx)) k

/-- The two composites `U∪V → U → U∩V` and `U∪V → V → U∩V` differ only in the proof that
`U ∩ V ⊆ U ∪ V`. -/
theorem pdMapInterHom_congr_h {M : TopCat} {U V : Set M} {K : Set M} {h h' : U ∩ V ⊆ U ∪ V}
    (k : ℕ) (x : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) K)).homology k) :
    (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V) K) (pdRelSub (U ∪ V) K)
      (pdIncl (U ∪ V) (U ∩ V) h) (fun x hx => hx)) k).hom x
    = (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V) K) (pdRelSub (U ∪ V) K)
      (pdIncl (U ∪ V) (U ∩ V) h') (fun x hx => hx)) k).hom x := by
  have hmap : pdIncl (U ∪ V) (U ∩ V) h = pdIncl (U ∪ V) (U ∩ V) h' := by
    rw [Subsingleton.elim h h']
  have hc := capRel_relComplexMap_congr ℤ (pdRelSub (U ∩ V) K) (pdRelSub (U ∪ V) K) hmap
    (fun x hx => hx) (fun x hx => hx)
  exact congrArg (fun m : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) K)) ⟶
      (relComplex ℤ (TopCat.of (U ∩ V : Set M)) (pdRelSub (U ∩ V) K)) =>
        (HomologicalComplex.homologyMap m k).hom x) hc

/-- **The restriction `M → U ∩ V` is an isomorphism on relative cohomology** (excision). -/
theorem pdMapMtIHom_isIso {M : TopCat} [T2Space M] {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {K : Set M} (hKU : K ⊆ U) (hKV : K ⊆ V) (hKc : IsCompact K) (k : ℕ) :
    IsIso (pdMapMtIHom U V K k) := by
  have hcovI : (U ∩ V : Set M) ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl ⟨hKU hx, hKV hx⟩
    · exact Or.inr hx
  exact capRel_excision_isIso M (U ∩ V) Kᶜ (hU.inter hV) hKc.isClosed.isOpen_compl hcovI k
    (fun x hx => hx)

/-- **The restriction `M → U ∪ V` is an isomorphism on relative cohomology** (excision). -/
theorem pdMapMtWHom_isIso {M : TopCat} [T2Space M] {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {K : Set M} (hKU : K ⊆ U) (hKc : IsCompact K) (k : ℕ) :
    IsIso (pdMapMtWHom U V K k) := by
  have hcovW : (U ∪ V : Set M) ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl (Set.mem_union_left V (hKU hx))
    · exact Or.inr hx
  exact capRel_excision_isIso M (U ∪ V) Kᶜ (hU.union hV) hKc.isClosed.isOpen_compl hcovW k
    (fun x hx => hx)

/-! ## The main lemma -/

theorem pd_union_extend {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Work.Cohomology.Good N c U hU) (hVV : Work.Cohomology.Good N c V hV)
    (hII : Work.Cohomology.Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N)
    {K₀ : Set M} (hK₀I : K₀ ⊆ U ∩ V) (hK₀c : IsCompact K₀)
    (w : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∩ V : Set M))
          (Work.Cohomology.pdRelSub (U ∩ V : Set M) K₀)).homology k) :
    ∃ (K₁' K₂' : Set M) (h₁ : K₀ ⊆ K₁') (h₂ : K₀ ⊆ K₂') (hK₁'U : K₁' ⊆ U) (hK₂'V : K₂' ⊆ V)
      (hK₁'c : IsCompact K₁') (hK₂'c : IsCompact K₂')
      (y₁ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁')).homology k)
      (y₂ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂')).homology k),
      (Work.Cohomology.goodD N c U hU K₁' hK₁'U hK₁'c k m hkm
          ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
              (Work.Cohomology.pdRelSub U K₁') (Work.Cohomology.pdRelSub (U ∪ V) K₁')
              (Work.Cohomology.pdIncl (U ∪ V) U Set.subset_union_left)
              (fun x hx => hx)) k) y₁))
        = (HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of U)
              (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)) m)
          (Work.Cohomology.goodD N c (U ∩ V) hI K₀ hK₀I hK₀c k m hkm w)
      ∧ (Work.Cohomology.goodD N c V hV K₂' hK₂'V hK₂'c k m hkm
          ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
              (Work.Cohomology.pdRelSub V K₂') (Work.Cohomology.pdRelSub (U ∪ V) K₂')
              (Work.Cohomology.pdIncl (U ∪ V) V Set.subset_union_right)
              (fun x hx => hx)) k) y₂))
        = (HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of V)
              (Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right)) m)
          (Work.Cohomology.goodD N c (U ∩ V) hI K₀ hK₀I hK₀c k m hkm w)
      ∧ (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
          (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) y₁
        = (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) y₂ := by
  classical
  have hK₀U : K₀ ⊆ U := hK₀I.trans Set.inter_subset_left
  have hK₀V : K₀ ⊆ V := hK₀I.trans Set.inter_subset_right
  -- the class `y`
  haveI hIso : IsIso (pdMapMtIHom U V K₀ k) := pdMapMtIHom_isIso hU hV hK₀U hK₀V hK₀c k
  let z : (relComplex ℤ M (K₀ᶜ)).homology k := (CategoryTheory.inv (pdMapMtIHom U V K₀ k)).hom w
  let y : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) K₀)).homology k :=
    (pdMapMtWHom U V K₀ k).hom z
  have hz : (pdMapMtIHom U V K₀ k).hom z = w := IsIso.inv_hom_id_apply _ _
  -- its restriction to `U ∩ V` is `w`
  have hy : (pdMapInterHom U V K₀ k).hom y = w := by
    have h := pdRestr_comp_subtype_apply (M := M) (V := U ∩ V) (W := U ∪ V) (K := K₀)
      (Set.inter_subset_left.trans Set.subset_union_left) k z
    exact h.trans hz
  -- the two composites with the restrictions to `U` and `V`
  have hσU : (pdMapIUHom U V K₀ k).hom ((pdMapWUHom U V K₀ k).hom y) = w := by
    have h := pdRestr_comp_apply (M := M) (V := U ∩ V) (U := U) (W := U ∪ V) (K := K₀)
      Set.inter_subset_left Set.subset_union_left k y
    exact h.trans hy
  have hσV : (pdMapIVHom U V K₀ k).hom ((pdMapWVHom U V K₀ k).hom y) = w := by
    have h := pdRestr_comp_apply (M := M) (V := U ∩ V) (U := V) (W := U ∪ V) (K := K₀)
      Set.inter_subset_right Set.subset_union_right k y
    have hc := pdMapInterHom_congr_h (M := M) (U := U) (V := V) (K := K₀)
      (h := Set.inter_subset_right.trans Set.subset_union_right)
      (h' := Set.inter_subset_left.trans Set.subset_union_left) k y
    exact h.trans (hc.trans hy)
  refine ⟨K₀, K₀, Set.Subset.rfl, Set.Subset.rfl, hK₀U, hK₀V, hK₀c, hK₀c, y, y, ?_, ?_, ?_⟩
  · show goodD N c U hU K₀ hK₀U hK₀c k m hkm ((pdMapWUHom U V K₀ k).hom y)
      = (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of U)
          (pdIncl U (U ∩ V) Set.inter_subset_left)) m)
        (goodD N c (U ∩ V) hI K₀ hK₀I hK₀c k m hkm w)
    rw [← hσU]
    exact (pd_goodD_incl (M := M) (W := U) (V := U ∩ V) Set.inter_subset_left hU hI hK₀I
      hK₀U hK₀c N c k m hkm ((pdMapWUHom U V K₀ k).hom y)).symm
  · show goodD N c V hV K₀ hK₀V hK₀c k m hkm ((pdMapWVHom U V K₀ k).hom y)
      = (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of V)
          (pdIncl V (U ∩ V) Set.inter_subset_right)) m)
        (goodD N c (U ∩ V) hI K₀ hK₀I hK₀c k m hkm w)
    rw [← hσV]
    exact (pd_goodD_incl (M := M) (W := V) (V := U ∩ V) Set.inter_subset_right hV hI hK₀I
      hK₀V hK₀c N c k m hkm ((pdMapWVHom U V K₀ k).hom y)).symm
  · have h3 : pdRelComplexEnlarge (U ∪ V) (Set.subset_union_left : K₀ ⊆ K₀ ∪ K₀)
        = pdRelComplexEnlarge (U ∪ V) (Set.subset_union_right : K₀ ⊆ K₀ ∪ K₀) := by
      unfold pdRelComplexEnlarge
      exact pd_relComplexMap_h_congr _ _ _ _ _
    rw [h3]

end

end Work.Cohomology
