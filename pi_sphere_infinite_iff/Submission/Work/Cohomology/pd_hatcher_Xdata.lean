import Mathlib
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.chainRetract_mem_range_inclChains
import Submission.Work.Cohomology.mem_range_inclChains_of_image
import Submission.Work.Cohomology.pd_relsub_aux

/-!
# The Hatcher decomposition in `U ∪ V`, starting from data in the ambient space

`Work.Cohomology.pd_hatcher_Xdata` is the form of Hatcher's Lemma 3.36 (the decomposition of a
cycle into pieces supported in `U ∖ L`, `U ∩ V`, `V ∖ K` and `(K ∪ L)ᶜ`) in which the three
summands `α₁, α₂, α₃` and the discarded piece `j` are *given* in the ambient space `M`, together
with a cycle `α` representing `c` whose underlying chain is `α₁ + α₂ + α₃ + j`.

The conclusion descends the three summands to the open set `W := U ∪ V` (they are supported in the
subspaces `U ∖ L`, `U ∩ V`, `V ∖ K`, all contained in `W`), verifies the support of their
boundaries, and produces the relative cycle `γ` representing the local fundamental class.

The proof is the one of `pd_hatcher_W` with the first half — the construction of the small cycle —
replaced by the hypotheses.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

theorem pd_hatcher_Xdata {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N} {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (α : (Work.Cohomology.singularChains ℤ M).cycles N)
    (α₁ α₂ α₃ : (Work.Cohomology.singularChains ℤ M).X N)
    (j : (Work.Cohomology.singularChains ℤ M).X N)
    (hα : (Work.Cohomology.singularChains ℤ M).iCycles N α = (α₁ + α₂ + α₃) + j)
    (hj : j ∈ LinearMap.range (((Work.Cohomology.inclChains M ((K ∪ L)ᶜ)).f N).hom))
    (hα₁ : α₁ ∈ LinearMap.range (((Work.Cohomology.inclChains M (U \ L)).f N).hom))
    (hα₂ : α₂ ∈ LinearMap.range (((Work.Cohomology.inclChains M (U ∩ V)).f N).hom))
    (hα₃ : α₃ ∈ LinearMap.range (((Work.Cohomology.inclChains M (V \ K)).f N).hom))
    (hc : HomologicalComplex.homologyπ (Work.Cohomology.singularChains ℤ M) N α = c) :
    ∃ (α₁X α₂X α₃X : (Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N)
      (ξX : (Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N)
      (γX : (Work.Cohomology.relChains (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K ∪ L))).cycles N),
      (Work.Cohomology.inclChains M (U ∪ V)).f N α₁X = α₁ ∧
      (Work.Cohomology.inclChains M (U ∪ V)).f N α₂X = α₂ ∧
      (Work.Cohomology.inclChains M (U ∪ V)).f N α₃X = α₃ ∧
      ξX = α₁X + α₂X + α₃X ∧
      (∃ a'', (Work.Cohomology.inclChains (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdTr (U ∪ V) (U \ L))).f N a'' = α₁X) ∧
      (∃ bX, (Work.Cohomology.inclChains (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdTr (U ∪ V) (U ∩ V))).f N bX = α₂X) ∧
      (∃ dX, (Work.Cohomology.inclChains (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdTr (U ∪ V) (V \ K))).f N dX = α₃X) ∧
      (∃ e, (Work.Cohomology.inclChains (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V) L)).f (N-1) e
        = (Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N-1) α₁X) ∧
      (∃ f, (Work.Cohomology.inclChains (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V) K)).f (N-1) f
        = (Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N-1) α₃X) ∧
      (Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N-1) ξX
        ∈ LinearMap.range (((Work.Cohomology.inclChains (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K ∪ L))).f (N-1)).hom) ∧
      (Work.Cohomology.relChains (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K ∪ L))).homologyπ N γX
        = Work.Cohomology.localFundClass N c (U ∪ V) (hU.union hV) (K ∪ L)
            (Set.union_subset (hKU.trans Set.subset_union_left)
              (hLV.trans Set.subset_union_right)) (hKc.union hLc) ∧
      (Work.Cohomology.relChains (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K ∪ L))).iCycles N γX
        = ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K ∪ L)))).f N).hom ξX := by
  classical
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  have hK'c : IsCompact (K ∪ L) := hKc.union hLc
  have hK'W : K ∪ L ⊆ (U ∪ V : Set M) :=
    Set.union_subset (hKU.trans Set.subset_union_left) (hLV.trans Set.subset_union_right)
  have h1 : U \ L ⊆ (U ∪ V : Set M) := Set.sdiff_subset.trans Set.subset_union_left
  have h2 : (U ∩ V : Set M) ⊆ (U ∪ V : Set M) :=
    Set.inter_subset_left.trans Set.subset_union_left
  have h3 : V \ K ⊆ (U ∪ V : Set M) := Set.sdiff_subset.trans Set.subset_union_right
  -- the three summands lie in the chains of `U ∪ V`
  have hmemA : α₁ ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M (U ∪ V)).f N)) :=
    mem_range_inclChains_of_subset (S := U \ L) (T := U ∪ V) h1 hα₁
  have hmemB : α₂ ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M (U ∪ V)).f N)) :=
    mem_range_inclChains_of_subset (S := U ∩ V) (T := U ∪ V) h2 hα₂
  have hmemD : α₃ ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M (U ∪ V)).f N)) :=
    mem_range_inclChains_of_subset (S := V \ K) (T := U ∪ V) h3 hα₃
  -- the three summands, descended to `C_*(U ∪ V)`
  let α₁X : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N :=
    (chainRetract ℤ M (U ∪ V) N).hom α₁
  let α₂X : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N :=
    (chainRetract ℤ M (U ∪ V) N).hom α₂
  let α₃X : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N :=
    (chainRetract ℤ M (U ∪ V) N).hom α₃
  have h1incl : (inclChains M (U ∪ V)).f N α₁X = α₁ := chainRetract_of_mem_range hmemA
  have h2incl : (inclChains M (U ∪ V)).f N α₂X = α₂ := chainRetract_of_mem_range hmemB
  have h3incl : (inclChains M (U ∪ V)).f N α₃X = α₃ := chainRetract_of_mem_range hmemD
  -- the supports of the descended summands
  have hsup1 : α₁X ∈ LinearMap.range (ModuleCat.Hom.hom
      ((inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (U \ L))).f N)) :=
    chainRetract_mem_range_of_subset h1 hα₁
  have hsup2 : α₂X ∈ LinearMap.range (ModuleCat.Hom.hom
      ((inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (U ∩ V))).f N)) :=
    chainRetract_mem_range_of_subset h2 hα₂
  have hsup3 : α₃X ∈ LinearMap.range (ModuleCat.Hom.hom
      ((inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (V \ K))).f N)) :=
    chainRetract_mem_range_of_subset h3 hα₃
  obtain ⟨a'', ha''⟩ := hsup1
  obtain ⟨bX, hbX⟩ := hsup2
  obtain ⟨dX, hdX⟩ := hsup3
  -- the total sum, in `C_*(U ∪ V)` and in `C_*(M)`
  have hξincl : (inclChains M (U ∪ V)).f N (α₁X + α₂X + α₃X) = α₁ + α₂ + α₃ := by
    rw [map_add, map_add, h1incl, h2incl, h3incl]
  have hξw : (inclChains M (U ∪ V)).f N (α₁X + α₂X + α₃X)
      = (singularChains ℤ M).iCycles N α - j := by
    rw [hξincl, hα]
    abel
  -- the discarded summand is killed by the projection to `C_*(M, M∖(K∪L))`
  have hj0 : ((cokernel.π (inclChains M (K ∪ L)ᶜ)).f N) j = 0 := by
    obtain ⟨y, rfl⟩ := hj
    exact cokernel_π_f_apply_eq_zero N y
  -- the boundary of the descended sum is relatively small
  have hDξ : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) (α₁X + α₂X + α₃X)
      ∈ LinearMap.range (ModuleCat.Hom.hom
          ((inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).f (N - 1))) := by
    refine mem_range_inclChains_of_image (M := M) (W := (U ∪ V : Set M)) (S := (K ∪ L)ᶜ)
      (N - 1) (γ := (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1)
        (α₁X + α₂X + α₃X)) ?_
    have hnat : (inclChains M (U ∪ V)).f (N - 1)
        ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) (α₁X + α₂X + α₃X))
        = (singularChains ℤ M).d N (N - 1)
            ((inclChains M (U ∪ V)).f N (α₁X + α₂X + α₃X)) := by
      have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N ⟶
          (singularChains ℤ M).X (N - 1)) => (ModuleCat.Hom.hom g) (α₁X + α₂X + α₃X))
        ((inclChains M (U ∪ V)).comm N (N - 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h.symm
    rw [hnat, hξincl]
    have h0 : (singularChains ℤ M).d N (N - 1) (α₁ + α₂ + α₃)
        + (singularChains ℤ M).d N (N - 1) j = 0 := by
      have h1 : (singularChains ℤ M).d N (N - 1) ((α₁ + α₂ + α₃) + j) = 0 := by
        rw [← hα, ← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
        simp
      rwa [map_add] at h1
    have hdj : (singularChains ℤ M).d N (N - 1) (α₁ + α₂ + α₃)
        = - ((singularChains ℤ M).d N (N - 1) j) := eq_neg_of_add_eq_zero_left h0
    rw [hdj]
    obtain ⟨g, hg⟩ := d_mem_range_inclChains (M := M) (S := (K ∪ L)ᶜ) (n := N) hj
    exact ⟨-g, by rw [map_neg, hg]⟩
  -- the relative cycle
  have hπξ : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).d N (N - 1)
      (((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L)))).f N)
        (α₁X + α₂X + α₃X)) = 0 := by
    show ((cokernel (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V) (K ∪ L)))).d N (N - 1))
      (((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V) (K ∪ L)))).f N) (α₁X + α₂X + α₃X)) = 0
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N ⟶
        (cokernel (inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V) (K ∪ L)))).X (N - 1)) =>
        (ModuleCat.Hom.hom g) (α₁X + α₂X + α₃X))
      ((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V) (K ∪ L)))).comm N (N - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h]
    obtain ⟨y, hy⟩ := hDξ
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero (N - 1) y
  let γX : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).cycles N :=
    cycleOf N (((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V) (K ∪ L)))).f N) (α₁X + α₂X + α₃X)) hπξ
  have hγi : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).iCycles N γX
      = ((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V) (K ∪ L)))).f N).hom (α₁X + α₂X + α₃X) := iCycles_cycleOf N _ hπξ
  -- its class is the local fundamental class
  have hcl : HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N
      ((relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γX)
      = relLocClass M N c (K ∪ L) :=
    relCycle_homologyMap_eq_relLocClass c γX hγi hc hξw hj0
  have hcov : (U ∪ V : Set M) ∪ (K ∪ L)ᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K ∪ L
    · exact Or.inl (hK'W hx)
    · exact Or.inr hx
  have hloc : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γX
      = localFundClass N c (U ∪ V) hW (K ∪ L) hK'W hK'c := by
    haveI : IsIso (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N) :=
      excision_relChainsMap_isIso M (U ∪ V) (K ∪ L)ᶜ hW hK'c.isClosed.isOpen_compl hcov N
    have hspec := localFundClass_spec N c (U ∪ V) hW (K ∪ L) hK'W hK'c
    calc (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γX
        = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N)
            (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N
              ((relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γX)) :=
            (IsIso.hom_inv_id_apply _ _).symm
      _ = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N)
            (relLocClass M N c (K ∪ L)) := by rw [hcl]
      _ = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N)
            (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N
              (localFundClass N c (U ∪ V) hW (K ∪ L) hK'W hK'c)) := by rw [hspec]
      _ = localFundClass N c (U ∪ V) hW (K ∪ L) hK'W hK'c := IsIso.hom_inv_id_apply _ _
  -- the boundaries of the first and third summands are small
  have hbd1 : ∃ e, (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) L)).f (N - 1) e
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₁X := by
    have hmemd : (inclChains M (U ∪ V)).f (N - 1)
        ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₁X)
        ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M Lᶜ).f (N - 1))) := by
      have hnat : (inclChains M (U ∪ V)).f (N - 1)
          ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₁X)
          = (singularChains ℤ M).d N (N - 1) ((inclChains M (U ∪ V)).f N α₁X) := by
        have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N ⟶
            (singularChains ℤ M).X (N - 1)) => (ModuleCat.Hom.hom g) α₁X)
          ((inclChains M (U ∪ V)).comm N (N - 1))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
        exact h.symm
      rw [hnat, h1incl]
      exact mem_range_inclChains_of_subset (S := U \ L) (T := Lᶜ) (fun x hx => hx.2)
        (d_mem_range_inclChains (M := M) (S := U \ L) hα₁)
    obtain ⟨e, he⟩ := mem_range_inclChains_of_image (M := M) (W := (U ∪ V : Set M))
      (S := Lᶜ) (N - 1) (γ := (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₁X) hmemd
    exact ⟨e, he⟩
  have hbd2 : ∃ f, (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) K)).f (N - 1) f
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₃X := by
    have hmemd : (inclChains M (U ∪ V)).f (N - 1)
        ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₃X)
        ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M Kᶜ).f (N - 1))) := by
      have hnat : (inclChains M (U ∪ V)).f (N - 1)
          ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₃X)
          = (singularChains ℤ M).d N (N - 1) ((inclChains M (U ∪ V)).f N α₃X) := by
        have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N ⟶
            (singularChains ℤ M).X (N - 1)) => (ModuleCat.Hom.hom g) α₃X)
          ((inclChains M (U ∪ V)).comm N (N - 1))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
        exact h.symm
      rw [hnat, h3incl]
      exact mem_range_inclChains_of_subset (S := V \ K) (T := Kᶜ) (fun x hx => hx.2)
        (d_mem_range_inclChains (M := M) (S := V \ K) hα₃)
    obtain ⟨f, hf⟩ := mem_range_inclChains_of_image (M := M) (W := (U ∪ V : Set M))
      (S := Kᶜ) (N - 1) (γ := (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₃X) hmemd
    exact ⟨f, hf⟩
  exact ⟨α₁X, α₂X, α₃X, α₁X + α₂X + α₃X, γX, h1incl, h2incl, h3incl, rfl,
    ⟨a'', ha''⟩, ⟨bX, hbX⟩, ⟨dX, hdX⟩, hbd1, hbd2, hDξ, hloc, hγi⟩

end

end Work.Cohomology
