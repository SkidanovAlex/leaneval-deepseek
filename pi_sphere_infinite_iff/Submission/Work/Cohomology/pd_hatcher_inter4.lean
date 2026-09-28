import Mathlib
import Submission.Work.Cohomology.pd_hatcher_cycles_inter
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_relsub_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

theorem pd_hatcher_inter4 {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N} {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (α : (Work.Cohomology.singularChains ℤ M).cycles N)
    (α₁ α₂ α₃ j : (Work.Cohomology.singularChains ℤ M).X N)
    (hα : (Work.Cohomology.singularChains ℤ M).iCycles N α = (α₁ + α₂ + α₃) + j)
    (hj : j ∈ LinearMap.range (((Work.Cohomology.inclChains M ((K ∪ L)ᶜ)).f N).hom))
    (hα₁ : α₁ ∈ LinearMap.range (((Work.Cohomology.inclChains M (U \ L)).f N).hom))
    (hα₂ : α₂ ∈ LinearMap.range (((Work.Cohomology.inclChains M (U ∩ V)).f N).hom))
    (hα₃ : α₃ ∈ LinearMap.range (((Work.Cohomology.inclChains M (V \ K)).f N).hom))
    (hc : HomologicalComplex.homologyπ (Work.Cohomology.singularChains ℤ M) N α = c) :
    ∃ (b' : (Work.Cohomology.singularChains ℤ (TopCat.of (U ∩ V : Set M))).X N)
      (γ : (Work.Cohomology.relChains (TopCat.of (U ∩ V : Set M))
        (Work.Cohomology.pdRelSub (U ∩ V : Set M) (K ∩ L))).cycles N),
      (Work.Cohomology.inclChains M (U ∩ V)).f N b' = α₂ ∧
      (Work.Cohomology.relChains (TopCat.of (U ∩ V : Set M))
          (Work.Cohomology.pdRelSub (U ∩ V : Set M) (K ∩ L))).iCycles N γ
        = ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (U ∩ V : Set M))
            (Work.Cohomology.pdRelSub (U ∩ V : Set M) (K ∩ L)))).f N).hom b' ∧
      (Work.Cohomology.relChains (TopCat.of (U ∩ V : Set M))
          (Work.Cohomology.pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ N γ
        = Work.Cohomology.localFundClass N c (U ∩ V) hI (K ∩ L)
            (fun x hx => ⟨hKU hx.1, hLV hx.2⟩) (IsCompact.inter hKc hLc) := by
  classical
  -- the lift of the middle summand
  obtain ⟨b', hb'⟩ := hα₂
  -- the two named summands, together with `j`, are all supported outside `K ∩ L`
  have hsub₁ : (U \ L : Set M) ⊆ (K ∩ L)ᶜ := fun _ hx h => hx.2 h.2
  have hsub₃ : (V \ K : Set M) ⊆ (K ∩ L)ᶜ := fun _ hx h => hx.2 h.1
  have hsubj : ((K ∪ L)ᶜ : Set M) ⊆ (K ∩ L)ᶜ := fun _ hx h => hx (Or.inl h.1)
  have hA₁ : α₁ ∈ LinearMap.range ((inclChains M ((K ∩ L)ᶜ)).f N).hom :=
    mem_range_inclChains_of_subset hsub₁ hα₁
  have hA₃ : α₃ ∈ LinearMap.range ((inclChains M ((K ∩ L)ᶜ)).f N).hom :=
    mem_range_inclChains_of_subset hsub₃ hα₃
  have hAJ : j ∈ LinearMap.range ((inclChains M ((K ∩ L)ᶜ)).f N).hom :=
    mem_range_inclChains_of_subset hsubj hj
  have hB₁ : (singularChains ℤ M).d N (N - 1) α₁
      ∈ LinearMap.range ((inclChains M ((K ∩ L)ᶜ)).f (N - 1)).hom :=
    mem_range_inclChains_of_subset hsub₁ (d_mem_range_inclChains hα₁)
  have hB₃ : (singularChains ℤ M).d N (N - 1) α₃
      ∈ LinearMap.range ((inclChains M ((K ∩ L)ᶜ)).f (N - 1)).hom :=
    mem_range_inclChains_of_subset hsub₃ (d_mem_range_inclChains hα₃)
  have hBJ : (singularChains ℤ M).d N (N - 1) j
      ∈ LinearMap.range ((inclChains M ((K ∩ L)ᶜ)).f (N - 1)).hom :=
    mem_range_inclChains_of_subset hsubj (d_mem_range_inclChains hj)
  -- consequently the boundary of `α₂` is supported outside `K ∩ L`
  have hdα₂ : (singularChains ℤ M).d N (N - 1) α₂
      ∈ LinearMap.range ((inclChains M ((K ∩ L)ᶜ)).f (N - 1)).hom := by
    have hzero : (singularChains ℤ M).d N (N - 1) (α₁ + α₂ + α₃ + j) = 0 := by
      rw [← hα, ← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
      simp
    have h0 : (singularChains ℤ M).d N (N - 1) α₁ + (singularChains ℤ M).d N (N - 1) α₂
        + (singularChains ℤ M).d N (N - 1) α₃ + (singularChains ℤ M).d N (N - 1) j = 0 := by
      simpa only [map_add] using hzero
    have hneg : (singularChains ℤ M).d N (N - 1) α₂
        + ((singularChains ℤ M).d N (N - 1) α₁ + (singularChains ℤ M).d N (N - 1) α₃
          + (singularChains ℤ M).d N (N - 1) j) = 0 := by
      calc (singularChains ℤ M).d N (N - 1) α₂
            + ((singularChains ℤ M).d N (N - 1) α₁ + (singularChains ℤ M).d N (N - 1) α₃
              + (singularChains ℤ M).d N (N - 1) j)
          = (singularChains ℤ M).d N (N - 1) α₁ + (singularChains ℤ M).d N (N - 1) α₂
            + (singularChains ℤ M).d N (N - 1) α₃ + (singularChains ℤ M).d N (N - 1) j := by abel
        _ = 0 := h0
    rw [eq_neg_of_add_eq_zero_left hneg]
    exact neg_mem (add_mem (add_mem hB₁ hB₃) hBJ)
  -- the boundary of the descended chain `b'`
  have hdb' : (inclChains M (U ∩ V)).f (N - 1)
      ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).d N (N - 1) b')
      = (singularChains ℤ M).d N (N - 1) α₂ := by
    have hnat := congrArg
      (fun (g : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X N
          ⟶ (singularChains ℤ M).X (N - 1)) => (ModuleCat.Hom.hom g) b')
      ((inclChains M (U ∩ V)).comm N (N - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [← hnat, hb']
  -- so the projection of `b'` to the relative complex of `(U ∩ V, (U ∩ V)∖(K ∩ L))` is a cycle
  have hmem : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d N (N - 1) b'
      ∈ LinearMap.range
          ((inclChains (TopCat.of (U ∩ V : Set M)) (pdTr (U ∩ V) ((K ∩ L)ᶜ))).f (N - 1)).hom :=
    mem_range_inclChains_of_image (N - 1) (by rw [hdb']; exact hdα₂)
  have hmem' : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).d N (N - 1) b'
      ∈ LinearMap.range
          ((inclChains (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V : Set M) (K ∩ L))).f (N - 1)).hom := hmem
  have hcycle : (relChains (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) (K ∩ L))).d N (N - 1)
      (((cokernel.π (inclChains (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) (K ∩ L)))).f N) b') = 0 := by
    show ((cokernel (inclChains (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) (K ∩ L)))).d N (N - 1))
      (((cokernel.π (inclChains (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) (K ∩ L)))).f N) b') = 0
    have hnat := congrArg
      (fun (g : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X N
          ⟶ (cokernel (inclChains (TopCat.of (U ∩ V : Set M))
              (pdRelSub (U ∩ V : Set M) (K ∩ L)))).X (N - 1)) => (ModuleCat.Hom.hom g) b')
      ((cokernel.π (inclChains (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) (K ∩ L)))).comm N (N - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [hnat]
    obtain ⟨y, hy⟩ := hmem'
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero (N - 1) y
  -- the relative cycle
  let γ : (relChains (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V : Set M) (K ∩ L))).cycles N :=
    cycleOf N (((cokernel.π (inclChains (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V : Set M) (K ∩ L)))).f N) b') hcycle
  have hγi : (relChains (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V : Set M) (K ∩ L))).iCycles N γ
      = ((cokernel.π (inclChains (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) (K ∩ L)))).f N).hom b' := iCycles_cycleOf N _ hcycle
  -- the three summands outside `α₂` are killed by the projection to `C_*(M, M∖(K ∩ L))`
  have hkill₁ : ((cokernel.π (inclChains M ((K ∩ L)ᶜ))).f N) α₁ = 0 := by
    obtain ⟨y, hy⟩ := hA₁
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero N y
  have hkill₃ : ((cokernel.π (inclChains M ((K ∩ L)ᶜ))).f N) α₃ = 0 := by
    obtain ⟨y, hy⟩ := hA₃
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero N y
  have hkillJ : ((cokernel.π (inclChains M ((K ∩ L)ᶜ))).f N) j = 0 := by
    obtain ⟨y, hy⟩ := hAJ
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero N y
  have hj0 : ((cokernel.π (inclChains M ((K ∩ L)ᶜ))).f N) (α₁ + α₃ + j) = 0 := by
    rw [map_add, map_add, hkill₁, hkill₃, hkillJ, add_zero, add_zero]
  -- the class of `γ` in `H_N(M, M∖(K ∩ L))` is the local class
  have hξ : (inclChains M (U ∩ V)).f N b'
      = (singularChains ℤ M).iCycles N α - (α₁ + α₃ + j) := by
    rw [hb', hα]
    abel
  have hcl : HomologicalComplex.homologyMap (relChainsMap M (U ∩ V) ((K ∩ L)ᶜ)) N
      ((relChains (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ N γ)
      = relLocClass M N c (K ∩ L) :=
    relCycle_homologyMap_eq_relLocClass c γ hγi hc hξ hj0
  -- the class of `γ` in `H_N(U ∩ V, (U ∩ V)∖(K ∩ L))` is the local fundamental class
  have hKL : K ∩ L ⊆ (U ∩ V : Set M) := fun x hx => ⟨hKU hx.1, hLV hx.2⟩
  have hKLc : IsCompact (K ∩ L) := IsCompact.inter hKc hLc
  have hcov : (U ∩ V : Set M) ∪ (K ∩ L)ᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases h : x ∈ K ∩ L
    · exact Or.inl (hKL h)
    · exact Or.inr h
  have hloc : (relChains (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ N γ
      = localFundClass N c (U ∩ V : Set M) hI (K ∩ L) hKL hKLc := by
    haveI : IsIso (HomologicalComplex.homologyMap (relChainsMap M (U ∩ V) ((K ∩ L)ᶜ)) N) :=
      excision_relChainsMap_isIso M (U ∩ V) ((K ∩ L)ᶜ) hI hKLc.isClosed.isOpen_compl hcov N
    have hspec := localFundClass_spec N c (U ∩ V) hI (K ∩ L) hKL hKLc
    calc (relChains (TopCat.of (U ∩ V : Set M))
          (pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ N γ
        = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∩ V) ((K ∩ L)ᶜ)) N)
            (HomologicalComplex.homologyMap (relChainsMap M (U ∩ V) ((K ∩ L)ᶜ)) N
              ((relChains (TopCat.of (U ∩ V : Set M))
                (pdRelSub (U ∩ V : Set M) (K ∩ L))).homologyπ N γ)) :=
            (IsIso.hom_inv_id_apply _ _).symm
      _ = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∩ V) ((K ∩ L)ᶜ)) N)
            (relLocClass M N c (K ∩ L)) := by rw [hcl]
      _ = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∩ V) ((K ∩ L)ᶜ)) N)
            (HomologicalComplex.homologyMap (relChainsMap M (U ∩ V) ((K ∩ L)ᶜ)) N
              (localFundClass N c (U ∩ V : Set M) hI (K ∩ L) hKL hKLc)) := by rw [hspec]
      _ = localFundClass N c (U ∩ V : Set M) hI (K ∩ L) hKL hKLc := IsIso.hom_inv_id_apply _ _
  exact ⟨b', γ, hb', hγi, hloc⟩

end

end Work.Cohomology
