import Mathlib
import Submission.Work.BW.HilbSerreDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped Pointwise

theorem isGrading_quoPiece {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (MR N) M] [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
    (x : Fin (N + 1) × Fin 2) (hg : IsGrading N piece) :
    IsGrading N (HilbSerre.quoPiece N M piece x) := by
  classical
  -- `X x • ⊤` is a *graded* submodule of `M`: it is the sum of its intersections with the
  -- graded pieces of `piece`.
  have hgrad : (⨆ u, piece u ⊓ (HilbSerre.Xsub N M x).restrictScalars ℂ) =
      (HilbSerre.Xsub N M x).restrictScalars ℂ := by
    refine le_antisymm (iSup_le fun u => inf_le_right) ?_
    intro y hy
    have hy' : y ∈ HilbSerre.Xsub N M x := hy
    rw [HilbSerre.Xsub] at hy'
    obtain ⟨m, -, hmy⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists y (MvPolynomial.X x)
        (⊤ : Submodule (MR N) M)).mp hy'
    obtain ⟨f, hfmem, hfsum⟩ :=
      (Submodule.mem_iSup_iff_exists_finsupp piece m).mp
        (by rw [hg.isInternal.submodule_iSup_eq_top]; trivial)
    have hfs : f.sum (fun _ z => z) = ∑ u ∈ f.support, f u := rfl
    rw [← hmy, ← hfsum, hfs, Finset.smul_sum]
    refine Submodule.sum_mem _ fun u _ => ?_
    refine Submodule.mem_iSup_of_mem (u + wZ N x) ⟨hg.smul_mem x u (hfmem u), ?_⟩
    have : (MvPolynomial.X x : MR N) • (f u) ∈ HilbSerre.Xsub N M x := by
      rw [HilbSerre.Xsub]
      exact Submodule.smul_mem_pointwise_smul (f u) (MvPolynomial.X x)
        (⊤ : Submodule (MR N) M) trivial
    exact this
  refine ⟨?_, ?_, ?_⟩
  · -- the images of the graded pieces form an internal direct sum
    change DirectSum.IsInternal (fun u => (piece u).map
      (Submodule.mkQ (HilbSerre.Xsub N M x) : M →ₗ[ℂ] (M ⧸ HilbSerre.Xsub N M x)))
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (fun u => (piece u).map
      (Submodule.mkQ (HilbSerre.Xsub N M x) : M →ₗ[ℂ] (M ⧸ HilbSerre.Xsub N M x)))).mpr
      ⟨?_, ?_⟩
    · refine (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (fun u => (piece u).map
        (Submodule.mkQ (HilbSerre.Xsub N M x) : M →ₗ[ℂ] (M ⧸ HilbSerre.Xsub N M x)))).mpr ?_
      intro s v hv hv0 i hi
      -- lift the `v j` to elements of the graded pieces
      have hchoice : ∀ j : Fin (N + 1) →₀ ℤ, ∃ a : M, a ∈ piece j ∧
          (j ∈ s → (Submodule.mkQ (HilbSerre.Xsub N M x)
            : M →ₗ[ℂ] (M ⧸ HilbSerre.Xsub N M x)) a = v j) := by
        intro j
        by_cases hj : j ∈ s
        · obtain ⟨a, ha, hae⟩ := Submodule.mem_map.mp (hv j hj)
          exact ⟨a, ha, fun _ => hae⟩
        · exact ⟨0, (piece j).zero_mem, fun h => absurd h hj⟩
      choose a ha_mem ha_eq using hchoice
      -- the associated sum lies in the quotienting submodule
      have hsum0 : (Submodule.mkQ (HilbSerre.Xsub N M x)
          : M →ₗ[ℂ] (M ⧸ HilbSerre.Xsub N M x)) (∑ j ∈ s, a j) = 0 := by
        rw [map_sum, Finset.sum_congr rfl (fun j hj => ha_eq j hj), hv0]
      have hxX : ∑ j ∈ s, a j ∈ HilbSerre.Xsub N M x :=
        (Submodule.Quotient.mk_eq_zero (p := HilbSerre.Xsub N M x)).mp hsum0
      -- hence it has a `piece`-decomposition whose components lie in `X x • ⊤`
      have hx' : ∑ j ∈ s, a j ∈ ⨆ u, piece u ⊓ (HilbSerre.Xsub N M x).restrictScalars ℂ := by
        rw [hgrad]; exact hxX
      obtain ⟨g, hgmem, hgsum⟩ :=
        (Submodule.mem_iSup_iff_exists_finsupp
          (fun u => piece u ⊓ (HilbSerre.Xsub N M x).restrictScalars ℂ) (∑ j ∈ s, a j)).mp hx'
      -- uniqueness of the decomposition into graded pieces
      have huniq := (iSupIndep_iff_finsetSum_eq_imp_eq piece).mp hg.isInternal.submodule_iSupIndep
      have hmem : ∀ k ∈ s ∪ g.support,
          (if k ∈ s then a k else 0) ∈ piece k ∧ g k ∈ piece k := by
        intro k _
        refine ⟨?_, (hgmem k).1⟩
        by_cases hk : k ∈ s
        · rw [ite_eq_left hk]; exact ha_mem k
        · rw [ite_eq_right hk]; exact (piece k).zero_mem
      have hsums : ∑ k ∈ s ∪ g.support, (if k ∈ s then a k else 0) =
          ∑ k ∈ s ∪ g.support, g k := by
        have h1 : ∑ k ∈ s ∪ g.support, (if k ∈ s then a k else 0) = ∑ k ∈ s, a k := by
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left]
        have h2 : ∑ k ∈ s ∪ g.support, g k = ∑ k ∈ g.support, g k :=
          (Finset.sum_subset Finset.subset_union_right
            (fun k _ hk => Finsupp.notMem_support_iff.mp hk)).symm
        rw [h1, h2]
        exact hgsum.symm
      have heq := huniq (s ∪ g.support) (fun k => if k ∈ s then a k else 0) g hmem hsums
      have hai : a i = g i := by
        have h := heq i (Finset.mem_union_left g.support hi)
        rwa [ite_eq_left hi] at h
      have haiX : a i ∈ HilbSerre.Xsub N M x := by
        rw [hai]; exact (hgmem i).2
      rw [← ha_eq i hi]
      exact (Submodule.Quotient.mk_eq_zero (p := HilbSerre.Xsub N M x)).mpr haiX
    · rw [← Submodule.map_iSup, hg.isInternal.submodule_iSup_eq_top, Submodule.map_top]
      exact Submodule.range_mkQ ((HilbSerre.Xsub N M x).restrictScalars ℂ)
  · -- multiplication by a variable shifts the grading
    intro v u m hm
    rw [HilbSerre.quoPiece] at hm
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hm
    rw [HilbSerre.quoPiece]
    refine Submodule.mem_map.mpr ⟨(MvPolynomial.X v : MR N) • a, hg.smul_mem v u ha, ?_⟩
    exact (Submodule.mkQ (HilbSerre.Xsub N M x)).map_smul (MvPolynomial.X v) a
  · -- pieces of negative multidegree vanish
    intro u hu
    rw [HilbSerre.quoPiece, hg.eq_bot_of_neg u hu, Submodule.map_bot]

end Work.BW
