/-
  S51 / `CoreLT_succ`: the Σ-case and the `cfs`-union compatibility.

  Two elementary but load-bearing steps of the `CoreLT_succ` assembly:

  * **Σ-case transfer.**  If a cell `κ` has base image inside `π_n(S)`, then its trace against
    `π_{n+1}(T)` (for an absolute stratum `T`) agrees with its trace against the `π_{n+1}`-image of
    the fibre product `Z_{T,S}` of `CoreStep.fibreProd_sigma_lem`.  Hence the compatibility clause
    that the inner `CoreLT n K` call provides for the `X`-member `Z_{T,S}` transfers to the piece
    `T` itself.

  * **`cfs`-union compatibility.**  If the `π_{n+1}`-image of a piece over a base cell `C` is a
    union of members of the level family `cfs C tt`, then every member of `cfs C tt` is either
    contained in that image or disjoint from it — purely from the pairwise disjointness of the
    cylindrical decomposition.  This is what makes the G-case compatibility independent of any
    topology (`hgraph`/`hint` are not needed).
-/
import Mathlib
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.CoreStep.FibreEndDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E

/-! ## 1. The Σ-case transfer -/

/-- If `A = B ∩ U` and `κ ⊆ U`, then the trace of `κ` against `A` and against `B` agree, so the
compatibility disjunction transfers. -/
theorem subset_or_disjoint_of_eq_inter {n : ℕ} {A B U : Set (Fin (n + 1) → ℝ)}
    {κ : Set (Fin (n + 1) → ℝ)} (hκ : κ ⊆ U) (hAB : A = B ∩ U) :
    (κ ⊆ A ∨ Disjoint κ A) → κ ⊆ B ∨ Disjoint κ B := by
  rintro (h | h)
  · left
    intro y hy
    exact (hAB ▸ h hy).1
  · right
    rw [Set.disjoint_left] at h ⊢
    intro y hy hyB
    exact h hy (by rw [hAB]; exact ⟨hyB, hκ hy⟩)

/-- **Σ-case transfer.**  `Z` is the fibre product of the piece `T` (an absolute stratum in the
`(n+1)+m` frame) with the `SemiPf` set `S : SemiPf (n + s)`, as produced by
`CoreStep.fibreProd_sigma_lem`.  If `κ`'s base image lies inside `π_n(S)`, then the compatibility
of `κ` with the `π_{n+1}`-image of `Z` transfers to the piece `T`. -/
theorem compat_of_fibreProd {n m s : ℕ}
    (T : WilkiesDesign.E.Stratum 0 ((n + 1) + m)) (S : WilkiesDesign.E.SemiPf (n + s))
    (Z : WilkiesDesign.E.SemiPf ((n + 1) + (m + s)))
    (hZ : WilkiesDesign.E.projFirst (n + 1) (m + s) '' Z.set =
      WilkiesDesign.E.projFirst (n + 1) m '' MainDesign.absSet T ∩
        {y | Fin.init y ∈ WilkiesDesign.E.projFirst n s '' S.set})
    {κ : Set (Fin (n + 1) → ℝ)}
    (hκ : Fin.init '' κ ⊆ WilkiesDesign.E.projFirst n s '' S.set)
    (h : κ ⊆ WilkiesDesign.E.projFirst (n + 1) (m + s) '' Z.set ∨
      Disjoint κ (WilkiesDesign.E.projFirst (n + 1) (m + s) '' Z.set)) :
    κ ⊆ WilkiesDesign.E.projFirst (n + 1) m '' MainDesign.absSet T ∨
      Disjoint κ (WilkiesDesign.E.projFirst (n + 1) m '' MainDesign.absSet T) := by
  refine subset_or_disjoint_of_eq_inter ?_ hZ h
  intro y hy
  exact hκ ⟨y, hy, rfl⟩

/-! ## 2. The `cfs`-union compatibility -/

/-- Pairwise disjointness of a cylindrical decomposition (`IsCylDecompOn`). -/
theorem pairwiseDisjoint_of_isCylDecompOn {N : ℕ} {A : Set (Fin N → ℝ)}
    {C : Finset (Set (Fin N → ℝ))} (h : WilkiesDesign.E.IsCylDecompOn N A C) :
    (C : Set (Set (Fin N → ℝ))).PairwiseDisjoint id := by
  cases N with
  | zero => rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [Set.pairwiseDisjoint_iff] <;> simp
  | succ N => exact h.2.1

/-- **`cfs`-union compatibility.**  If `A` is a union of members of the level family
`cfs C tt` (the members being listed by a Finset `S ⊆ cfs C tt`), then every `κ ∈ cfs C tt` is
either contained in `A` or disjoint from `A`. -/
theorem cell_subset_or_disjoint_of_union {p q : ℕ} {C : Set (Fin p → ℝ)}
    {tt : Fin q → (Fin p → ℝ) → ℝ} {A : Set (Fin (p + 1) → ℝ)}
    (hdec : WilkiesDesign.E.IsCylDecompOn (p + 1) (cyl C) (cfs C tt))
    (S : Finset (Set (Fin (p + 1) → ℝ))) (hS : S ⊆ cfs C tt)
    (hA : A = ⋃₀ (S : Set (Set (Fin (p + 1) → ℝ)))) :
    ∀ κ ∈ cfs C tt, κ ⊆ A ∨ Disjoint κ A := by
  intro κ hκ
  by_cases hsub : κ ⊆ A
  · exact Or.inl hsub
  · refine Or.inr ?_
    rw [Set.disjoint_left]
    intro y hy hyA
    rw [hA, Set.mem_sUnion] at hyA
    obtain ⟨κ', hκ', hyκ'⟩ := hyA
    have heq : κ' = κ :=
      (Set.pairwiseDisjoint_iff.mp (pairwiseDisjoint_of_isCylDecompOn hdec)) (hS hκ') hκ
        ⟨y, hyκ', hy⟩
    exact hsub (fun z hz => by
      rw [hA]
      exact Set.mem_sUnion.mpr ⟨κ', hκ', heq ▸ hz⟩)

end Work.WilE7.coreLT_succ
