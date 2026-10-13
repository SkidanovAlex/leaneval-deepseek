import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.DimAPI.isCylDecompOn_liftFam
import Submission.Work.WilE7.Endgame.gr_inter_cyl_closed
import Submission.Work.WilE7.Endgame.preconnected_subset_or_disjoint_of_closed_traces

namespace Work.WilE7.Endgame

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)

/-- **Elementary topology step (open/closed form).**  Let `K`, `A` be subsets of a topological
space and let `κ ⊆ K` be preconnected.  If `A ∩ K` is open in the subspace `K` and `κ` avoids the
part of the boundary of `A` lying in `K` (that is `κ ∩ (closure A \ A) ∩ K = ∅`), then `κ` is
contained in `A` or disjoint from `A`.

Indeed, choose an ambient open set `V` with `V ∩ K = A ∩ K`; then `V` and `(closure A)ᶜ` are
disjoint on `κ` and cover `κ`, so preconnectedness puts `κ` inside one of them.  Either alternative
gives the conclusion because `κ ⊆ K`. -/
lemma preconnected_subset_or_disjoint_of_open_subtype {X : Type*} [TopologicalSpace X]
    {K A κ : Set X} (hκ : IsPreconnected κ) (hκK : κ ⊆ K)
    (hAopen : IsOpen {z : ↥K | (z : X) ∈ A})
    (hdisj : Disjoint κ ((closure A \ A) ∩ K)) :
    κ ⊆ A ∨ Disjoint κ A := by
  obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp hAopen
  have hVA : κ ∩ V ⊆ A := by
    rintro z ⟨hzκ, hzV⟩
    have hmem : (⟨z, hκK hzκ⟩ : ↥K) ∈ Subtype.val ⁻¹' V := hzV
    rw [hVeq] at hmem
    exact hmem
  have hcover : κ ⊆ V ∪ (closure A)ᶜ := by
    intro z hzκ
    by_cases hzA : z ∈ A
    · left
      have hmem : (⟨z, hκK hzκ⟩ : ↥K) ∈ ({z : ↥K | (z : X) ∈ A}) := hzA
      rwa [← hVeq] at hmem
    · right
      rw [Set.mem_compl_iff]
      intro hzcl
      exact (Set.disjoint_left.mp hdisj hzκ) ⟨⟨hzcl, hzA⟩, hκK hzκ⟩
  have hdisj2 : κ ∩ (V ∩ (closure A)ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzκ, hzV, hzcl⟩
    exact hzcl (subset_closure (hVA ⟨hzκ, hzV⟩))
  rcases (isPreconnected_iff_subset_of_disjoint.mp hκ) V (closure A)ᶜ hVopen
      isClosed_closure.isOpen_compl hcover hdisj2 with hsub | hsub
  · exact Or.inl fun z hz => hVA ⟨hz, hsub hz⟩
  · exact Or.inr (Set.disjoint_left.mpr fun z hzκ hzA => hsub hzκ (subset_closure hzA))

theorem cell_compat_of_levelGraphs {p r : ℕ} {C : Set (Fin p → ℝ)}
    {C' : Finset (Set (Fin (p + 1) → ℝ))}
    (hC' : IsCylDecompOn (p + 1) (Work.WilE7.cyl C) C')
    (k : Fin r → ℕ) (f : (t : Fin r) → Fin (k t) → (Fin p → ℝ) → ℝ)
    (hf : ∀ t j, ContinuousOn (f t j) C)
    (hcompat : ∀ κ ∈ C', ∀ t : Fin r, κ ⊆ (⋃ j, Work.WilE7.gr C (f t j)) ∨
      Disjoint κ (⋃ j, Work.WilE7.gr C (f t j)))
    (A : Set (Fin (p + 1) → ℝ))
    (hAopen : IsOpen {z : ↥(Work.WilE7.cyl C) | (z : Fin (p + 1) → ℝ) ∈ A})
    (hgraph : ∀ t j, Work.WilE7.gr C (f t j) ⊆ A ∨ Disjoint (Work.WilE7.gr C (f t j)) A)
    (hbound : (closure A \ A) ∩ Work.WilE7.cyl C ⊆ ⋃ t, ⋃ j, Work.WilE7.gr C (f t j)) :
    ∀ κ ∈ C', κ ⊆ A ∨ Disjoint κ A := by
  intro κ hκ
  -- `κ` is a nonempty cell of the decomposition, hence preconnected and inside `cyl C`.
  have hcell : IsCell (p + 1) κ := Work.WilE7.DimAPI.liftFamAux_isCell_of_mem hC' κ hκ
  have hpre : IsPreconnected κ := Work.WilE7.isPreconnected_of_isCell hcell
  have hsubK : κ ⊆ Work.WilE7.cyl C := hC'.2.2.1 ▸ Set.subset_sUnion_of_mem hκ
  by_cases hfr : Disjoint κ ((closure A \ A) ∩ Work.WilE7.cyl C)
  · -- `κ` avoids the boundary of `A` inside the cylinder: `hAopen` + preconnectedness.
    exact preconnected_subset_or_disjoint_of_open_subtype hpre hsubK hAopen hfr
  · -- `κ` meets the boundary; `hbound` then puts it inside a level-graph union, and `hcompat`
    -- upgrades this to `κ ⊆ ⋃_j gr C (f t j)` for that `t`.
    rw [Set.not_disjoint_iff] at hfr
    obtain ⟨z, hzκ, hz⟩ := hfr
    have hzU : z ∈ ⋃ t, ⋃ j, Work.WilE7.gr C (f t j) := hbound hz
    rw [Set.mem_iUnion] at hzU
    obtain ⟨t, ht⟩ := hzU
    have hsubgr : κ ⊆ ⋃ j, Work.WilE7.gr C (f t j) := by
      rcases hcompat κ hκ t with h | h
      · exact h
      · exact absurd ht (Set.disjoint_left.mp h hzκ)
    -- Each level graph is cut out of the cylinder by a closed set of `ℝ^{p+1}`.
    have hFex : ∀ j : Fin (k t), ∃ F : Set (Fin (p + 1) → ℝ), IsClosed F ∧
        F ∩ Work.WilE7.cyl C = Work.WilE7.gr C (f t j) ∩ Work.WilE7.cyl C :=
      fun j => gr_inter_cyl_closed (hf t j)
    let F : Fin (k t) → Set (Fin (p + 1) → ℝ) := fun j => Classical.choose (hFex j)
    have hFc : ∀ j, IsClosed (F j) := fun j => (Classical.choose_spec (hFex j)).1
    have hFtr : ∀ j, F j ∩ Work.WilE7.cyl C =
        (fun j => Work.WilE7.gr C (f t j)) j ∩ Work.WilE7.cyl C :=
      fun j => (Classical.choose_spec (hFex j)).2
    -- The traces of the two closed pieces `{j | gr ⊆ A}` resp. `{j | gr ∩ A = ∅}` separate `κ`.
    exact preconnected_subset_or_disjoint_of_closed_traces F (fun j => Work.WilE7.gr C (f t j))
      hpre hsubK hFc hFtr hsubgr (fun j => hgraph t j)

end

end Work.WilE7.Endgame
