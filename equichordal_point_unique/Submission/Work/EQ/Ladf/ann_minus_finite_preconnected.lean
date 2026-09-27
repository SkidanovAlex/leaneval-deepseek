import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.Drive.isPreconnected_sdiff_finite
import Submission.Work.EQ.Ladf.isConnected_openAnnulus
import Submission.Work.EQ.Ladf.Ann_subset_closure_openAnnulus

/-! # The closed annulus minus a finite set is preconnected

`Work.EQ.Ann r₁ r₂ = {z : ℂ | r₁ ≤ ‖z‖ ≤ r₂}` is a closed annulus (or a closed disc / the
degenerate set `{0}`) and removing finitely many points from it leaves a preconnected set.

The proof is a closure argument.  The open set
`G = {z : ℂ | max r₁ 0 < ‖z‖ ∧ ‖z‖ < r₂}` is an open annulus (or a punctured/open disc); it is
connected, and by `Work.Drive.isPreconnected_sdiff_finite` (removing a finite set from an open
preconnected subset of a surface preserves preconnectedness) so is `G \ F`.  Moreover
`Ann r₁ r₂` is contained in the closure of `G` (every boundary point is a limit of points of `G`)
and `G \ F ⊆ Ann r₁ r₂ \ F ⊆ closure (G \ F)`, so `IsPreconnected.subset_closure` finishes.
-/

namespace Work.EQ.Ladf

open Set Metric
open scoped Topology

theorem ann_minus_finite_preconnected {r₁ r₂ : ℝ} (hr : r₁ < r₂) {F : Set ℂ} (hF : F.Finite) :
    IsPreconnected (Work.EQ.Ann r₁ r₂ \ F) := by
  rcases le_or_gt r₂ 0 with h2 | h2
  · -- Degenerate case: `Ann r₁ r₂ = {0}`.
    have hA : Work.EQ.Ann r₁ r₂ ⊆ {0} := by
      intro z hz
      simp only [Work.EQ.Ann, Set.mem_ofPred_eq] at hz
      have hn : ‖z‖ = 0 := le_antisymm (le_trans hz.2 h2) (norm_nonneg z)
      simpa using hn
    refine Set.Subsingleton.isPreconnected ?_
    intro x hx y hy
    rw [Set.mem_sdiff] at hx hy
    exact (Set.mem_singleton_iff.mp (hA hx.1)).trans (Set.mem_singleton_iff.mp (hA hy.1)).symm
  · -- Main case: the open annulus `G` is connected and its closure covers `Ann r₁ r₂`.
    have hα0 : 0 ≤ max r₁ 0 := le_max_right _ _
    have hαb : max r₁ 0 < r₂ := max_lt hr h2
    have hopen : IsOpen {z : ℂ | max r₁ 0 < ‖z‖ ∧ ‖z‖ < r₂} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hGpre : IsPreconnected ({z : ℂ | max r₁ 0 < ‖z‖ ∧ ‖z‖ < r₂} \ F) :=
      Work.Drive.isPreconnected_sdiff_finite hopen
        (isConnected_openAnnulus hα0 hαb).isPreconnected F hF
    refine hGpre.subset_closure ?_ ?_
    · rintro z ⟨hzG, hzF⟩
      refine ⟨?_, hzF⟩
      simp only [Work.EQ.Ann, Set.mem_ofPred_eq]
      exact ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hzG.1), le_of_lt hzG.2⟩
    · rintro z ⟨hzA, hzF⟩
      have hzc : z ∈ closure {z : ℂ | max r₁ 0 < ‖z‖ ∧ ‖z‖ < r₂} :=
        Ann_subset_closure_openAnnulus hr h2 hzA
      have hop : IsOpen (Fᶜ : Set ℂ) := hF.isClosed.isOpen_compl
      have h := IsOpen.closure_inter hop ⟨hzc, hzF⟩
      simpa [Set.sdiff_eq] using h

end Work.EQ.Ladf
