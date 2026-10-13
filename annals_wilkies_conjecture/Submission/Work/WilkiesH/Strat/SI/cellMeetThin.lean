import Mathlib
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Strat.rpc_cell_frontier
import Submission.Work.WilkiesH.Omega.semialgebraic_mem_Omega
import Submission.Work.WilG5.Basic

namespace Work.WilkiesH.Strat.SI

open WilkiesDesign WilkiesConjecture

theorem cellMeetThin {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {n μ FD FE DD DE : ℕ} {V : Set (Fin n → ℝ)} (hVsem : WilkiesConjecture.IsSemialgebraic V) (hVdim : WilkiesDesign.DimLE V μ) {CD : Finset (Set (Fin n → ℝ))} (hCD : WilkiesDesign.IsCylDecomp n CD) {D E : Set (Fin n → ℝ)} (hD : D ∈ CD) (hE : E ∈ CD) (hne : D ≠ E) (hDV : D ⊆ V) (hEV : E ⊆ V) (hDΩ : D ∈ S.Ω FD DD n) (hEΩ : E ∈ S.Ω FE DE n) : WilkiesDesign.DimLE (D ∩ closure E) (μ - 1) := by
  classical
  -- `V` is semialgebraic, hence `Ω`-definable: it is the `V` of the cell-frontier lemma.
  obtain ⟨FV, DV, hVΩ⟩ := Work.WilkiesH.Omega.semialgebraic_mem_Omega S hVsem
  rcases n with _ | n
  · -- in `ℝ⁰` the dimension bound is vacuous
    intro e
    exact Fin.elim0 (e ⟨0, by omega⟩)
  · -- the cell-frontier lemma for the family `V`, in format `max FD FV`
    obtain ⟨a, pm, hcf⟩ := Work.WilkiesH.Strat.RPC.frontierThin (S := S) hcd (max FD FV) (n + 1)
    -- distinct cells of a cylindrical decomposition are disjoint
    have hdisj : Disjoint D E := hCD.2.1 hD hE hne
    have hEsub : E ⊆ V \ D := fun x hx =>
      ⟨hEV hx, fun hxD => Set.disjoint_left.mp hdisj hxD hx⟩
    -- pad the `Ω`-formats to a common one
    have hV2 : V ∈ S.Ω (max FD FV) DV (n + 1) :=
      Work.WilG5.mem_mono hVΩ _ _ (le_max_right _ _) le_rfl
    have hD2 : D ∈ S.Ω (max FD FV) (max DD DV) (n + 1) :=
      Work.WilG5.mem_mono hDΩ _ _ (le_max_left _ _) (le_max_left _ _)
    have hcell : WilkiesDesign.IsCell (n + 1) D := (hCD.1 D hD).1
    have hDne : D.Nonempty := (hCD.1 D hD).2
    obtain ⟨W, -, -, hWdim, hWcov⟩ :=
      hcf μ (max DD DV) DV V D hV2 hVsem hVdim hD2 hcell hDne hDV
    -- `D ∩ closure E ⊆ D ∩ closure (V \ D) ⊆ W`
    refine Work.WilkiesH.dimLE_of_subset hWdim ?_
    rintro x ⟨hxD, hxclE⟩
    exact hWcov ⟨hxD, (closure_mono hEsub) hxclE⟩

end Work.WilkiesH.Strat.SI
