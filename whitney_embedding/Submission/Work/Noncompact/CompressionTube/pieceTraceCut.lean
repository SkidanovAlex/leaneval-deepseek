import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# Cutting a piece at its last visit to a region

The two-lane ray is built piece by piece, and the trace that a piece leaves in the *next* corridor
has to be a single terminal sub-arc of the piece; then the next region is obtained from the
corridor by removing a half-open arc, and `isPreconnected_sdiff_Ico_image_arc` keeps it
preconnected with the new seed kept.

This file contains the elementary real-variable input.  For a continuous path `α : ℝ → M` and an
open set `U` there is a parameter `t` such that everything after `t` lies in `U`, and no parameter
outside `U` in `[0,1]` is bigger than `t`: the "last exit" from `U`.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- **The last exit from an open set.**  For a continuous path `α` and an open set `U` there is
`t ∈ [0,1]` which upper bounds all parameters in `[0,1]` at which `α` is outside `U`, and such
that `α` lies in `U` after `t`. -/
theorem exists_last_exit {α : ℝ → M} (hα : Continuous α) {U : Set M} (hU : IsOpen U) :
    ∃ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 ∧
      (∀ s : ℝ, t < s → s ≤ 1 → α s ∈ U) ∧
      (∀ t' : ℝ, t' ∈ Set.Icc (0:ℝ) 1 → α t' ∉ U → t' ≤ t) := by
  set S : Set ℝ := Set.Icc (0:ℝ) 1 ∩ α ⁻¹' Uᶜ with hSdef
  have hSclosed : IsClosed S :=
    isClosed_Icc.inter (hU.isClosed_compl.preimage hα)
  have hSbdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
  by_cases hne : S.Nonempty
  · have hmem : sSup S ∈ S := hSclosed.csSup_mem hne hSbdd
    refine ⟨sSup S, hmem.1, ?_, ?_⟩
    · intro s hts hs1
      by_contra hcon
      have hsS : s ∈ S := ⟨⟨le_trans hmem.1.1 hts.le, hs1⟩, hcon⟩
      exact absurd (le_csSup hSbdd hsS) (not_le.mpr hts)
    · intro t' ht' ht'U
      exact le_csSup hSbdd ⟨ht', ht'U⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hSdef] at hne
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · intro s hs0 hs1
      by_contra hcon
      exact Set.eq_empty_iff_forall_notMem.mp hne s ⟨⟨le_of_lt hs0, hs1⟩, hcon⟩
    · intro t' ht' ht'U
      exact absurd ⟨ht', ht'U⟩ (Set.eq_empty_iff_forall_notMem.mp hne t')

end Work.Noncompact.CompressionTube
