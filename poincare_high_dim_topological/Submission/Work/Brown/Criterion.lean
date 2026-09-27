/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Brown
-/
import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Brown.Basic
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Brown.Cover.exists_mem_of_compact_subset_iUnion
import Submission.Work.Brown.Cover.t2Space_of_monotone_open_cover
import Submission.Work.Brown.Cover.secondCountableTopology_of_monotone_open_cover
import Submission.Work.Brown.Cover.locallyCompactSpace_of_monotone_open_cover
import Submission.Work.Brown.Cover.sigmaCompactSpace_of_monotone_open_cover
import Submission.Work.Brown.Main.nonempty_homeomorph_of_compact_subsets_in_openCell

/-!
# Brown's theorem in "criterion" form

The form of Brown's monotone union theorem used by the Poincaré assembly
(`Work.Cells.Connell.two_cells_sphere`, blueprint §3 C4) is the *criterion* form:
a locally compact, second countable space in which every compact subset is contained in an open
`n`-cell is itself homeomorphic to `ℝⁿ` (`Work.Cells.Connell.BrownCriterion`).

Here we prove it from `Work.Brown.Main.nonempty_homeomorph_of_compact_subsets_in_openCell`,
which states it for `n ≥ 1` with the separation hypothesis `[T2Space W]` unbundled (that
hypothesis is derivable: two points of `W` lie in a common open cell, and inside that cell they
are separated by opens of the cell, which are open in `W`).

The case `n = 0` is handled separately: there `ℝ⁰` is a point and the criterion forces the space
to be a point.
-/

open Set Function Metric

namespace Work.Brown

/-- Two points of a space satisfying the *criterion* hypothesis lie in a common open cell; since
an open cell is Hausdorff, the space is Hausdorff. -/
theorem t2Space_of_compact_subsets_in_openCell {n : ℕ} {W : Type*} [TopologicalSpace W]
    (h : ∀ K : Set W, IsCompact K → ∃ V : Set W, PL.IsOpenCell n V ∧ K ⊆ V) : T2Space W := by
  refine ⟨?_⟩
  intro x y hxy
  have hfin : ({x, y} : Set W).Finite := (Set.finite_singleton y).insert x
  have hc : IsCompact ({x, y} : Set W) := hfin.isCompact
  obtain ⟨V, hVcell, hxVyV⟩ := h {x, y} hc
  have hVcell' : IsOpen V ∧ Nonempty (↥V ≃ₜ PL.E n) := hVcell
  obtain ⟨hVo, ⟨e⟩⟩ := hVcell'
  haveI : T2Space ↥V := e.isEmbedding.t2Space
  have hxV : x ∈ V := hxVyV (by simp)
  have hyV : y ∈ V := hxVyV (by simp)
  have hne : (⟨x, hxV⟩ : ↥V) ≠ ⟨y, hyV⟩ := fun hh ↦ hxy (Subtype.ext_iff.mp hh)
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hne
  refine ⟨Subtype.val '' u, Subtype.val '' v, hVo.isOpenMap_subtype_val u hu,
    hVo.isOpenMap_subtype_val v hv, ⟨⟨x, hxV⟩, hxu, rfl⟩, ⟨⟨y, hyV⟩, hyv, rfl⟩, ?_⟩
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.image_inter Subtype.val_injective,
    Set.disjoint_iff_inter_eq_empty.mp huv, Set.image_empty]

/-- **Brown's criterion form**, for `n ≥ 1`: a locally compact, second countable space in which
every compact subset lies in an open `n`-cell is homeomorphic to `ℝⁿ`. -/
theorem nonempty_homeomorph_of_compact_subsets_in_openCell' {n : ℕ} (hn : 1 ≤ n) {W : Type*}
    [TopologicalSpace W] [LocallyCompactSpace W] [SecondCountableTopology W]
    (h : ∀ K : Set W, IsCompact K → ∃ V : Set W, PL.IsOpenCell n V ∧ K ⊆ V) :
    Nonempty (W ≃ₜ PL.E n) := by
  haveI := t2Space_of_compact_subsets_in_openCell h
  exact Main.nonempty_homeomorph_of_compact_subsets_in_openCell hn h

/-- **Brown's criterion form**, `n = 0`: there `ℝ⁰` is a point, and the criterion forces the
space to be a point. -/
theorem nonempty_homeomorph_of_compact_subsets_in_openCell_zero {W : Type*} [TopologicalSpace W]
    (h : ∀ K : Set W, IsCompact K → ∃ V : Set W, PL.IsOpenCell 0 V ∧ K ⊆ V) :
    Nonempty (W ≃ₜ PL.E 0) := by
  -- `W` is nonempty: apply the criterion to `∅`
  obtain ⟨U₀, hcell₀, -⟩ := h (∅ : Set W) isCompact_empty
  have hcell₀' : IsOpen U₀ ∧ Nonempty (↥U₀ ≃ₜ PL.E 0) := hcell₀
  obtain ⟨-, ⟨e₀⟩⟩ := hcell₀'
  haveI : Nonempty W := ⟨(e₀.symm 0 : ↥U₀).1⟩
  -- a point together with an open point-neighbourhood
  obtain ⟨U, hcellU, hx₀U⟩ := h ({Classical.arbitrary W} : Set W) isCompact_singleton
  have hcellU' : IsOpen U ∧ Nonempty (↥U ≃ₜ PL.E 0) := hcellU
  obtain ⟨-, ⟨e⟩⟩ := hcellU'
  -- every point lies in `U`: the criterion puts `{x₀, y}` inside a point-cell
  have hUuniv : U = Set.univ := by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    have hfin : ({Classical.arbitrary W, y} : Set W).Finite := (Set.finite_singleton y).insert _
    have hc : IsCompact ({Classical.arbitrary W, y} : Set W) := hfin.isCompact
    obtain ⟨V, hcellV, hx₀yV⟩ := h {Classical.arbitrary W, y} hc
    have hcellV' : IsOpen V ∧ Nonempty (↥V ≃ₜ PL.E 0) := hcellV
    obtain ⟨-, ⟨eV⟩⟩ := hcellV'
    have hx₀V : Classical.arbitrary W ∈ V := hx₀yV (by simp)
    have hyV : y ∈ V := hx₀yV (by simp)
    have hsub : Subsingleton ↥V :=
      ⟨fun a b ↦ eV.injective (Subsingleton.elim (eV a) (eV b))⟩
    have hEq : (⟨Classical.arbitrary W, hx₀V⟩ : ↥V) = ⟨y, hyV⟩ := hsub.elim _ _
    have hy : y = Classical.arbitrary W := (Subtype.ext_iff.mp hEq).symm
    rw [hy]
    exact hx₀U (by simp)
  exact ⟨(Homeomorph.Set.univ W).symm.trans (Homeomorph.setCongr hUuniv.symm) |>.trans e⟩

/-- **Brown's theorem, criterion form** (`Work.Cells.Connell.BrownCriterion`): a locally compact,
second countable space in which every compact subset lies in an open `n`-cell is an open
`n`-cell, i.e. is homeomorphic to `ℝⁿ`. -/
theorem brownCriterion (n : ℕ) : Work.Cells.Connell.BrownCriterion n := by
  intro W _ _ _ h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact nonempty_homeomorph_of_compact_subsets_in_openCell_zero fun K hK ↦ by
      obtain ⟨V, -, hKV, hVcell⟩ := h K hK
      exact ⟨V, hVcell, hKV⟩
  · exact nonempty_homeomorph_of_compact_subsets_in_openCell' hn fun K hK ↦ by
      obtain ⟨V, -, hKV, hVcell⟩ := h K hK
      exact ⟨V, hVcell, hKV⟩

/-- **Brown's monotone union theorem via the criterion form.**  Every compact subset of `X`
lies in some member of the increasing open cell cover (`Cover.exists_mem_of_compact_subset_iUnion`),
so the criterion form applies.  This is an alternative route to `Work.Brown.brown_monotone_union`
(`Main.lean`), which instead uses the collapse-sequence engine. -/
theorem brown_monotone_union_via_criterion {n : ℕ} {X : Type*} [TopologicalSpace X]
    {U : ℕ → Set X} (hU : MonotoneOpenCellCover n U) : Nonempty (X ≃ₜ PL.E n) := by
  obtain ⟨hopen, hmono, hcell, hcover⟩ := hU
  have hcr : ∀ K : Set X, IsCompact K → ∃ V : Set X, PL.IsOpenCell n V ∧ K ⊆ V := fun K hK ↦ by
    obtain ⟨k, hk⟩ := Cover.exists_mem_of_compact_subset_iUnion hopen hmono hK
      (by rw [hcover]; exact subset_univ K)
    exact ⟨U k, hcell k, hk⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact nonempty_homeomorph_of_compact_subsets_in_openCell_zero hcr
  · haveI : T2Space X := t2Space_of_compact_subsets_in_openCell hcr
    haveI : SecondCountableTopology X :=
      Cover.secondCountableTopology_of_monotone_open_cover hopen hcover fun k ↦ by
        obtain ⟨-, ⟨e⟩⟩ := hcell k
        exact e.secondCountableTopology
    haveI : LocallyCompactSpace X :=
      Cover.locallyCompactSpace_of_monotone_open_cover hopen hcover fun k ↦ by
        obtain ⟨-, ⟨e⟩⟩ := hcell k
        exact e.locallyCompactSpace_iff.mpr inferInstance
    exact nonempty_homeomorph_of_compact_subsets_in_openCell' hn hcr

end Work.Brown
