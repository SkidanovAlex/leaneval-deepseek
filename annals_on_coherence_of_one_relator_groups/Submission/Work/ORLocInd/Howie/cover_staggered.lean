/-
# The lifted presentation of the cyclic cover is staggered (Howie 2000, Case 1)

Howie's Case 1 (`Submission/Work/ORLocInd/Howie/CoverPresentation.lean`,
`coverPresentation.lean`) lifts a staggered groupoid presentation `P` of a graph `Γ`, together with
a labelling `L` which vanishes on the relators, to the cyclic cover `Γ̃`: the relators of the lifted
presentation are the closed paths `coverPath P L hrel i n` (the lift of `P.path i` starting at the
level `n`), indexed by `(i, n)` with the lexicographic order, and the code of an unoriented edge of
the cover is

    `coverEdgeOf P L τ f = (ω f.hom, f.left.level + τ f.hom)`,

where `τ` is a section of the level cocycle.

This file proves that the lifted presentation is staggered again: for `(i, m) < (j, n)` in the
lexicographic order on `P.ι × ℤ` (i.e. for `i < j`, or `i = j` and `m < n`), the lifted relator
`(i, m)` has strictly smaller greatest and least edges than `(j, n)`.

The proof is a comparison of the *lists of codes* of the two relators
(`coverCodeList P L τ (P.path i) m = (coverCodeList P L τ (P.path i) 0).map (codeShift P m)`,
`Work.ORLocInd.Howie.coverCodeList_shift`), whose maxima and minima are the `pathMax`/`pathMin` of
the relators (`pathMax_eq_maximum`, `pathMin_eq_minimum`,
`Work.ORLocInd.Howie.coverPath_arrowList_coverEdgeOf`).  In the case `i < j` the codes of `P.path i`
and of `P.path j` are compared by their first coordinates, whose extrema are the extrema of
`P.path i` and `P.path j` for `P.edgeOf` (`Work.ORLocInd.Howie.coverCodeList_maximum_fst`,
`Work.ORLocInd.Howie.coverCodeList_minimum_fst`), and the staggeredness of `P` applies; in the case
`i = j` and `m < n` the two lists are translates of each other and the second coordinate decides.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.CoverCode
import Submission.Work.ORLocInd.Howie.coverPath_arrowList_coverEdgeOf
import Submission.Work.ORLocInd.Howie.coverCodeList_shift
import Submission.Work.ORLocInd.Howie.coverCodeList_maximum_fst
import Submission.Work.ORLocInd.Howie.coverCodeList_minimum_fst
import Submission.Work.ORLocInd.Howie.presentation_path_ne_nil

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## `pathMax` and `pathMin` of a lifted relator are extrema of its code list -/

/-- The greatest edge of a lifted relator is the maximum of its list of codes. -/
theorem coverPath_pathMax (P : Presentation V) (L : Labelling V) (hrel : VanishOnRelators L P)
    (τ : Quiver.Total V → ℤ) (i : P.ι) (n : ℤ) :
    pathMax (coverEdgeOf P L τ) (coverPath P L hrel i n) =
      (coverCodeList P L τ (P.path i) n).maximum := by
  rw [pathMax_eq_maximum, coverPath_arrowList_coverEdgeOf]

/-- The least edge of a lifted relator is the minimum of its list of codes. -/
theorem coverPath_pathMin (P : Presentation V) (L : Labelling V) (hrel : VanishOnRelators L P)
    (τ : Quiver.Total V → ℤ) (i : P.ι) (n : ℤ) :
    pathMin (coverEdgeOf P L τ) (coverPath P L hrel i n) =
      (coverCodeList P L τ (P.path i) n).minimum := by
  rw [pathMin_eq_minimum, coverPath_arrowList_coverEdgeOf]

/-- The code list of a relator is nonempty: relator paths are not the empty path
(`Work.ORLocInd.Howie.presentation_path_ne_nil`). -/
theorem coverCodeList_path_ne_nil (P : Presentation V) (L : Labelling V)
    (τ : Quiver.Total V → ℤ) (i : P.ι) (n : ℤ) :
    coverCodeList P L τ (P.path i) n ≠ [] :=
  coverCodeList_ne_nil_of_ne_nil P L τ (presentation_path_ne_nil P i) n

/-! ## The extremum of a nonempty list of codes is attained -/

/-- A nonempty list of codes has a greatest element `c`, which is the coercion of `c` and bounds
every element of the list. -/
theorem exists_maximum_eq_coe {P : Presentation V} {l : List (CoverCode P)} (h : l ≠ []) :
    ∃ c : CoverCode P, l.maximum = ↑c ∧ c ∈ l ∧ ∀ a ∈ l, a ≤ c := by
  obtain ⟨c, hc⟩ := WithBot.ne_bot_iff_exists.mp (List.maximum_ne_bot_of_ne_nil h)
  exact ⟨c, hc.symm, List.maximum_mem hc.symm, (List.maximum_eq_coe_iff.mp hc.symm).2⟩

/-- A nonempty list of codes has a least element `c`, which is the coercion of `c` and is bounded
by every element of the list. -/
theorem exists_minimum_eq_coe {P : Presentation V} {l : List (CoverCode P)} (h : l ≠ []) :
    ∃ c : CoverCode P, l.minimum = ↑c ∧ c ∈ l ∧ ∀ a ∈ l, c ≤ a := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (List.minimum_ne_top_of_ne_nil h)
  exact ⟨c, hc.symm, List.minimum_mem hc.symm, (List.minimum_eq_coe_iff.mp hc.symm).2⟩

/-! ## The four comparisons of the code lists of two relators -/

/-- For `i < j` and any levels, the greatest edge of the lifted relator `(i, m)` is smaller than
the greatest edge of `(j, n)`: compare the first coordinates, where the staggeredness of `P`
applies. -/
theorem coverCodeList_max_lt_of_lt (P : Presentation V) (L : Labelling V)
    (τ : Quiver.Total V → ℤ) {i j : P.ι} (hij : i < j) (m n : ℤ) :
    (coverCodeList P L τ (P.path i) m).maximum <
      (coverCodeList P L τ (P.path j) n).maximum := by
  obtain ⟨c₁, hc₁, _, hc₁le⟩ := exists_maximum_eq_coe (coverCodeList_path_ne_nil P L τ i m)
  obtain ⟨c₂, hc₂, _, _⟩ := exists_maximum_eq_coe (coverCodeList_path_ne_nil P L τ j n)
  have hfst₁ : ((ofLex c₁).1 : WithBot P.α) = pathMax P.edgeOf (P.path i) :=
    coverCodeList_maximum_fst P L τ (P.path i) m hc₁
  have hfst₂ : ((ofLex c₂).1 : WithBot P.α) = pathMax P.edgeOf (P.path j) :=
    coverCodeList_maximum_fst P L τ (P.path j) n hc₂
  have hall : ∀ a ∈ coverCodeList P L τ (P.path i) m, a < c₂ := by
    intro a ha
    have ha₁ : ((ofLex a).1 : WithBot P.α) ≤ ((ofLex c₁).1 : WithBot P.α) :=
      WithBot.coe_le_coe.mpr (Prod.Lex.monotone_fst a c₁ (hc₁le a ha))
    have hlt : ((ofLex a).1 : WithBot P.α) < ((ofLex c₂).1 : WithBot P.α) :=
      calc ((ofLex a).1 : WithBot P.α) ≤ ((ofLex c₁).1 : WithBot P.α) := ha₁
        _ = pathMax P.edgeOf (P.path i) := hfst₁
        _ < pathMax P.edgeOf (P.path j) := (P.staggered i j hij).1
        _ = ((ofLex c₂).1 : WithBot P.α) := hfst₂.symm
    exact Prod.Lex.lt_iff.mpr (Or.inl (WithBot.coe_lt_coe.mp hlt))
  have hres := list_maximum_lt_coe_of_forall_lt hall
  exact lt_of_lt_of_le hres (le_of_eq hc₂.symm)

/-- For `i < j` and any levels, the least edge of the lifted relator `(i, m)` is smaller than the
least edge of `(j, n)`: compare the first coordinates, where the staggeredness of `P` applies. -/
theorem coverCodeList_min_lt_of_lt (P : Presentation V) (L : Labelling V)
    (τ : Quiver.Total V → ℤ) {i j : P.ι} (hij : i < j) (m n : ℤ) :
    (coverCodeList P L τ (P.path i) m).minimum <
      (coverCodeList P L τ (P.path j) n).minimum := by
  obtain ⟨c₁, hc₁, _, _⟩ := exists_minimum_eq_coe (coverCodeList_path_ne_nil P L τ i m)
  obtain ⟨c₂, hc₂, _, _⟩ := exists_minimum_eq_coe (coverCodeList_path_ne_nil P L τ j n)
  have hfst₁ : ((ofLex c₁).1 : WithTop P.α) = pathMin P.edgeOf (P.path i) :=
    coverCodeList_minimum_fst P L τ (P.path i) m hc₁
  have hfst₂ : ((ofLex c₂).1 : WithTop P.α) = pathMin P.edgeOf (P.path j) :=
    coverCodeList_minimum_fst P L τ (P.path j) n hc₂
  have hltα : ((ofLex c₁).1 : WithTop P.α) < ((ofLex c₂).1 : WithTop P.α) := by
    rw [hfst₁, hfst₂]
    exact (P.staggered i j hij).2
  have hlt : c₁ < c₂ := Prod.Lex.lt_iff.mpr (Or.inl (WithTop.coe_lt_coe.mp hltα))
  calc (coverCodeList P L τ (P.path i) m).minimum = ↑c₁ := hc₁
    _ < ↑c₂ := WithTop.coe_lt_coe.mpr hlt
    _ = (coverCodeList P L τ (P.path j) n).minimum := hc₂.symm

/-- For `m < n` the greatest edge of the lifted relator `(i, m)` is smaller than the greatest edge
of `(i, n)`: the two code lists are translates of each other and the level decides. -/
theorem coverCodeList_max_lt_of_level_lt (P : Presentation V) (L : Labelling V)
    (τ : Quiver.Total V → ℤ) {i : P.ι} {m n : ℤ} (hmn : m < n) :
    (coverCodeList P L τ (P.path i) m).maximum <
      (coverCodeList P L τ (P.path i) n).maximum := by
  obtain ⟨c, hc, hcmem, _⟩ := exists_maximum_eq_coe (coverCodeList_path_ne_nil P L τ i m)
  rw [coverCodeList_shift P L τ (P.path i) m] at hcmem
  obtain ⟨c₀, hc₀mem, hc₀eq⟩ := List.mem_map.mp hcmem
  have hmem : codeShift P n c₀ ∈ coverCodeList P L τ (P.path i) n := by
    rw [coverCodeList_shift P L τ (P.path i) n]
    exact List.mem_map.mpr ⟨c₀, hc₀mem, rfl⟩
  have hle := List.le_maximum_of_mem' hmem
  have hlt : c < codeShift P n c₀ := by
    rw [← hc₀eq]
    exact codeShift_lt_of_lt P hmn c₀
  calc (coverCodeList P L τ (P.path i) m).maximum = ↑c := hc
    _ < ↑(codeShift P n c₀) := WithBot.coe_lt_coe.mpr hlt
    _ ≤ (coverCodeList P L τ (P.path i) n).maximum := hle

/-- For `m < n` the least edge of the lifted relator `(i, m)` is smaller than the least edge of
`(i, n)`: the two code lists are translates of each other and the level decides. -/
theorem coverCodeList_min_lt_of_level_lt (P : Presentation V) (L : Labelling V)
    (τ : Quiver.Total V → ℤ) {i : P.ι} {m n : ℤ} (hmn : m < n) :
    (coverCodeList P L τ (P.path i) m).minimum <
      (coverCodeList P L τ (P.path i) n).minimum := by
  obtain ⟨c₂, hc₂, hc₂mem, _⟩ := exists_minimum_eq_coe (coverCodeList_path_ne_nil P L τ i n)
  obtain ⟨c₁, hc₁, _, hc₁le⟩ := exists_minimum_eq_coe (coverCodeList_path_ne_nil P L τ i m)
  rw [coverCodeList_shift P L τ (P.path i) n] at hc₂mem
  obtain ⟨c₀', hc₀'mem, hc₀'eq⟩ := List.mem_map.mp hc₂mem
  have hmem : codeShift P m c₀' ∈ coverCodeList P L τ (P.path i) m := by
    rw [coverCodeList_shift P L τ (P.path i) m]
    exact List.mem_map.mpr ⟨c₀', hc₀'mem, rfl⟩
  have hle : c₁ ≤ codeShift P m c₀' := hc₁le _ hmem
  have h₂ : codeShift P m c₀' < codeShift P n c₀' := codeShift_lt_of_lt P hmn c₀'
  have hlt : c₁ < c₂ := by
    have h₃ : c₁ < codeShift P n c₀' := lt_of_le_of_lt hle h₂
    rw [hc₀'eq] at h₃
    exact h₃
  calc (coverCodeList P L τ (P.path i) m).minimum = ↑c₁ := hc₁
    _ < ↑c₂ := WithTop.coe_lt_coe.mpr hlt
    _ = (coverCodeList P L τ (P.path i) n).minimum := hc₂.symm

/-! ## Staggeredness of the lifted presentation -/

theorem cover_staggered {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (hrel : Work.ORLocInd.Howie.VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {i j : P.ι} {m n : ℤ} (h : i < j ∨ (i = j ∧ m < n)) :
    Work.ORLocInd.Howie.pathMax (Work.ORLocInd.Howie.coverEdgeOf P L τ)
        (Work.ORLocInd.Howie.coverPath P L hrel i m) <
      Work.ORLocInd.Howie.pathMax (Work.ORLocInd.Howie.coverEdgeOf P L τ)
        (Work.ORLocInd.Howie.coverPath P L hrel j n) ∧
    Work.ORLocInd.Howie.pathMin (Work.ORLocInd.Howie.coverEdgeOf P L τ)
        (Work.ORLocInd.Howie.coverPath P L hrel i m) <
      Work.ORLocInd.Howie.pathMin (Work.ORLocInd.Howie.coverEdgeOf P L τ)
        (Work.ORLocInd.Howie.coverPath P L hrel j n) := by
  rw [coverPath_pathMax P L hrel τ i m, coverPath_pathMax P L hrel τ j n,
      coverPath_pathMin P L hrel τ i m, coverPath_pathMin P L hrel τ j n]
  rcases h with hij | ⟨rfl, hmn⟩
  · exact ⟨coverCodeList_max_lt_of_lt P L τ hij m n, coverCodeList_min_lt_of_lt P L τ hij m n⟩
  · exact ⟨coverCodeList_max_lt_of_level_lt P L τ hmn, coverCodeList_min_lt_of_level_lt P L τ hmn⟩

end Work.ORLocInd.Howie
