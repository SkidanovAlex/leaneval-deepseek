/-
  WilE4 / CAD — the cells of a decomposition are *laminar*: two cells are nested or disjoint.

  This is what turns "the set `Z` is a union of cells" (which is how `projSAd` and `complSAd`
  produce their values: as `unionCells` of a sub-list of `CadCells`) into the hypothesis
  `hUn : ∀ D ∈ CadCells n H, D.set ⊆ Z.set ∨ Disjoint D.set Z.set` that `projSAd_set` and
  `complSAd_set` consume.

  The proof of laminarity is the induction that matches the recursion of `CadCells`: at level `k+1`
  a cell is `cell C H v`, every point of it realises the sign vector `v` (`mem_cell_iff`), so two
  cells with different sign vectors are disjoint, and two cells with the same sign vector are
  compared through the base cells, which are laminar by the induction hypothesis.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Decomp
import Submission.Work.WilE4.CAD.CadCells_isUnionOf
import Submission.Work.WilE4.CAD.Ops

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial

/-- **The cells of a cylindrical decomposition are laminar**: two cells of the same decomposition
are either nested or disjoint. -/
theorem CadCells_laminar : ∀ (n : ℕ) (H : List (MvPolynomial (Fin n) ℝ)) (C D : SAd n),
    C ∈ CadCells n H → D ∈ CadCells n H → C.set ⊆ D.set ∨ Disjoint C.set D.set := by
  intro n
  induction n with
  | zero =>
    intro H C D hC hD
    rw [mem_CadCells_zero] at hC hD
    subst hC
    subst hD
    left
    rw [topCell_set]
  | succ k ih =>
    intro H C D hC hD
    obtain ⟨C₀, hC₀, v, -, rfl⟩ := (mem_CadCells_succ).mp hC
    obtain ⟨D₀, hD₀, w, -, rfl⟩ := (mem_CadCells_succ).mp hD
    by_cases hvw : v = w
    · subst hvw
      rcases ih (projDataT k H) C₀ D₀ hC₀ hD₀ with hsub | hdisj
      · left
        intro z hz
        rw [mem_cell_iff] at hz ⊢
        exact ⟨hsub hz.1, hz.2⟩
      · right
        rw [Set.disjoint_left] at hdisj ⊢
        intro z hz hz'
        rw [mem_cell_iff] at hz hz'
        exact hdisj hz.1 hz'.1
    · right
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hvw
      rw [Set.disjoint_left]
      intro z hz hz'
      rw [mem_cell_iff] at hz hz'
      exact hi (by rw [← hz.2 i, ← hz'.2 i])

/-- **A cell is contained in a union of cells of the same decomposition, or disjoint from it.**
This is the `hUn` input of `projSAd_set` and `complSAd_set` when the set is a `unionCells` of a
sub-list of the decomposition (which is how `projSAd` and `complSAd` are built). -/
theorem cell_subset_unionCells_or_disjoint {n : ℕ} (H : List (MvPolynomial (Fin n) ℝ))
    (L : List (SAd n)) (hL : ∀ C ∈ L, C ∈ CadCells n H) (D : SAd n)
    (hD : D ∈ CadCells n H) :
    D.set ⊆ (unionCells L).set ∨ Disjoint D.set (unionCells L).set := by
  by_cases h : ∃ C ∈ L, D.set ⊆ C.set
  · left
    intro z hz
    rw [unionCells_set]
    obtain ⟨C, hC, hsub⟩ := h
    exact ⟨C, hC, hsub hz⟩
  · right
    rw [unionCells_set, Set.disjoint_left]
    intro z hzD hzU
    obtain ⟨C, hC, hzC⟩ := hzU
    rcases CadCells_laminar n H D C hD (hL C hC) with hsub | hdisj
    · exact h ⟨C, hC, hsub⟩
    · exact Set.disjoint_left.mp hdisj hzD hzC

/-- The same, for the family `projDataT k H`: every cell of `CadCells k (projDataT k H)` is either
contained in a union of cells of the same decomposition or disjoint from it. -/
theorem cell_subset_unionCells_or_disjoint' {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ))
    (L : List (SAd k)) (hL : ∀ C ∈ L, C ∈ CadCells k (projDataT k H)) (D : SAd k)
    (hD : D ∈ CadCells k (projDataT k H)) :
    D.set ⊆ (unionCells L).set ∨ Disjoint D.set (unionCells L).set :=
  cell_subset_unionCells_or_disjoint (projDataT k H) L hL D hD

end Work.WilE4.CAD
