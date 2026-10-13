/-
  WilE4 / CAD — every set whose atoms lie in the family `H` is a union of cells.

  Let `H` be a family of polynomials in `n` variables and `Z` a semialgebraic set in disjunctive
  normal form all of whose atoms belong to `H`.  Then every cell of the cylindrical decomposition
  `CadCells n H` is *either contained in* `Z` or *disjoint from* `Z`; equivalently `Z` is a union of
  cells (this is the form `Ops.complSAd_set` consumes).

  The argument has no analytic content; it only uses the way the cells are built.

  * level `0`: the decomposition has the single cell `topCell 0 = ℝ⁰`.  The space `Fin 0 → ℝ` is a
    subsingleton, so the set of *any* `SAd 0` is either all of it or empty; in the two cases the
    cell is contained in `Z` or disjoint from `Z`.

  * level `k+1`: by `mem_CadCells_succ` a cell is `cell C H v` where `v` is a sign vector of `H`
    realised over the base cell `C`.  By construction (`mem_cell_iff`) every point of `cell C H v`
    realises the sign vector `v`, so **the sign of every member of `H` is the same at any two points
    of the cell** (`sign_eq_of_mem_cell`).  Hence the truth of a basic set whose atoms lie in `H` is
    the same at any two points of the cell (`holds_congr_of_mem_cell`), and evaluating the two cases
    at one single point of the (non-empty) cell decides whether the whole cell lies in `Z` or is
    disjoint from it.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Decomp

namespace Work.WilE4.CAD

open MvPolynomial

/-! ## The decomposition at level `0` -/

/-- The decomposition of `ℝ⁰` consists of the single cell `topCell 0`. -/
theorem CadCells_zero (H : List (MvPolynomial (Fin 0) ℝ)) : CadCells 0 H = [topCell 0] := rfl

/-- Membership in the decomposition at level `0`. -/
theorem mem_CadCells_zero {H : List (MvPolynomial (Fin 0) ℝ)} {C : SAd 0} :
    C ∈ CadCells 0 H ↔ C = topCell 0 := by
  rw [CadCells_zero, List.mem_singleton]

/-- A subset of a subsingleton space is all of it or empty. -/
theorem SAd_set_eq_univ_or_empty_of_subsingleton {m : ℕ} (X : SAd m)
    [Subsingleton (Fin m → ℝ)] : X.set = Set.univ ∨ X.set = ∅ := by
  by_cases hne : (X.set).Nonempty
  · left
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨y, hy⟩ := hne
    rwa [Subsingleton.elim y x] at hy
  · right
    ext x
    exact ⟨fun hx => absurd ⟨x, hx⟩ hne, fun hx => hx.elim⟩

/-! ## The sign of a member of the family is constant on a cell -/

/-- On a cell `cell C G v`, the sign of every member `P ∈ G` is the value prescribed by `v`, so it
is the same at any two points of the cell. -/
theorem sign_eq_of_mem_cell {m : ℕ} {G : List (MvPolynomial (Fin (m+1)) ℝ)} {C : SAd m}
    {v : Fin G.length → SignType} {z z' : Fin (m+1) → ℝ}
    (hz : z ∈ (cell C G v).set) (hz' : z' ∈ (cell C G v).set)
    {P : MvPolynomial (Fin (m+1)) ℝ} (hP : P ∈ G) :
    SignType.sign (MvPolynomial.eval z P) = SignType.sign (MvPolynomial.eval z' P) := by
  obtain ⟨i, hi⟩ := List.get_of_mem hP
  rw [← hi, ((mem_cell_iff G C v z).mp hz).2 i, ((mem_cell_iff G C v z').mp hz').2 i]

/-- If all atoms of a basic set `B` belong to the family `G` defining a cell, then the truth of `B`
is the same at any two points of the cell. -/
theorem holds_congr_of_mem_cell {m : ℕ} {G : List (MvPolynomial (Fin (m+1)) ℝ)} {C : SAd m}
    {v : Fin G.length → SignType} {B : BasicD (m+1)}
    (hatoms : ∀ P ∈ B.eqs ++ B.pos, P ∈ G) {z z' : Fin (m+1) → ℝ}
    (hz : z ∈ (cell C G v).set) (hz' : z' ∈ (cell C G v).set) :
    B.Holds z ↔ B.Holds z' := by
  have hzero : ∀ P ∈ G, (MvPolynomial.eval z P = 0 ↔ MvPolynomial.eval z' P = 0) := by
    intro P hP
    rw [← sign_eq_zero_iff, sign_eq_of_mem_cell hz hz' hP, sign_eq_zero_iff]
  have hpos : ∀ P ∈ G, (0 < MvPolynomial.eval z P ↔ 0 < MvPolynomial.eval z' P) := by
    intro P hP
    rw [← sign_eq_one_iff, sign_eq_of_mem_cell hz hz' hP, sign_eq_one_iff]
  constructor
  · intro hB
    exact ⟨fun f hf => (hzero f (hatoms f (List.mem_append_left _ hf))).mp (hB.1 f hf),
      fun g hg => (hpos g (hatoms g (List.mem_append_right _ hg))).mp (hB.2 g hg)⟩
  · intro hB
    exact ⟨fun f hf => (hzero f (hatoms f (List.mem_append_left _ hf))).mpr (hB.1 f hf),
      fun g hg => (hpos g (hatoms g (List.mem_append_right _ hg))).mpr (hB.2 g hg)⟩

/-! ## The main statement -/

theorem CadCells_isUnionOf {n : ℕ} (H : List (MvPolynomial (Fin n) ℝ)) (Z : SAd n)
    (h : ∀ B ∈ Z.basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ H) :
    ∀ C ∈ CAD.CadCells n H, C.set ⊆ Z.set ∨ Disjoint C.set Z.set := by
  cases n with
  | zero =>
    intro C hC
    rw [mem_CadCells_zero] at hC
    subst hC
    rw [topCell_set]
    rcases SAd_set_eq_univ_or_empty_of_subsingleton Z with hZ | hZ
    · left; rw [hZ]
    · right; rw [hZ]; simp
  | succ k =>
    intro D hD
    rw [mem_CadCells_succ] at hD
    obtain ⟨C, hC, v, hreal, rfl⟩ := hD
    obtain ⟨z₀, hz₀⟩ := (realizedOn_iff_nonempty H C v).mp hreal
    by_cases hB : ∃ B ∈ Z.basics, B.Holds z₀
    · left
      intro z hz
      obtain ⟨B, hBmem, hBz₀⟩ := hB
      exact ⟨B, hBmem, (holds_congr_of_mem_cell (h B hBmem) hz hz₀).mpr hBz₀⟩
    · right
      rw [Set.disjoint_left]
      intro z hz hzZ
      obtain ⟨B, hBmem, hBz⟩ := hzZ
      exact hB ⟨B, hBmem, (holds_congr_of_mem_cell (h B hBmem) hz hz₀).mp hBz⟩

/-! ## The same statement for the tower-refined decomposition

`cadCells n H = CadCells n (towerTop n H)` refines `CadCells n H` (the family `towerTop n H` contains
`H`, since the tower of a family contains the family itself), so the union-of statement holds for it
with the same hypothesis. -/

/-- A member of a family belongs to its derivative tower, hence to `towerTop`. -/
theorem self_mem_towerTop {n : ℕ} {H : List (MvPolynomial (Fin n) ℝ)}
    {P : MvPolynomial (Fin n) ℝ} (hP : P ∈ H) : P ∈ towerTop n H := by
  match n with
  | 0 => exact hP
  | k + 1 =>
    show P ∈ tower H
    exact List.mem_flatMap.mpr ⟨P, hP,
      List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), by simp⟩⟩

/-- `CadCells_isUnionOf` for the decomposition `cadCells` refined by the derivative tower. -/
theorem cadCells_isUnionOf {n : ℕ} (H : List (MvPolynomial (Fin n) ℝ)) (Z : SAd n)
    (h : ∀ B ∈ Z.basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ H) :
    ∀ C ∈ cadCells n H, C.set ⊆ Z.set ∨ Disjoint C.set Z.set :=
  CadCells_isUnionOf (towerTop n H) Z (fun B hB P hP => self_mem_towerTop (h B hB P hP))

end Work.WilE4.CAD
