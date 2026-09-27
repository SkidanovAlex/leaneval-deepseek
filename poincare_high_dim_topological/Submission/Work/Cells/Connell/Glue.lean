import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Cells.Connell.Basic
import Submission.Work.Cells.Connell.connell_step
import Submission.Work.Cells.Connell.two_cells_sphere
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_compl_homeomorph

/-!
# Gluing Connell's step with the rest of the proof (blueprint `C3`-glue)

* `cellCover_two`: iterate `connell_step` to reduce any cell cover with at least one cell to a
  cover by two cells.
* `exists_compl_homeomorph_of_cellCover` / `..._of_exists_cellCover`: combine with `C4`
  (`two_cells_sphere`) to produce a point whose complement is `ℝⁿ`.
* `nonempty_homeomorph_sphere_of_cellCover`: the resulting statement in the shape of the
  challenge conclusion, using the one-point compactification (`Work.Endgame`).
-/

open Set Metric

namespace Work.Cells.Connell

/-- Iterated Connell step: a cover by `k ≥ 1` open cells can be reduced to a cover by two.
(The case `k = 0` is excluded: `PL.CellCover n M 0` says that `M` is empty.) -/
theorem cellCover_two_aux {n : ℕ} (hn : 5 ≤ n) {M : Type*} [MetricSpace M] [CompactSpace M]
    (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j) :
    ∀ k, 1 ≤ k → PL.CellCover n M k → PL.CellCover n M 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk h
    rcases lt_or_ge k 3 with h3 | h3
    · interval_cases k
      · exact cellCover_succ (k := 1) le_rfl h
      · exact h
    · have h1 : k - 3 + 3 = k := Nat.sub_add_cancel h3
      have h2 : k - 3 + 2 = k - 1 := by omega
      have hstep : PL.CellCover n M (k - 1) := by
        have hs := connell_step hn A hloc hconn (k - 3)
        rw [h1, h2] at hs
        exact hs h
      exact ih (k - 1) (by omega) (by omega) hstep

/-- A cover by `k ≥ 1` open cells of a compact metric space satisfying the Connell hypotheses
can be reduced to a cover by two cells. -/
theorem cellCover_two {n : ℕ} (hn : 5 ≤ n) {M : Type*} [MetricSpace M] [CompactSpace M]
    (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j) {k : ℕ} (hk : 1 ≤ k)
    (h : PL.CellCover n M k) : PL.CellCover n M 2 :=
  cellCover_two_aux hn A hloc hconn k hk h

/-- **The conclusion of Connell's argument in cell-cover form**: from a cell cover with at
least one cell, some point of `M` has `ℝⁿ` as its complement. -/
theorem exists_compl_homeomorph_of_cellCover {n : ℕ} (hn : 5 ≤ n) {M : Type*} [MetricSpace M]
    [CompactSpace M] (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j) (hbrown : BrownCriterionAt n M)
    (hrad : RadialExpandForm n) (hext : ExtHomeoForm n) {k : ℕ} (hk : 1 ≤ k)
    (h : PL.CellCover n M k) : ∃ q : M, Nonempty (↥({q}ᶜ : Set M) ≃ₜ PL.E n) :=
  two_cells_sphere (by omega) (cellCover_two hn A hloc hconn hk h) hbrown hrad hext

/-- The same conclusion from the mere existence of a finite cell cover, for nonempty `M`. -/
theorem exists_compl_homeomorph_of_exists_cellCover {n : ℕ} (hn : 5 ≤ n) {M : Type*}
    [MetricSpace M] [CompactSpace M] (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j) (hbrown : BrownCriterionAt n M)
    (hrad : RadialExpandForm n) (hext : ExtHomeoForm n) (hne : Nonempty M)
    (h : ∃ k, PL.CellCover n M k) : ∃ q : M, Nonempty (↥({q}ᶜ : Set M) ≃ₜ PL.E n) := by
  obtain ⟨k, hk⟩ := h
  have hk1 : 1 ≤ k := by
    by_contra hcon
    have h0 : k = 0 := by omega
    subst k
    obtain ⟨W, -, hcov⟩ := hk
    obtain ⟨x⟩ := hne
    have hx : x ∈ (⋃ i : Fin 0, W i : Set M) := by
      rw [hcov]; exact Set.mem_univ x
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp hx
    exact i.elim0
  exact exists_compl_homeomorph_of_cellCover hn A hloc hconn hbrown hrad hext hk1 hk


/-- Variant of `cellCover_two` that does not ask for `1 ≤ k`: for nonempty `M` the case `k = 0`
is impossible (`CellCover n M 0` says that `M` is empty). -/
theorem cellCover_two_of_nonempty {n : ℕ} (hn : 5 ≤ n) {M : Type*} [MetricSpace M]
    [CompactSpace M] (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j) (hne : Nonempty M) {k : ℕ}
    (h : PL.CellCover n M k) : PL.CellCover n M 2 := by
  have hk1 : 1 ≤ k := by
    by_contra hcon
    have h0 : k = 0 := by omega
    subst k
    obtain ⟨W, -, hcov⟩ := h
    obtain ⟨x⟩ := hne
    have hx : x ∈ (⋃ i : Fin 0, W i : Set M) := by
      rw [hcov]; exact Set.mem_univ x
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp hx
    exact i.elim0
  exact cellCover_two hn A hloc hconn hk1 h

/-- The end-to-end statement in the shape of the challenge conclusion: a compact metric space
with local cube charts, `(n-1)`-connected, `n ≥ 5`, and admitting a finite cover by open
`n`-cells is homeomorphic to `𝕊ⁿ`. -/
theorem nonempty_homeomorph_sphere_of_cellCover {n : ℕ} (hn : 5 ≤ n) {M : Type*}
    [MetricSpace M] [CompactSpace M] (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j) (hbrown : BrownCriterionAt n M)
    (hrad : RadialExpandForm n) (hext : ExtHomeoForm n) {k : ℕ} (hk : 1 ≤ k)
    (h : PL.CellCover n M k) :
    Nonempty (M ≃ₜ sphere (0 : PL.E (n + 1)) 1) := by
  obtain ⟨q, ⟨e⟩⟩ := exists_compl_homeomorph_of_cellCover hn A hloc hconn hbrown hrad hext hk h
  exact Work.Endgame.nonempty_homeomorph_sphere_of_compl_homeomorph q e

/-- The end-to-end statement in the shape of the challenge conclusion, from the existence of a
finite cover by open cells: a compact metric space with local cube charts, `(n-1)`-connected and
`n ≥ 5`, is homeomorphic to `𝕊ⁿ`. -/
theorem nonempty_homeomorph_sphere_of_exists_cellCover {n : ℕ} (hn : 5 ≤ n) {M : Type*}
    [MetricSpace M] [CompactSpace M] (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j) (hbrown : BrownCriterionAt n M)
    (hrad : RadialExpandForm n) (hext : ExtHomeoForm n) (hne : Nonempty M)
    (h : ∃ k, PL.CellCover n M k) :
    Nonempty (M ≃ₜ sphere (0 : PL.E (n + 1)) 1) := by
  obtain ⟨q, ⟨e⟩⟩ := exists_compl_homeomorph_of_exists_cellCover hn A hloc hconn hbrown hrad hext hne h
  exact Work.Endgame.nonempty_homeomorph_sphere_of_compl_homeomorph q e

end Work.Cells.Connell
