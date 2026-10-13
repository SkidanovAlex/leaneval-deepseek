/-
  WilG1 / Cell / thin_closure.

  `thin_closure` : the topological closure of an `Ω`-set with empty interior again has empty
  interior.  This is the statement that the sharp-o-minimal sets of the frozen structure
  `SOMin` are "thin" in the o-minimal sense: dimension is not created by taking closures.

  Proof outline.  Let `A ∈ S.Ω a D n` have empty interior.  Apply the sharp cell decomposition
  `S.SharpCD` to the one-element family `A`: we obtain a finite cylindrical decomposition `C`
  of `ℝⁿ` into cells, each of which is contained in `A` or disjoint from it.  Because `C`
  covers `ℝⁿ`, every point of `A` lies in a cell of `C` that is contained in `A`, so

    `A = ⋃ {κ ∈ C : κ ⊆ A}`

  as sets.  Every such cell `κ` has empty interior (it is contained in `A`), and a *cell* with
  empty interior is nowhere dense (`isCell_isNowhereDense`, the only o-minimal input: graph
  cells are graphs of continuous functions, band cells project to nowhere dense base cells).
  A finite union of nowhere dense sets is nowhere dense, so `closure A` has empty interior.

  Helper lemmas used, and where they live:
  * `isNowhereDense_graph` (`Cell/isNowhereDense_graph.lean`): the closure of the graph of a
    function continuous on `C` has empty interior;
  * `interior_band_nonempty` (`Cell/thin_union.lean`), `interior_preimage_init_subset`
    (`Cell/interior_preimage_init_subset.lean`): the two inputs to the band case;
  * `isCell_of_mem_cylDecomp`, `exists_mem_of_cylDecomp` (`Cell/thin_union.lean`): cells of a
    cylindrical decomposition are `IsCell`, and the decomposition covers `ℝⁿ`.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG1.Cell.isNowhereDense_graph
import Submission.Work.WilG1.Cell.interior_preimage_init_subset

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilG1.Cell

open WilkiesDesign

/-! ## The band case of the cell lemma

A band cell over `C` is `{z | Fin.init z ∈ C ∧ a (Fin.init z) < z (Fin.last n) < b (Fin.init z)}`.
It has nonempty interior as soon as `C` does (a point of `interior C` lifts to an interior point
of the band, using only that `a` and `b` are continuous on `C`).  Hence if the band has empty
interior then so does `C`, and the induction hypothesis applies to the base cell. -/

theorem band_cell_isNowhereDense {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (ha : ContinuousOn a C) (hb : ContinuousOn b C) (hab : ∀ x ∈ C, a x < b x)
    (ihC : interior C = ∅ → IsNowhereDense C)
    (hint : interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} = ∅) :
    IsNowhereDense {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  have hCint : interior C = ∅ := by
    by_contra hne
    have hne' : (interior C).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have h := interior_band_nonempty ha hb hab hne'
    rw [hint] at h
    exact h.ne_empty rfl
  have hcell : IsNowhereDense C := ihC hCint
  rw [IsNowhereDense] at hcell ⊢
  refine Set.eq_empty_of_subset_empty ?_
  have hcont : Continuous (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
    continuous_pi fun i => continuous_apply (Fin.castSucc i)
  have hsub : interior (closure {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)}) ⊆
      {z : Fin (n + 1) → ℝ | Fin.init z ∈ interior (closure C)} :=
    (interior_mono ((closure_mono (fun z hz => hz.1)).trans
      (hcont.closure_preimage_subset C))).trans (interior_preimage_init_subset (closure C))
  rw [hcell] at hsub
  exact hsub

/-! ## The cell lemma -/

/-- A cell with empty interior is nowhere dense.  The three cases of `IsCell`:

* `zero`: `Set.univ ⊆ ℝ⁰` has nonempty interior, so the hypothesis is contradictory;
* `graph`: the closure of a graph of a function continuous on `C` has empty interior
  (`isNowhereDense_graph`), with no hypothesis on `C` needed;
* `band`: `band_cell_isNowhereDense` above. -/
theorem isCell_isNowhereDense {n : ℕ} {κ : Set (Fin n → ℝ)} (h : IsCell n κ)
    (hint : interior κ = ∅) : IsNowhereDense κ := by
  induction h with
  | zero =>
      exfalso
      have hne : (Set.univ : Set (Fin 0 → ℝ)).Nonempty := ⟨Fin.elim0, Set.mem_univ _⟩
      obtain ⟨x, hx⟩ := hne
      rw [IsOpen.interior_eq isOpen_univ] at hint
      rw [hint] at hx
      exact hx
  | graph hC f hf _ih => exact isNowhereDense_graph hf
  | band hC a b ha hb hab ih => exact band_cell_isNowhereDense ha hb hab ih hint

/-- A finite union of cells contained in a set of empty interior is nowhere dense. -/
theorem isNowhereDense_biUnion_cells {n : ℕ} {C : Finset (Set (Fin n → ℝ))} {A : Set (Fin n → ℝ)}
    (hcell : ∀ κ ∈ C, IsCell n κ) (hsub : ∀ κ ∈ C, κ ⊆ A) (hint : interior A = ∅) :
    IsNowhereDense (⋃ κ ∈ C, κ) := by
  refine IsNowhereDense.biUnion (u := C) (f := fun κ => κ) (fun κ hκ => ?_)
  have hintκ : interior κ = ∅ :=
    Set.eq_empty_of_subset_empty (by rw [← hint]; exact interior_mono (hsub κ hκ))
  exact isCell_isNowhereDense (hcell κ hκ) hintκ

/-! ## The main statement -/

theorem thin_closure {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {n : ℕ} {a D : ℕ}
    {b : Polynomial ℕ} {A : Set (Fin n → ℝ)} (hA : A ∈ S.Ω a (b.eval D) n)
    (hint : interior A = ∅) : interior (closure A) = ∅ := by
  obtain ⟨a', b', c', hsharp⟩ := hcd a n
  obtain ⟨C, hdec, hsep, -, -⟩ := hsharp (b.eval D) 1 (fun _ => A) (fun _ => hA)
  have hcover : ∀ z : Fin n → ℝ, ∃ κ ∈ C, z ∈ κ := fun z => exists_mem_of_cylDecomp hdec z
  have hcell : ∀ κ ∈ C, IsCell n κ := fun κ hκ => isCell_of_mem_cylDecomp hdec hκ
  -- the cells of `C` that lie in `A` cover `A`
  have hAeq : A = ⋃ κ ∈ C.filter (fun κ => κ ⊆ A), κ := by
    ext z
    constructor
    · intro hz
      obtain ⟨κ, hκC, hzκ⟩ := hcover z
      have hsub : κ ⊆ A := by
        rcases hsep 0 κ hκC with h | hd
        · exact h
        · exact absurd hz (Set.disjoint_left.mp hd hzκ)
      exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hκC, hsub⟩) hzκ
    · intro hz
      obtain ⟨κ, hκ, hzκ⟩ := Set.mem_iUnion₂.mp hz
      exact (Finset.mem_filter.mp hκ).2 hzκ
  have hA' : IsNowhereDense A := by
    rw [hAeq]
    exact isNowhereDense_biUnion_cells (C := C.filter (fun κ => κ ⊆ A))
      (fun κ hκ => hcell κ (Finset.mem_filter.mp hκ).1)
      (fun κ hκ => (Finset.mem_filter.mp hκ).2) hint
  simpa [IsNowhereDense] using hA'

end Work.WilG1.Cell
