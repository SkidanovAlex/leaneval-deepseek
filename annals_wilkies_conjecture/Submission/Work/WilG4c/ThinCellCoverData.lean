import Mathlib
import Submission.Work.WilG4a.CD.thinCellParam
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG4a.CD.badLoci_cellDecomp

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

/-- A member of a cylindrical decomposition is a cell. -/
private theorem isCell_of_isCylDecomp : ∀ {n : ℕ} {C : Finset (Set (Fin n → ℝ))},
    WilkiesDesign.IsCylDecomp n C → ∀ c ∈ C, WilkiesDesign.IsCell n c := by
  intro n
  induction n with
  | zero =>
      intro C h c hc
      have hC : C = {Set.univ} := h
      rw [hC] at hc
      rw [Finset.mem_singleton.mp hc]
      exact WilkiesDesign.IsCell.zero
  | succ m ih =>
      intro C h c hc
      exact (h.1 c hc).1

theorem ThinCellCoverData (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (p F0 : ℕ) :
    ∃ (A : ℕ) (aCell : ℕ) (bCard : MvPolynomial (Fin 2) ℕ) (bCell bD : Polynomial ℕ),
      ∀ (D : ℕ) (V : Set (Fin p → ℝ)), V ∈ S.Ω F0 D p → interior V = ∅ →
        ∃ C : Finset (Set (Fin p → ℝ)),
          WilkiesDesign.IsCylDecomp p C ∧
          (∀ κ ∈ C, κ ⊆ V ∨ Disjoint κ V) ∧
          C.card ≤ MvPolynomial.eval ![D, 1] bCard ∧
          (∀ κ ∈ C, WilkiesDesign.IsCell p κ) ∧
          (∀ κ ∈ C, κ ∈ S.Ω aCell (bCell.eval D) p) ∧
          (∀ κ ∈ C, κ ⊆ V → ∃ (k : ℕ) (_hk : k < p) (e : Fin k ↪ Fin p)
              (Ψ : (Fin k → ℝ) → (Fin p → ℝ)),
            (∀ l ∈ κ, Ψ (l ∘ e) = l) ∧
            Work.WilG4a.CD.paramGraph Ψ ∈ S.Ω A (bD.eval D) (k + p)) := by
  -- Sharp cell decomposition of `ℝ^p` adapted to `V`, with the format `aCell` and the
  -- degree polynomial `bCell` coming from sharp cell decomposition at format `F0`.
  obtain ⟨aCell, bCard, bCell, hsharp⟩ := hcd F0 p
  -- The thin cell parametrisation: for a cell with empty interior, at format `aCell`,
  -- the parametrisation of the cell is `Ω A (B.eval D)`-definable.
  obtain ⟨A, B, hparam⟩ := Work.WilG4a.CD.thinCellParam S hcd p aCell
  refine ⟨A, aCell, bCard, bCell, B.comp bCell, ?_⟩
  intro D V hV hInt
  -- Decompose `ℝ^p` into cells each of which is contained in `V` or disjoint from it.
  obtain ⟨C, hcyl, hcompat, hcard, hmem⟩ :=
    hsharp D 1 (fun _ : Fin 1 => V) (fun _ => hV)
  refine ⟨C, hcyl, ?_, ?_, ?_, ?_, ?_⟩
  · -- compatibility with `V`
    intro κ hκ
    simpa using hcompat 0 κ hκ
  · -- cardinality bound
    simpa using hcard
  · -- every cell of the decomposition is a cell
    intro κ hκ
    exact isCell_of_isCylDecomp hcyl κ hκ
  · -- the `Ω`-membership of every cell
    intro κ hκ
    exact hmem κ hκ
  · -- the thin cells contained in `V` admit a parametrisation over `k < p` coordinates
    intro κ hκ hκV
    have hintκ : interior κ = ∅ := by
      have hsub : interior κ ⊆ interior V := interior_mono hκV
      rw [hInt] at hsub
      exact Set.subset_empty_iff.mp hsub
    obtain ⟨k, hk, e, Ψ, hsec, hmemΨ⟩ :=
      hparam (bCell.eval D) κ (hmem κ hκ) (isCell_of_isCylDecomp hcyl κ hκ) hintκ
    refine ⟨k, hk, e, Ψ, hsec, ?_⟩
    simpa using hmemΨ

end Work.WilG4c
