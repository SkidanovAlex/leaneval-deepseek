import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Cell
import Submission.Work.WilkiesH.Cell.cellDimLE_of_isCell_dimLE
import Submission.Work.WilkiesH.Cell.cellDimLE_zero_subsingleton
import Submission.Work.WilkiesH.Cell.isCell_nonempty
import Submission.Work.WilkiesH.Count.eval_pair_bound
import Submission.Work.WilkiesH.Count.card_le_card_of_subsingleton_cover

/-!
# Area H (counting) — the dimension-`0` base case

This file proves the base case of the dimension induction of BNZ §6: a definable
set `X ∈ S.Ω F D n` of o-minimal dimension `≤ 0` — i.e. `X` contains no interval
in any coordinate direction — has polynomially many points in `D`.

The argument is short once the vocabulary of sharp cell decomposition is in
place.  Applying `S.SharpCD` to the single set `X` (the family `Fin 1 → Set _`
whose only member is `X`) produces a cylindrical decomposition `C` of `ℝⁿ` all
of whose cells are either contained in `X` or disjoint from `X`, and whose
cardinality is bounded by `b(D, 1)`, a polynomial in `D`.

* Every point of `X` lies in a member of `C`, and that member cannot be disjoint
  from `X`, so it is contained in `X`; since `DimLE X 0`, that cell has dimension
  `≤ 0`, so by `cellDimLE_of_isCell_dimLE` it is a `CellDimLE`-cell of dimension
  `0`, and by `cellDimLE_zero_subsingleton` it is a subsingleton.
* Hence the map sending a point of `X` to a cell of `C` containing it is
  injective, so any finite `T ⊆ X` has `T.card ≤ C.card ≤ b(D,1)`.
* Finally `b(D,1) ≤ b.support.sum b.coeff * (D+1)^b.totalDegree`
  (`eval_pair_bound`), a polynomial bound in `D` with fixed coefficients.
-/

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilkiesH.Count

open WilkiesDesign

/-! ## Two elementary consequences of the definition of a cylindrical decomposition -/

/-- Every member of a cylindrical decomposition is a cell.  For `n = 0` the
decomposition is forced to be `{Set.univ}` and `Set.univ ⊆ ℝ⁰` is the base
cell; for `n + 1` this is part of the definition. -/
theorem isCell_of_mem_isCylDecomp {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (h : WilkiesDesign.IsCylDecomp n C) {κ : Set (Fin n → ℝ)} (hκ : κ ∈ C) :
    WilkiesDesign.IsCell n κ := by
  cases n with
  | zero =>
    have hC : C = {Set.univ} := h
    have hκ' : κ = Set.univ := by
      rw [hC] at hκ
      simpa using hκ
    rw [hκ']
    exact WilkiesDesign.IsCell.zero
  | succ n => exact (h.1 κ hκ).1

/-- A cylindrical decomposition covers its ambient space. -/
theorem exists_mem_of_isCylDecomp {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (h : WilkiesDesign.IsCylDecomp n C) (x : Fin n → ℝ) : ∃ κ ∈ C, x ∈ κ := by
  cases n with
  | zero => exact ⟨Set.univ, by rw [h]; simp, trivial⟩
  | succ n => exact h.2.2.1 x

/-! ## The dimension-`0` counting bound -/

/-- **Base case of the dimension induction.**  If `X ∈ S.Ω F D n` has dimension
`≤ 0` then its finite subsets have cardinality bounded by a polynomial in `D`
with constants depending only on `F` and `n`. -/
theorem dimLE_zero_card (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (F n : ℕ) :
    ∃ c e : ℕ, ∀ (D : ℕ) (X : Set (Fin n → ℝ)), X ∈ S.Ω F D n → WilkiesDesign.DimLE X 0 →
      ∀ T : Finset (Fin n → ℝ), (↑T : Set (Fin n → ℝ)) ⊆ X →
        T.card ≤ c * (D + 1) ^ e := by
  obtain ⟨_a, b, _c, hcd'⟩ := hcd F n
  refine ⟨b.support.sum b.coeff, b.totalDegree, fun D X hX hdim T hT => ?_⟩
  -- the cylindrical decomposition of `ℝⁿ` adapted to the single set `X`
  obtain ⟨C, hcyl, hsep, hcard, _⟩ := hcd' D 1 (fun _ : Fin 1 => X) (fun _ => hX)
  -- the cells of `C` that meet `X`
  set Csub : Finset (Set (Fin n → ℝ)) := C.filter (fun κ => (κ ∩ X).Nonempty) with hCsub
  have hCsub_mem : ∀ κ, κ ∈ Csub ↔ κ ∈ C ∧ (κ ∩ X).Nonempty := by
    intro κ
    rw [hCsub]
    exact Finset.mem_filter
  -- each of them is contained in `X` (it is not disjoint from `X`)
  have hsub_of_mem : ∀ κ ∈ Csub, κ ⊆ X := by
    intro κ hκ
    obtain ⟨hκC, hne⟩ := (hCsub_mem κ).mp hκ
    rcases hsep (0 : Fin 1) κ hκC with hsub | hdisj
    · exact hsub
    · exfalso
      obtain ⟨x, hxκ, hxX⟩ := hne
      exact (Set.disjoint_left.mp hdisj) hxκ hxX
  -- and each of them is a subsingleton, because `X` has dimension `0`
  have hsubsing : ∀ κ ∈ Csub, κ.Subsingleton := by
    intro κ hκ
    obtain ⟨hκC, _⟩ := (hCsub_mem κ).mp hκ
    exact Work.WilkiesH.Cell.cellDimLE_zero_subsingleton
      (Work.WilkiesH.Cell.cellDimLE_of_isCell_dimLE (isCell_of_mem_isCylDecomp hcyl hκC)
        (Work.WilkiesH.dimLE_of_subset hdim (hsub_of_mem κ hκ)))
  -- but they still cover `X`
  have hcover : ∀ x ∈ X, ∃ κ ∈ Csub, x ∈ κ := by
    intro x hx
    obtain ⟨κ, hκC, hxκ⟩ := exists_mem_of_isCylDecomp hcyl x
    exact ⟨κ, (hCsub_mem κ).mpr ⟨hκC, ⟨x, hxκ, hx⟩⟩, hxκ⟩
  -- counting: an injection `T → Csub`
  have h1 : T.card ≤ Csub.card := card_le_card_of_subsingleton_cover hsubsing hcover hT
  have h2 : Csub.card ≤ C.card := by
    rw [hCsub]
    exact Finset.card_filter_le _ _
  have h3 : C.card ≤ MvPolynomial.eval ![D, 1] b := hcard
  have h4 : MvPolynomial.eval ![D, 1] b
      ≤ (b.support.sum b.coeff) * (D + 1) ^ b.totalDegree := eval_pair_bound b D
  exact h1.trans (h2.trans (h3.trans h4))

end Work.WilkiesH.Count
