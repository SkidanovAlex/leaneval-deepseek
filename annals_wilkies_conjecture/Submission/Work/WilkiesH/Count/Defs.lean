import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Dim.dimLE_mono

/-!
# Area H (counting) — the dimension-indexed counting statement

The area theorem of the lead's `Holes.lean`,

`CountBound S F n`, says that the points of `X.trans` of bounded degree and
height in a set `X ∈ S.Ω F D n` are counted by a polynomial in
`(D, g, log H)`.

The proof of BNZ §6 is an induction on `μ = dim X`, so the induction statement
carries the dimension bound `DimLE X μ` as a hypothesis.  This file defines that
statement (`CountBoundDim`) and relates it back to the lead's `CountBound`:
since `DimLE X n` holds for every `X ⊆ ℝⁿ` (there is no embedding
`Fin (n+1) ↪ Fin n`), the case `μ = n` of `CountBoundDim` is exactly the area
theorem.
-/

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilkiesH

open WilkiesDesign WilkiesConjecture

/-- `CountBoundDim S F n μ` is the dimension-bounded counting statement: the
points of `X.trans` of degree `≤ g` and height `≤ H` in a set
`X ∈ S.Ω F D n` with `dim X ≤ μ` are counted by a polynomial in
`(D, g, log H)`. -/
def CountBoundDim (S : SOMin) (F n μ : ℕ) : Prop :=
  ∃ f : MvPolynomial (Fin 3) ℝ,
    ∀ (D : ℕ) (X : Set (Fin n → ℝ)), X ∈ S.Ω F D n → DimLE X μ →
      ∀ (g H : ℕ) (T : Finset (Fin n → ℝ)),
        (↑T : Set (Fin n → ℝ)) ⊆ degreeHeightLE X.trans g H →
        (T.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] f

/-- The dimension-bounded counting statement at `μ = n` is the lead's
`CountBound`: `DimLE X n` is vacuous.  This is the bridge that turns a proof of
`CountBoundDim S F n n` into the area theorem `CountBound S F n`. -/
theorem countBound_of_countBoundDim (S : SOMin) (F n : ℕ) (h : CountBoundDim S F n n) :
    CountBound S F n := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun D X hX g H T hT => hf D X hX (dimLE_top X) g H T hT⟩

/-- `CountBoundDim` is monotone in the dimension bound: the statement for the
larger bound `μ'` implies the one for `μ ≤ μ'`, because `DimLE X μ` implies
`DimLE X μ'`. -/
theorem countBoundDim_mono (S : SOMin) {F n μ μ' : ℕ} (h : CountBoundDim S F n μ')
    (hμ : μ ≤ μ') : CountBoundDim S F n μ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun D X hX hXμ g H T hT =>
    hf D X hX (Work.WilkiesH.Dim.dimLE_mono hXμ hμ) g H T hT⟩

end Work.WilkiesH
