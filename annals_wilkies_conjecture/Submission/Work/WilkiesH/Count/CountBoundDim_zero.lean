import Mathlib
import Submission.Work.WilkiesH.Count.Defs
import Submission.Work.WilkiesH.Count.dimLE_zero_card
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Basic

/-!
# Area H (counting) — the dimension-`0` case of `CountBoundDim`

`dimLE_zero_card` bounds the cardinality of a finite subset of a definable set
`X ∈ S.Ω F D n` of dimension `≤ 0` by `c * (D + 1) ^ e`.  The dimension-indexed
counting statement `CountBoundDim S F n 0` demands the same bound as the
evaluation of a polynomial in `(D, g, log H)` — all three of which are available
in the conclusion.  So we simply choose the polynomial

`f = c * (X₀ + 1) ^ e`,

whose evaluation at `![D, g, log H]` is `c * (D + 1) ^ e`, independently of `g`
and `H`, and feed it the bound of `dimLE_zero_card`.

The only point that needs care is the inclusion `T ⊆ X`: the hypothesis of
`CountBoundDim` only places `T` inside `degreeHeightLE X.trans g H`, but
`degreeHeightLE Y g H ⊆ Y` and `X.trans ⊆ X`.
-/

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilkiesH.Count

open WilkiesDesign

/-- Evaluation of the counting polynomial `c * (X₀ + 1) ^ e` of `Fin 3` variables
at `(D, g, log H)`: it is `c * (D + 1) ^ e`, independent of `g` and `H`. -/
lemma eval_countPoly (c e : ℕ) (D g H : ℕ) :
    MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log (H : ℝ)]
        (MvPolynomial.C (c : ℝ) *
          ((MvPolynomial.X (0 : Fin 3) + 1 : MvPolynomial (Fin 3) ℝ)) ^ e) =
      (c : ℝ) * ((D : ℝ) + 1) ^ e := by
  simp [Matrix.cons_val_zero]

/-- **Base case of the dimension induction.**  The counting statement
`CountBoundDim S F n μ` at `μ = 0`: a definable set of dimension `≤ 0` has
polynomially many points of bounded degree and height in `D`. -/
theorem CountBoundDim_zero (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (F n : ℕ) :
    Work.WilkiesH.CountBoundDim S F n 0 := by
  obtain ⟨c, e, hce⟩ := dimLE_zero_card S hcd F n
  refine ⟨MvPolynomial.C (c : ℝ) *
    ((MvPolynomial.X (0 : Fin 3) + 1 : MvPolynomial (Fin 3) ℝ)) ^ e, ?_⟩
  intro D X hX hdim g H T hT
  -- `T` sits inside `degreeHeightLE X.trans g H`, hence inside `X`
  have hsub : (↑T : Set (Fin n → ℝ)) ⊆ X := fun x hx => (hT hx).1.1
  have h1 : T.card ≤ c * (D + 1) ^ e := hce D X hX hdim T hsub
  rw [eval_countPoly]
  exact_mod_cast h1

end Work.WilkiesH.Count
