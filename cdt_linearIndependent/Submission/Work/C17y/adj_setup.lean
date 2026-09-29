import Mathlib
import Submission.Work.C17y.defs
import Submission.Work.C17.adjoint_defs
import Submission.Work.C17adj.divisor_defs
import Submission.Work.C17adj.rhs_ord
import Submission.Work.C17adj.adjoint_base_change
import Submission.Work.C17adj.adjoint_clearing
import Submission.Work.C17y.RiccatiSelfContained

/-!
# Vocabulary for the adjoint non-existence theorem (`Work.C17y.adjoint_no_solution_rat`)

This module fixes the objects used by the proof of `Work.C17y.adjoint_no_solution_rat`:

* `LBE a b B = Lst a b (B / P₂)` (`LBE_eq_Lst_div`): the operator tested by the theorem is the
  formal adjoint `Lst` of `M` applied to `β = B/P₂`;
* `AdjOpC a b β`: the `ℂ`-image of `Lst`;
* `Sfun a b β = P₂·β' − (P₁ − P₂')·β`, the first-order companion of the adjoint operator, with
  `dRat (Sfun a b β) = AdjOpC a b β − P₀·β` (`dRat_Sfun`).

The divisor bound for `β` (pole bounds at the finite points and the degree bound at `∞`) is
proved in the sibling modules `adj_ord_bound` and `adj_deg_bound`; the certificate for the
admissible pair `(a,b)` (`Work.C17.linear_core`) then closes the argument.
-/

namespace Work.C17y

open Polynomial

noncomputable section

/-- The adjoint operator `(P₂β)'' − (P₁β)' + P₀β` over `ℂ`: the `ℂ`-image of `Work.C17y.Lst`. -/
def AdjOpC (a b : ℚ) (β : RatFunc ℂ) : RatFunc ℂ :=
  Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
    - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β

/-- `S = P₂·β' − (P₁ − P₂')·β`, the first-order companion of the adjoint operator:
`S' = (P₂β)'' − (P₁β)' + P₀·β` (`dRat_Sfun`). -/
def Sfun (a b : ℚ) (β : RatFunc ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P2C a b) * Submission.CDT.dRat β
    - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Work.C17.P1C a b - (Work.C17.P2C a b).derivative) * β

/-- `P₂ = x(x²−1)Q₄` is nonzero. -/
theorem P2Q_ne_zero (a b : ℚ) : Work.C17.P2Q a b ≠ 0 := by
  rw [Work.C17.P2Q]
  intro h
  have h2 : Work.C17.P2x a b = 0 :=
    IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) (by simpa using h)
  have h3 := P2x_natDegree a b
  rw [h2] at h3
  simp at h3

/-- `D = x⁶(x²−1)²` is nonzero. -/
theorem Dadj_ne_zero' : (Work.C17.Dadj : Polynomial ℚ) ≠ 0 := Work.C17adj.Dadj_ne_zero

/-- **The operator tested by the theorem is the formal adjoint of `M`.** -/
theorem LBE_eq_Lst_div (a b : ℚ) (B : RatFunc ℚ) :
    LBE a b B = Lst a b (B / Work.C17.P2Q a b) := by
  have hq : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P2x a b) ≠ 0 := P2Q_ne_zero a b
  have h1 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P2x a b)
      * (B / Work.C17.P2Q a b) = B := by
    rw [Work.C17.P2Q, ← mul_div_assoc, mul_div_cancel_left₀ _ hq]
  have h2 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P1x a b)
      * (B / Work.C17.P2Q a b) = p1Q a b * B := by
    rw [p1Q, Work.C17.P2Q, ← mul_div_assoc, div_mul_eq_mul_div]
  have h3 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P0x a b)
      * (B / Work.C17.P2Q a b) = p0Q a b * B := by
    rw [p0Q, Work.C17.P2Q, ← mul_div_assoc, div_mul_eq_mul_div]
  rw [LBE, Lst, h1, h2, h3, Submission.CDT.dRat_mul]
  ring

/-- The first-order identity: the derivative of `S = P₂β' − (P₁ − P₂')β` is the adjoint
expression minus `P₀·β`. -/
theorem dRat_Sfun (a b : ℚ) (β : RatFunc ℂ) :
    Submission.CDT.dRat (Sfun a b β) = AdjOpC a b β
      - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P0C a b) * β := by
  have e2 : Work.C17.Pac a b
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P2C a b) := rfl
  have e1 : Work.C17.Pbc a b
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P1C a b) := rfl
  have e0 : Work.C17.Pcc a b
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P0C a b) := rfl
  simp only [Sfun, AdjOpC, e2, e1, e0, Submission.CDT.dRat_mul, Submission.CDT.dRat_sub,
    Submission.CDT.dRat_add, Submission.CDT.dRat_algebraMap, map_sub, Polynomial.derivative_sub]
  ring

end

end Work.C17y
