import Mathlib
import Submission.Work.C17.adjoint_C_defs
import Submission.Work.C17adj.adjoint_clearing

/-!
# Clearing denominators in the adjoint certificate over `ℂ`

This file proves `Work.C17adj2.adjoint_clearingL`: if `β = N/D` (with `D = X^6(X-1)^2(X+1)^2`)
satisfies the inhomogeneous second order equation
`(P₂β)'' - (P₁β)' + P₀β = Σᵢ cᵢ y^{i-4} dy`
in `ℂ(x)` (with `y = x²/(x-1)`), then the cleared polynomial identity `EpolyL = 0` holds.

The argument is the `ℂ`-copy of `Work.C17adj.adjoint_clearing`: after multiplying by `D³`, the
generic denominator-clearing identity `Work.C17adj.dRat_clearing_general` (valid over any field)
turns the left hand side into `LeftPolyL`, and the right hand side is cleared termwise by the
computation `gD3L_clearing`.
-/

namespace Work.C17adj2

open Polynomial

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Clearing the denominators of `Σᵢ cᵢ y^{i-4} dy` over `ℂ` -/

/-- `yQc^{i-4} · dyQc` cleared against `DadjL^3` gives exactly the polynomial `gD3L i`. -/
theorem gD3L_clearing (i : Fin 6) :
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL) ^ 3
        * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.gD3L i) := by
  have hx1 : (RatFunc.X : RatFunc ℂ) - 1 ≠ 0 := by
    intro h
    have h2 : (RatFunc.X : RatFunc ℂ) = 1 := sub_eq_zero.mp h
    rw [← RatFunc.algebraMap_X, ← map_one (algebraMap (Polynomial ℂ) (RatFunc ℂ))] at h2
    have h3 : (Polynomial.X : Polynomial ℂ) = 1 :=
      IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) h2
    have h4 : (Polynomial.X - 1 : Polynomial ℂ) ≠ 0 := by
      intro hh
      have hc := congrArg (fun p : Polynomial ℂ => p.eval 0) hh
      norm_num at hc
    exact h4 (sub_eq_zero.mpr h3)
  fin_cases i <;>
    simp only [Work.C17.yQc, Work.C17.dyQc, RatFunc.algebraMap_X] <;>
    norm_num <;>
    simp [Work.C17C.DadjL, Work.C17C.gD3L, Work.C17C.gD3L_0, Work.C17C.gD3L_1,
      Work.C17C.gD3L_2, Work.C17C.gD3L_3, Work.C17C.gD3L_4, Work.C17C.gD3L_5, map_ofNat] <;>
    field_simp <;>
    ring

/-- The cleared right hand side: `DadjL^3 · Σᵢ cᵢ y^{i-4} dyQc = RightPolyL c`. -/
theorem RhsYc_clearing (c : Fin 6 → ℂ) :
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL) ^ 3 * Work.C17C.RhsYc c
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.RightPolyL c) := by
  have per_i : ∀ i : Fin 6,
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL) ^ 3
        * (Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.gD3L i) := by
    intro i
    rw [← mul_assoc]
    exact gD3L_clearing i
  rw [Work.C17C.RhsYc, Work.C17C.RightPolyL, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL) ^ 3 *
        (algebraMap ℂ (RatFunc ℂ) (c i) * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc)
      = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (c i))) *
        ((algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL) ^ 3 *
          (Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc)) by
    rw [show (algebraMap ℂ (RatFunc ℂ) (c i))
          = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (c i)) from by
      rw [Polynomial.C_eq_algebraMap]
      exact (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) (c i)).symm]
    ring]
  rw [per_i i, ← map_mul]

/-! ## The left hand side: the generic clearing identity over `ℂ` -/

/-- Clearing `DadjL^3` from `(P₂·n/d)'' - (P₁·n/d)' + P₀·n/d` gives `LeftPolyL`. -/
theorem LeftPolyL_clearing (a b : ℂ) (n : Fin 7 → ℂ) :
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL) ^ 3 *
      (Submission.CDT.dRat (Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (Work.C17C.P2xL a b) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.NpolyL n)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL)))
       - Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.P1xL a b) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.NpolyL n)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL))
       + algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.P0xL a b) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.NpolyL n)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL))
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.LeftPolyL a b n) := by
  rw [Work.C17adj.dRat_clearing_general (Work.C17C.P2xL a b) (Work.C17C.P1xL a b)
    (Work.C17C.P0xL a b) (Work.C17C.NpolyL n) Work.C17C.DadjL Work.C17C.DadjL_ne_zero]
  apply congrArg (algebraMap (Polynomial ℂ) (RatFunc ℂ))
  rw [← Work.C17C.BadjL_eq_deriv a b, ← Work.C17C.CadjL_eq_deriv a b,
    Work.C17C.NpolyL_derivative, Work.C17C.NpolyDL_derivative,
    Work.C17C.DadjL_derivative, Work.C17C.Dadj1L_derivative]
  simp only [Work.C17C.LeftPolyL]

/-! ## The main clearing statement -/

/-- **Adjoint certificate, denominator clearing (over `ℂ`).**  If `β = N/D` with
`D = X^6(X-1)^2(X+1)^2` solves the inhomogeneous equation
`(P₂β)'' - (P₁β)' + P₀β = Σᵢ cᵢ y^{i-4} dy` in `ℂ(x)`, then the cleared polynomial identity
`EpolyL a b n c = 0` holds. -/
theorem adjoint_clearingL (a b : ℚ) (n : Fin 7 → ℂ) (c : Fin 6 → ℂ) (β : RatFunc ℂ)
    (hβ : β = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.NpolyL n)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.DadjL))
    (h : Work.C17C.AdjOpL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) β = Work.C17C.RhsYc c) :
    Work.C17C.EpolyL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) n c = 0 := by
  have hA : (algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL) ^ 3
        * Work.C17C.AdjOpL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) β
      = (algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17C.DadjL) ^ 3 * Work.C17C.RhsYc c := by
    rw [h]
  rw [hβ, Work.C17C.AdjOpL] at hA
  rw [LeftPolyL_clearing ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) n, RhsYc_clearing c] at hA
  have hzero : algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Work.C17C.EpolyL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) n c) = 0 := by
    rw [Work.C17C.EpolyL, map_sub, hA, sub_self]
  exact IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [hzero, map_zero])

end

end Work.C17adj2
