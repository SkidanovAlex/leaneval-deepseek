import Mathlib
import Submission.Work.CDcl.setup

/-!
# The φ-symmetrisation of a polynomial is a polynomial in `y`

`symPoly n ∈ ℚ[y]` is the polynomial with `(symPoly n)(y) = x^n + φ(x)^n`; hence for any
`P ∈ ℚ[x]`, `P(x) + P(x/(x-1)) = p(y)` with the polynomial `p = Σ_k (coeff k P) • symPoly k`.

This is `Work.CDcl.inv_sum`.
-/

noncomputable section

namespace Work.CDcl

open Polynomial PowerSeries

/-- `symPoly n (y) = x^n + φ(x)^n` (as a polynomial in `y`):
`symPoly 0 = 2`, `symPoly 1 = y`, `symPoly (n+2) = y * (symPoly (n+1) - symPoly n)`. -/
def symPoly : ℕ → Polynomial ℚ
  | 0 => 2
  | 1 => Polynomial.X
  | n + 2 => Polynomial.X * (symPoly (n + 1) - symPoly n)

/-- the defining recurrence, in the shape used by induction -/
theorem symPoly_succ_succ (n : ℕ) :
    symPoly (n + 2) = Polynomial.X * (symPoly (n + 1) - symPoly n) := rfl

/-- `symPoly n (y) = x^n + φ(x)^n` as power series in `x`. -/
theorem symPoly_subst (n : ℕ) :
    ((symPoly n : Polynomial ℚ) : PowerSeries ℚ).subst Submission.CDT.sympY
      = Submission.CDT.sympP n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      show PowerSeries.subst Submission.CDT.sympY ((2 : Polynomial ℚ) : PowerSeries ℚ)
        = Submission.CDT.sympP 0
      rw [Submission.CDT.sympP_zero]
      have h2 : ((2 : Polynomial ℚ) : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) := by
        rw [show (2 : Polynomial ℚ) = Polynomial.C (2 : ℚ) from (Polynomial.C_eq_natCast 2).symm]
        exact Polynomial.coe_C 2
      rw [h2, PowerSeries.subst_C]
      exact map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
  | one =>
      show PowerSeries.subst Submission.CDT.sympY ((Polynomial.X : Polynomial ℚ) : PowerSeries ℚ)
        = Submission.CDT.sympP 1
      have hX : ((Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) = (PowerSeries.X : PowerSeries ℚ) :=
        Polynomial.coe_X
      rw [Submission.CDT.sympP_one, hX, PowerSeries.subst_X Submission.CDT.sympY_hasSubst]
  | more n ih1 ih2 =>
      have hcast : (((Polynomial.X * (symPoly (n + 1) - symPoly n) : Polynomial ℚ)) : PowerSeries ℚ)
          = (PowerSeries.X : PowerSeries ℚ)
            * (((symPoly (n+1) : Polynomial ℚ) : PowerSeries ℚ)
                - ((symPoly n : Polynomial ℚ) : PowerSeries ℚ)) := by
        push_cast
        ring
      rw [symPoly_succ_succ n, hcast]
      rw [PowerSeries.subst_mul Submission.CDT.sympY_hasSubst,
        PowerSeries.subst_sub Submission.CDT.sympY_hasSubst,
        PowerSeries.subst_X Submission.CDT.sympY_hasSubst, ih1, ih2,
        Submission.CDT.sympP_succ_succ n]
      ring

/-- the symmetrisation identity for polynomials, with the explicit polynomial `Σ c_k symPoly k`. -/
theorem inv_sum_aux (P : Polynomial ℚ) :
    (P : PowerSeries ℚ) + (P : PowerSeries ℚ).subst Submission.CDT.sympPhi
      = (((P.sum (fun k c => Polynomial.C c * symPoly k)) : Polynomial ℚ) :
            PowerSeries ℚ).subst Submission.CDT.sympY := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      have hsum : ((p + q).sum (fun k c => Polynomial.C c * symPoly k))
          = (p.sum (fun k c => Polynomial.C c * symPoly k))
            + (q.sum (fun k c => Polynomial.C c * symPoly k)) := by
        rw [Polynomial.sum_add_index]
        · intro i; simp
        · intro i b₁ b₂
          simp only [map_add]
          ring
      rw [hsum]
      push_cast
      rw [PowerSeries.subst_add Submission.CDT.sympY_hasSubst,
        PowerSeries.subst_add Submission.CDT.sympPhi_hasSubst]
      rw [show ((p : PowerSeries ℚ) + (q : PowerSeries ℚ))
              + ((p : PowerSeries ℚ).subst Submission.CDT.sympPhi
                 + (q : PowerSeries ℚ).subst Submission.CDT.sympPhi)
            = ((p : PowerSeries ℚ) + (p : PowerSeries ℚ).subst Submission.CDT.sympPhi)
              + ((q : PowerSeries ℚ) + (q : PowerSeries ℚ).subst Submission.CDT.sympPhi) from by ring]
      rw [hp, hq]
  | monomial n a =>
      have hsum : ((Polynomial.monomial n a).sum (fun k c => Polynomial.C c * symPoly k))
          = Polynomial.C a * symPoly n := by
        rw [Polynomial.sum_monomial_index a _ (by simp)]
      rw [hsum]
      have hmono : ((Polynomial.monomial n a : Polynomial ℚ) : PowerSeries ℚ)
          = PowerSeries.C a * (PowerSeries.X : PowerSeries ℚ) ^ n := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        push_cast
        ring
      rw [hmono]
      have hsub : ((Polynomial.C a * symPoly n : Polynomial ℚ) : PowerSeries ℚ)
          = PowerSeries.C a * ((symPoly n : Polynomial ℚ) : PowerSeries ℚ) := by
        push_cast
        ring
      rw [hsub, PowerSeries.subst_mul Submission.CDT.sympY_hasSubst, PowerSeries.subst_C,
        symPoly_subst n]
      rw [PowerSeries.subst_mul Submission.CDT.sympPhi_hasSubst, PowerSeries.subst_C,
        PowerSeries.subst_pow Submission.CDT.sympPhi_hasSubst,
        PowerSeries.subst_X Submission.CDT.sympPhi_hasSubst]
      rw [Submission.CDT.sympP]
      rw [mul_add, mul_comm (PowerSeries.C a) ((PowerSeries.X : PowerSeries ℚ) ^ n),
        mul_comm (MvPowerSeries.C a) ((PowerSeries.X : PowerSeries ℚ) ^ n)]
      rfl

/-- **`Work.CDcl.inv_sum`**: the φ-symmetrisation `P(x) + P(x/(x-1))` of a polynomial is a
rational function of `y = x²/(x-1)` (in fact a polynomial in `y`). -/
theorem inv_sum (P : Polynomial ℚ) :
    ∃ p q : Polynomial ℚ, q ≠ 0 ∧
      ((q : PowerSeries ℚ).subst Submission.CDT.sympY)
        * ((P : PowerSeries ℚ) + (P : PowerSeries ℚ).subst Submission.CDT.sympPhi)
      = (p : PowerSeries ℚ).subst Submission.CDT.sympY := by
  refine ⟨P.sum (fun k c => Polynomial.C c * symPoly k), 1, one_ne_zero, ?_⟩
  have hq : ((1 : Polynomial ℚ) : PowerSeries ℚ).subst Submission.CDT.sympY = 1 := by
    have h1 : ((1 : Polynomial ℚ) : PowerSeries ℚ) = PowerSeries.C (1 : ℚ) := by
      rw [show (1 : Polynomial ℚ) = Polynomial.C (1 : ℚ) from (Polynomial.C_eq_natCast 1).symm]
      exact Polynomial.coe_C 1
    rw [h1, PowerSeries.subst_C]
    exact map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1
  rw [hq, one_mul, inv_sum_aux P]

end Work.CDcl
