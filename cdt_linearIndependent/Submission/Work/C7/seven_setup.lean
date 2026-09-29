import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.C7.gsetup

/-!
# Area C7 — setup for the `x`-side proof that `B₁,…,B₇` are `ℚ(x)`-independent

The pullbacks `g i = Bᵢ ∘ y` of the seven pure functions along `y = x²/(x-1)`
(`Work.C7.g`) satisfy (`h0`–`h4`, `h6`, `h7` of `Work.C7.indep_seven`)

* `g 0 = 1`, `g 1 = 2y − cL`, `g 2 = −½L²`, `g 3 = c(2Li₂ + ½L²)`, `g 4 = (x/(x−1))J`
  with `c = x − φ = x(x−2)/(x−1)` the "difference" `x - x/(x-1)`, and
* `y·(g 5)' = (g 2)·y'`, `y·(g 6)' = (g 3)·y'` (so `g 5`, `g 6` are the two "integrals").

The five functions `f5 0 = 1`, `f5 1 = L = log(1−x)`, `f5 2 = L²`, `f5 3 = Li₂(x)`,
`f5 4 = J(x)` are `ℚ(x)`-linearly independent (`hind`).

This module sets up the derivation that makes the elimination argument polynomial:

  `∂ = x(x−1)²·d/dx`.

`∂` keeps the `ℚ[x]`-span of `f5 0,…,f5 4, g 5, g 6` closed *with polynomial coefficients*
(`dsh_Lps`, `dsh_Lps_sq`, `dsh_Li2ps`, and `dsh_jps`, `dsh_g5`, `dsh_g6` in `dsh_pull`),
which is what lets the elimination be run with `PolyIndependent` (polynomial coefficients)
rather than over the field `ℚ(x)`.
-/

noncomputable section

namespace Work.C7

open PowerSeries
open scoped BigOperators

/-- The derivation `∂ = x(x-1)²·d/dx` of `ℚ⟦x⟧`. -/
def dsh (u : PowerSeries ℚ) : PowerSeries ℚ :=
  (PowerSeries.X * (PowerSeries.X - 1) ^ 2) * PowerSeries.derivative (R := ℚ) u

/-- `∂` on polynomials, again a polynomial: `x(x-1)²·p'`. -/
def dshP (p : Polynomial ℚ) : Polynomial ℚ :=
  Polynomial.X * (Polynomial.X - 1) ^ 2 * Polynomial.derivative p

/-- The five `ℚ(x)`-independent basis functions `1, L, L², Li₂, J` of the x-side. -/
def f5 : Fin 5 → PowerSeries ℚ := fun i => ![1, Lps, Lps ^ 2, Li2ps, Jps] i

@[simp] lemma f5_zero : f5 0 = 1 := rfl
@[simp] lemma f5_one : f5 1 = Lps := rfl
@[simp] lemma f5_two : f5 2 = Lps ^ 2 := rfl
@[simp] lemma f5_three : f5 3 = Li2ps := rfl
@[simp] lemma f5_four : f5 4 = Jps := rfl

/-- The coefficient extraction used at the end of every case: a `ℚ[x]`-relation among the five
basis functions has all coefficients zero (`hind` for `f5`). -/
lemma f5_rel_zero (hind : Submission.CDTPlan.PolyIndependent f5) (B : Fin 5 → Polynomial ℚ)
    (h : ∑ j, (B j : PowerSeries ℚ) * f5 j = 0) : ∀ j, B j = 0 :=
  hind B h

/-! ## Elementary calculus with `∂` -/

@[simp] lemma dsh_zero : dsh 0 = 0 := by simp [dsh]

@[simp] lemma dsh_one : dsh 1 = 0 := by simp [dsh]

lemma dsh_add (u v : PowerSeries ℚ) : dsh (u + v) = dsh u + dsh v := by
  have h : (PowerSeries.derivative (R := ℚ)) (u + v)
      = (PowerSeries.derivative (R := ℚ)) u + (PowerSeries.derivative (R := ℚ)) v := Derivation.map_add _ _ _
  simp only [dsh, h, mul_add]

lemma dsh_neg (u : PowerSeries ℚ) : dsh (-u) = -dsh u := by
  have h : (PowerSeries.derivative (R := ℚ)) (-u) = -(PowerSeries.derivative (R := ℚ)) u := Derivation.map_neg _ _
  simp only [dsh, h]
  ring

lemma dsh_sub (u v : PowerSeries ℚ) : dsh (u - v) = dsh u - dsh v := by
  have h : (PowerSeries.derivative (R := ℚ)) (u - v)
      = (PowerSeries.derivative (R := ℚ)) u - (PowerSeries.derivative (R := ℚ)) v := Derivation.map_sub _ _ _
  simp only [dsh, h, mul_sub]

lemma dsh_mul (u v : PowerSeries ℚ) : dsh (u * v) = dsh u * v + u * dsh v := by
  simp only [dsh]
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

@[simp] lemma dsh_C (c : ℚ) : dsh (PowerSeries.C c) = 0 := by
  simp [dsh]

lemma dsh_smul_C (c : ℚ) (u : PowerSeries ℚ) :
    dsh (PowerSeries.C c * u) = PowerSeries.C c * dsh u := by
  rw [dsh_mul, dsh_C, zero_mul, zero_add]

@[simp] lemma dsh_X : dsh (PowerSeries.X : PowerSeries ℚ)
    = PowerSeries.X * (PowerSeries.X - 1) ^ 2 := by
  simp [dsh]

lemma dsh_sum {ι : Type*} (s : Finset ι) (u : ι → PowerSeries ℚ) :
    dsh (∑ i ∈ s, u i) = ∑ i ∈ s, dsh (u i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, dsh_add, ih]

/-! ## `∂` of polynomials -/

@[simp] lemma dshP_zero : dshP 0 = 0 := by simp [dshP]

@[simp] lemma dshP_one : dshP 1 = 0 := by simp [dshP]

@[simp] lemma dshP_C (c : ℚ) : dshP (Polynomial.C c) = 0 := by simp [dshP]

@[simp] lemma dshP_X : dshP (Polynomial.X : Polynomial ℚ)
    = Polynomial.X * (Polynomial.X - 1) ^ 2 := by simp [dshP]

lemma dshP_add (p q : Polynomial ℚ) : dshP (p + q) = dshP p + dshP q := by
  simp only [dshP, Polynomial.derivative_add]
  ring

lemma dshP_mul (p q : Polynomial ℚ) : dshP (p * q) = dshP p * q + p * dshP q := by
  simp only [dshP, Polynomial.derivative_mul]
  ring

/-- `∂` of a polynomial, viewed inside `ℚ⟦x⟧`, agrees with `dshP`. -/
lemma dsh_coe (p : Polynomial ℚ) :
    dsh ((p : PowerSeries ℚ)) = ((dshP p : Polynomial ℚ) : PowerSeries ℚ) := by
  simp only [dsh, dshP, PowerSeries.derivative_coe]
  push_cast
  ring

/-! ## Elementary facts about the symmetrization data -/

lemma constantCoeff_X_sub_one :
    PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℚ) - 1) = -1 := by
  rw [map_sub, PowerSeries.constantCoeff_X, map_one]
  norm_num

lemma yps_eq_Xsq :
    yps = (PowerSeries.X : PowerSeries ℚ) ^ 2 * ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ := by
  rw [yps, Submission.CDT.sympY, Submission.CDT.sympPhi]
  ring

/-- `y·(x-1) = x²`. -/
lemma yps_mul_sub_one_seven_setup : yps * ((PowerSeries.X : PowerSeries ℚ) - 1) = PowerSeries.X ^ 2 := by
  rw [yps_eq_Xsq]
  have h := mul_gU
  linear_combination ((PowerSeries.X : PowerSeries ℚ) ^ 2) * h

/-- `(x-1)²·y = x²(x-1)`. -/
lemma sq_sub_one_mul_yps :
    ((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2 * yps
      = PowerSeries.X ^ 2 * ((PowerSeries.X : PowerSeries ℚ) - 1) := by
  rw [yps_eq_Xsq]
  have h := mul_gU
  linear_combination ((PowerSeries.X : PowerSeries ℚ) ^ 2 * ((PowerSeries.X : PowerSeries ℚ) - 1)) * h

/-- `y'(x-1) + y = 2x`, the derivative of `y(x-1) = x²`. -/
lemma deriv_yps_mul_sub_one_add :
    PowerSeries.derivative (R := ℚ) yps * ((PowerSeries.X : PowerSeries ℚ) - 1) + yps
      = 2 * PowerSeries.X := by
  have hder : PowerSeries.derivative (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) - 1) = 1 := by
    rw [map_sub, PowerSeries.derivative_X, PowerSeries.derivative_one, sub_zero]
  have h2 : PowerSeries.derivative (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2)
      = 2 * PowerSeries.X := by
    rw [show (PowerSeries.X : PowerSeries ℚ) ^ 2 = PowerSeries.X * PowerSeries.X by ring,
      Derivation.leibniz]
    simp only [smul_eq_mul, PowerSeries.derivative_X]
    ring
  have h := congrArg (PowerSeries.derivative (R := ℚ)) yps_mul_sub_one_seven_setup
  rw [Derivation.leibniz, hder, h2] at h
  simp only [smul_eq_mul, mul_one] at h
  linear_combination h

/-- `(x-1)²·y' = x(x-2)`. -/
lemma sq_sub_one_mul_deriv_yps :
    ((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2 * PowerSeries.derivative (R := ℚ) yps
      = PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) - 2) := by
  have key := deriv_yps_mul_sub_one_add
  linear_combination ((PowerSeries.X : PowerSeries ℚ) - 1) * key
    - (1 : PowerSeries ℚ) * yps_mul_sub_one_seven_setup

/-- `c = x - φ = x(x-2)/(x-1)`. -/
lemma cfun_sub_phi :
    (PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi = cfun := by
  rw [cfun, Submission.CDT.sympPhi]
  have h := mul_gU
  linear_combination (-(PowerSeries.X : PowerSeries ℚ)) * h

lemma cfun_eq' : cfun = (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2)
    * ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ := rfl

/-! ## `∂` of the five basis functions -/

/-- `∂L = x(x-1)`. -/
lemma dsh_Lps : dsh Lps = PowerSeries.X * (PowerSeries.X - 1) := by
  rw [dsh, deriv_Lps_gU]
  have h := mul_gU
  linear_combination ((PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 1)) * h

/-- `∂(L²) = 2x(x-1)L`. -/
lemma dsh_Lps_sq : dsh (Lps ^ 2) = 2 * PowerSeries.X * (PowerSeries.X - 1) * Lps := by
  rw [show (Lps : PowerSeries ℚ) ^ 2 = Lps * Lps by ring, dsh_mul, dsh_Lps]
  ring

/-- `∂Li₂ = -(x-1)²L`. -/
lemma dsh_Li2ps : dsh Li2ps = -((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2 * Lps := by
  have h := deriv_Li2ps
  rw [dsh]
  linear_combination ((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2 * h

end Work.C7
