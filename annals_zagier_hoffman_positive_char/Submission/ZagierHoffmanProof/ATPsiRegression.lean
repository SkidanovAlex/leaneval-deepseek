import Submission.ZagierHoffmanProof.ATDrinfeld

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the Anderson–Thakur polynomials `Ψ_k`

Concrete instances of `atPsi_vanishes` / `atPsi_X_pow` / `atPsi_self` / `carlitzAct_eq_sum`
over `ZMod 2` and `ZMod 3`. -/

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

section

open PowerSeries

/-- `Ψ_k` vanishes on polynomials of degree `< k` (here: on `1 = θ ^ 0` for `k = 1`). -/
example : atPsi (ZMod 2) 1 (1 : (ZMod 2)[X]) = 0 :=
  atPsi_eq_zero_of_lt_degree _ 1 1 (by rw [Polynomial.natDegree_one]; norm_num)

/-- `Ψ_2` vanishes on `θ`. -/
example : atPsi (ZMod 2) 2 (Polynomial.X : (ZMod 2)[X]) = 0 :=
  atPsi_eq_zero_of_lt_degree _ 2 Polynomial.X (by rw [Polynomial.natDegree_X]; norm_num)

/-- `Ψ_k(θ ^ k) = 1`. -/
example : atPsi (ZMod 2) 1 ((Polynomial.X : (ZMod 2)[X]) ^ 1) = 1 :=
  atPsi_X_pow _ 1

example : atPsi (ZMod 3) 2 ((Polynomial.X : (ZMod 3)[X]) ^ 2) = 1 :=
  atPsi_X_pow _ 2

/-- `Ψ_2` on a degree-`2` polynomial is its leading coefficient. -/
example : atPsi (ZMod 2) 2 ((Polynomial.X : (ZMod 2)[X]) ^ 2 + Polynomial.X) = 1 := by
  rw [atPsi_add, atPsi_X_pow, atPsi_eq_zero_of_lt_degree _ 2 Polynomial.X
    (by rw [Polynomial.natDegree_X]; norm_num), add_zero]

example : atPsi (ZMod 3) 3 ((Polynomial.X : (ZMod 3)[X]) ^ 3 + 2 * Polynomial.X ^ 2
    + Polynomial.X + 1) = 1 := by
  have h1 : atPsi (ZMod 3) 3 (Polynomial.X ^ 2 : (ZMod 3)[X]) = 0 :=
    atPsi_eq_zero_of_lt_degree _ 3 _ (by rw [Polynomial.natDegree_X_pow]; norm_num)
  have h2 : atPsi (ZMod 3) 3 (2 * Polynomial.X ^ 2 : (ZMod 3)[X]) = 0 := by
    rw [show (2 * Polynomial.X ^ 2 : (ZMod 3)[X]) = Polynomial.C 2 * Polynomial.X ^ 2 from rfl,
      atPsi_C_mul, h1, mul_zero]
  have h3 : atPsi (ZMod 3) 3 (Polynomial.X : (ZMod 3)[X]) = 0 :=
    atPsi_eq_zero_of_lt_degree _ 3 _ (by rw [Polynomial.natDegree_X]; norm_num)
  have h4 : atPsi (ZMod 3) 3 (1 : (ZMod 3)[X]) = 0 :=
    atPsi_eq_zero_of_lt_degree _ 3 _ (by rw [Polynomial.natDegree_one]; norm_num)
  have hX3 : atPsi (ZMod 3) 3 ((Polynomial.X : (ZMod 3)[X]) ^ 3) = 1 := atPsi_X_pow _ 3
  rw [show (Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 3)[X])
      = (Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2) + (Polynomial.X + 1) from by ring,
    atPsi_add, atPsi_add, atPsi_add, hX3, h2, h3, h4]
  norm_num

/-- The Drinfeld recursion `Ψ_k(θ a) = θ Ψ_k(a) + Ψ_{k-1}(a) ^ q`, at `k = 2`, `a = θ`. -/
example : atPsi (ZMod 2) 2 ((Polynomial.X : (ZMod 2)[X]) * Polynomial.X) = 1 := by
  rw [atPsi_X_mul, show (2 - 1 : ℕ) = 1 from rfl,
    show atPsi (ZMod 2) 1 (Polynomial.X : (ZMod 2)[X]) = 1 from by
      rw [show (Polynomial.X : (ZMod 2)[X]) = Polynomial.X ^ 1 from (pow_one _).symm, atPsi_X_pow],
    one_pow, atPsi_eq_zero_of_lt_degree _ 2 Polynomial.X (by rw [Polynomial.natDegree_X]; norm_num),
    mul_zero, zero_add, if_neg (by norm_num)]

/-- `C_θ(f) = θ f + f ^ q` (the Drinfeld structure of the Carlitz module). -/
example (f : PowerSeries (RatFunc (ZMod 2))) :
    carlitzAct (ZMod 2) (Polynomial.X : (ZMod 2)[X]) f
      = PowerSeries.C (carlitzTheta (ZMod 2)) * f + f ^ 2 :=
  (carlitzAct_X_apply (ZMod 2) f).trans (by rw [show Nat.card (ZMod 2) = 2 from by
    rw [Nat.card_eq_fintype_card, ZMod.card]])

/-- `Ψ_0` is the linear coefficient: `Ψ_0(a) = a` (`C_a(x) = a x + ` higher terms). -/
example : atPsi (ZMod 2) 0 (Polynomial.X : (ZMod 2)[X])
    = carlitzTheta (ZMod 2) := by
  rw [atPsi_zero_eq]
  rfl

/-- ★ The Drinfeld-module expansion on `θ`: `C_θ(f) = θ f + f ^ q`. -/
example (f : PowerSeries (RatFunc (ZMod 2))) :
    carlitzAct (ZMod 2) (Polynomial.X : (ZMod 2)[X]) f
      = PowerSeries.C (carlitzTheta (ZMod 2)) * f + f ^ 2 := by
  rw [carlitzAct_eq_sum, Polynomial.natDegree_X, Finset.sum_range_succ, Finset.sum_range_one,
    show (Polynomial.X : (ZMod 2)[X]) = Polynomial.X ^ 1 from (pow_one _).symm,
    atPsi_X_pow, atPsi_zero_eq, map_pow,
    show (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2))) Polynomial.X = carlitzTheta (ZMod 2) from rfl]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- ★ The Drinfeld-module expansion on `θ ^ 2` over `ZMod 3`, degree-`2` case. -/
example : atPsi (ZMod 3) 2 ((Polynomial.X : (ZMod 3)[X]) ^ 2) = 1 := atPsi_X_pow _ 2

end

end ZagierHoffmanPositiveChar
