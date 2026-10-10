import Mathlib
import Submission.Work.MotAS.SdualAS2Explicit
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

section

variable {K : Type*} [Field K]

/-! ## Splitting `sdualAS2` as a polynomial in `X 0`

`MvPolynomial.finSuccEquiv K 2` views a polynomial in `X 0, X 1, X 2` as a polynomial in `X 0`
whose coefficients are polynomials in `X 1, X 2` (sent to `X 0, X 1` of the two-variable ring).
The explicit form `sdualAS2_explicit` shows that `sdualAS2 a b g` is a sum of terms
`c * X 0 ^ p * X 1 ^ q * X 2 ^ r` with `p ≤ 5`, and that the terms with `p = 5` reduce to the
single monomial `X 0 ^ 5` with coefficient `g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)`.

Below, `sd5 … sd0` are the coefficients of `X 0 ^ 5, …, X 0 ^ 0` (as polynomials in the two
remaining variables), transcribed verbatim from `sdualAS2_explicit`. -/

/-- `finSuccEquiv` sends constants to constants. -/
theorem sdFinSuccEquiv_C (r : K) :
    MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C r)
      = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq K (Fin 3), AlgEquiv.commutes, Polynomial.algebraMap_apply]
  rfl

theorem sdFinSuccEquiv_X_1 :
    MvPolynomial.finSuccEquiv K 2 (X 1 : MvPolynomial (Fin 3) K)
      = Polynomial.C (X 0 : MvPolynomial (Fin 2) K) := by
  rw [show (1 : Fin 3) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ]

theorem sdFinSuccEquiv_X_2 :
    MvPolynomial.finSuccEquiv K 2 (X 2 : MvPolynomial (Fin 3) K)
      = Polynomial.C (X 1 : MvPolynomial (Fin 2) K) := by
  rw [show (2 : Fin 3) = Fin.succ 1 from rfl, MvPolynomial.finSuccEquiv_X_succ]

/-- The coefficient of `X 0 ^ 5` in `sdualAS2 a b g`. -/
noncomputable def sd5 (a b g : K) : MvPolynomial (Fin 2) K :=
    (C a ^(10:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + -C b ^(10:ℕ) * C g)

/-- The coefficient of `X 0 ^ 4` in `sdualAS2 a b g`. -/
noncomputable def sd4 (a b g : K) : MvPolynomial (Fin 2) K :=
    (-C a ^(10:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) + C b ^(10:ℕ))

/-- The coefficient of `X 0 ^ 3` in `sdualAS2 a b g`. -/
noncomputable def sd3 (a b g : K) : MvPolynomial (Fin 2) K :=
    (-C a ^(9:ℕ) * C b + -C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ)) * X 0 * X 1
      + ((-2 : MvPolynomial (Fin 2) K) * C a ^(10:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(5:ℕ) * C b ^(5:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C b ^(10:ℕ) * C g) * X 1 ^(2:ℕ)

/-- The coefficient of `X 0 ^ 2` in `sdualAS2 a b g`. -/
noncomputable def sd2 (a b g : K) : MvPolynomial (Fin 2) K :=
    ((2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ)) * X 0 ^(3:ℕ)
      + (-C a ^(10:ℕ) * C g + C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C b ^(10:ℕ) * C g) * X 0 ^(2:ℕ) * X 1
      + (-C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 * X 1 ^(2:ℕ)
      + (-C a ^(10:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) + C b ^(10:ℕ)) * X 0
      + ((2 : MvPolynomial (Fin 2) K) * C a ^(10:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + -C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(5:ℕ) * C b ^(5:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C b ^(10:ℕ)) * X 1 ^(2:ℕ)

/-- The coefficient of `X 0 ^ 1` in `sdualAS2 a b g`. -/
noncomputable def sd1 (a b g : K) : MvPolynomial (Fin 2) K :=
    (-C a ^(10:ℕ) * C g + C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C b ^(10:ℕ) * C g) * X 0 ^(4:ℕ)
      + (C a ^(10:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + -C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) + -C b ^(10:ℕ)) * X 0 ^(2:ℕ) * X 1
      + (C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 * X 1 ^(3:ℕ)
      + ((-2 : MvPolynomial (Fin 2) K) * C a ^(10:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(5:ℕ) * C b ^(5:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C b ^(10:ℕ) * C g) * X 0 * X 1 ^(2:ℕ)
      + (C a ^(10:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) * C g + C a ^(7:ℕ) * C b ^(3:ℕ) * C g + -C a ^(6:ℕ) * C b ^(4:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C a ^(4:ℕ) * C b ^(6:ℕ) * C g + C a ^(3:ℕ) * C b ^(7:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) * C g + -C b ^(10:ℕ) * C g) * X 1 ^(4:ℕ)
      + ((-2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b + C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ)) * X 1 ^(3:ℕ)
      + (C a ^(10:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) + -C b ^(10:ℕ)) * X 1

/-- The coefficient of `X 0 ^ 0` in `sdualAS2 a b g`. -/
noncomputable def sd0 (a b g : K) : MvPolynomial (Fin 2) K :=
    (C a ^(10:ℕ) * C g ^(2:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) + -C b ^(10:ℕ) * C g ^(2:ℕ)) * X 0 ^(5:ℕ)
      + (C a ^(10:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) + -C b ^(10:ℕ)) * X 0 ^(4:ℕ)
      + (C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 ^(3:ℕ) * X 1 ^(2:ℕ)
      + (C a ^(10:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + -C b ^(10:ℕ) * C g) * X 0 ^(3:ℕ) * X 1
      + (-C a ^(9:ℕ) * C b * C g + -C a ^(8:ℕ) * C b ^(2:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(7:ℕ) * C b ^(3:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(3:ℕ) * C b ^(7:ℕ) * C g + C a ^(2:ℕ) * C b ^(8:ℕ) * C g + -C a * C b ^(9:ℕ) * C g) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
      + (-C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ)
      + ((-2 : MvPolynomial (Fin 2) K) * C a ^(10:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(5:ℕ) * C b ^(5:ℕ) + (2 : MvPolynomial (Fin 2) K) * C b ^(10:ℕ)) * X 0 ^(2:ℕ)
      + (-C a ^(10:ℕ) * C g ^(2:ℕ) + C a ^(9:ℕ) * C b + C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ) + C b ^(10:ℕ) * C g ^(2:ℕ)) * X 0 * X 1 ^(4:ℕ)
      + (-C a ^(10:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) + C b ^(10:ℕ)) * X 0 * X 1 ^(2:ℕ)
      + (C a ^(10:ℕ) * C g ^(3:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) * C g + C a ^(7:ℕ) * C b ^(3:ℕ) * C g + -C a ^(6:ℕ) * C b ^(4:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) * C g + -C a ^(3:ℕ) * C b ^(7:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) * C g + -C b ^(10:ℕ) * C g ^(3:ℕ)) * X 1 ^(5:ℕ)
      + (-C a ^(10:ℕ) + -C a ^(9:ℕ) * C b + C a ^(8:ℕ) * C b ^(2:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + -C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ) + C b ^(10:ℕ)) * X 1 ^(4:ℕ)
      + ((-2 : MvPolynomial (Fin 2) K) * C a ^(10:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(5:ℕ) * C b ^(5:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C b ^(10:ℕ) * C g) * X 1 ^(3:ℕ)
      + (C a ^(10:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) + -C b ^(10:ℕ))

/-- The part of `sdualAS2 a b g` of `X 0`-degree at most `4`, as a polynomial in `X 0` over
`K[X 1, X 2]`. -/
noncomputable def sdLow (a b g : K) : Polynomial (MvPolynomial (Fin 2) K) :=
  Polynomial.C (sd4 a b g) * Polynomial.X ^(4:ℕ) + Polynomial.C (sd3 a b g) * Polynomial.X ^(3:ℕ)
    + Polynomial.C (sd2 a b g) * Polynomial.X ^(2:ℕ) + Polynomial.C (sd1 a b g) * Polynomial.X ^(1:ℕ)
    + Polynomial.C (sd0 a b g)

/-- **The `X 0`-decomposition of `sdualAS2`.**  Splitting off the variable `X 0` via
`MvPolynomial.finSuccEquiv K 2`, the ruling quintic is `X ^ 5` times its top coefficient
`sd5 a b g` plus the lower part `sdLow a b g`. -/
theorem sdualAS2_succEquiv (a b g : K) :
    MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g)
      = Polynomial.C (sd5 a b g) * Polynomial.X ^(5:ℕ) + sdLow a b g := by
  rw [sdualAS2_explicit]
  simp only [sdLow, sd5, sd4, sd3, sd2, sd1, sd0,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    MvPolynomial.finSuccEquiv_X_zero, sdFinSuccEquiv_X_1, sdFinSuccEquiv_X_2, sdFinSuccEquiv_C,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat]
  refl_ring1

/-- The lower part of `sdualAS2` has `X`-degree at most `4`. -/
theorem sdLow_natDegree_le (a b g : K) : (sdLow a b g).natDegree ≤ 4 := by
  rw [sdLow, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have h4 : ¬ (m = 4) := by omega
  have h3 : ¬ (m = 3) := by omega
  have h2 : ¬ (m = 2) := by omega
  have h1 : ¬ (m = 1) := by omega
  have h0 : ¬ (m = 0) := by omega
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C,
    if_neg h4, if_neg h3, if_neg h2, if_neg h1, if_neg h0]
  refl_ring1

/-- The top coefficient `sd5` is the constant `g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)`. -/
theorem sd5_eq (a b g : K) :
    sd5 a b g = MvPolynomial.C (g * (a ^(10:ℕ) - a ^(5:ℕ) * b ^(5:ℕ) - b ^(10:ℕ))) := by
  rw [sd5]
  simp only [← map_pow, ← map_mul, ← map_add, ← map_neg]
  congr 1
  refl_ring1

/-- A polynomial `C c * X ^ 5 + q` with `q` of degree at most `4` and `c ≠ 0` has degree `5` and
leading coefficient `c`. -/
theorem natDegree_leadingCoeff_add_low {R : Type*} [Semiring R] (c : R) (q : Polynomial R)
    (hc : c ≠ 0) (hq : q.natDegree ≤ 4) :
    (Polynomial.C c * Polynomial.X ^(5:ℕ) + q).natDegree = 5 ∧
    (Polynomial.C c * Polynomial.X ^(5:ℕ) + q).leadingCoeff = c := by
  have hq5 : q.natDegree < 5 := by omega
  have hA : (Polynomial.C c * Polynomial.X ^(5:ℕ)).natDegree = 5 := by
    refine le_antisymm (Polynomial.natDegree_C_mul_X_pow_le c 5) ?_
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.coeff_C_mul_X_pow]
    simpa using hc
  have h5 : (Polynomial.C c * Polynomial.X ^(5:ℕ) + q).natDegree = 5 := by
    refine le_antisymm ?_ ?_
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact le_of_eq hA
      · omega
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_eq_zero_of_natDegree_lt hq5]
      simpa using hc
  refine ⟨h5, ?_⟩
  rw [← Polynomial.coeff_natDegree, h5, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_eq_zero_of_natDegree_lt hq5]
  simp

end

theorem sdualAS2_finSuccEquiv_deg_lc {K : Type*} [Field K] (a b g : K)
    (h : g * (a ^(10:ℕ) - a ^(5:ℕ) * b ^(5:ℕ) - b ^(10:ℕ)) ≠ 0) :
    (MvPolynomial.finSuccEquiv K 2 (Work.MotAS.sdualAS2 a b g)).natDegree = 5 ∧
    (MvPolynomial.finSuccEquiv K 2 (Work.MotAS.sdualAS2 a b g)).leadingCoeff
      = MvPolynomial.C (g * (a ^(10:ℕ) - a ^(5:ℕ) * b ^(5:ℕ) - b ^(10:ℕ))) := by
  have hc : (MvPolynomial.C (g * (a ^(10:ℕ) - a ^(5:ℕ) * b ^(5:ℕ) - b ^(10:ℕ))) :
      MvPolynomial (Fin 2) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr h
  have hkey := sdualAS2_succEquiv (K := K) a b g
  rw [sd5_eq (K := K) a b g] at hkey
  rw [hkey]
  exact natDegree_leadingCoeff_add_low _ _ hc (sdLow_natDegree_le a b g)

end Work.MotAS
