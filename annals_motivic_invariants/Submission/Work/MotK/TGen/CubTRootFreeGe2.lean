import Mathlib
import Submission.Work.MotK.TGen.CubTSetup
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

/-- `cubTG a b h` has `X`-degree at most `2` (it is
`C (cubTG0) + C (cubTG1) * X + C (cubTG2) * X ^ 2`). -/
theorem natDegree_cubTG_le {K : Type*} [Field K] (a b h : K) :
    (cubTG a b h).natDegree ≤ 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  simp only [cubTG, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  simp only [show N ≠ 0 by omega, show 1 ≠ N by omega, show N ≠ 2 by omega, ite_false,
    mul_zero, add_zero]

/-- `cubTD a b h` has `X`-degree at most `2` (it is
`C (cubTD0) + C (cubTD1) * X + C (cubTD2) * X ^ 2`). -/
theorem natDegree_cubTD_le {K : Type*} [Field K] (a b h : K) :
    (cubTD a b h).natDegree ≤ 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  simp only [cubTD, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  simp only [show N ≠ 0 by omega, show 1 ≠ N by omega, show N ≠ 2 by omega, ite_false,
    mul_zero, add_zero]

/-- `cubTA a b h = C (a ^ 2 * b ^ 2 * h)` is nonzero when `a`, `b`, `h` are. -/
theorem cubTA_ne_zero {K : Type*} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) : cubTA a b h ≠ 0 := by
  intro h
  rw [cubTA, MvPolynomial.C_eq_zero] at h
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)) hh h

/-- **Root-free, case `natDegree Q ≥ 2`.**  No `Q ∈ K[x₁][X]` of `X`-degree at least two is a root of the inner cubic form `cubTEval a b h`.

`cubTEval a b h Q = C (cubTA a b h) * Q ^ 3 + C (cubTB a b h) * X * Q ^ 2 + cubTG a b h * Q + cubTD a b h`, where (importing `Submission.Work.MotK.TGen.CubTSetup`, module `MotK/TGen/CubTSetup`)
`cubTA = C (a^2*b^2*h)`, `cubTB = C (-2*a^3*b*h)`, `cubTG = C (cubTG0) + C (cubTG1) * X + C (cubTG2) * X^2`, `cubTD = C (cubTD0) + C (cubTD1) * X + C (cubTD2) * X^2` with
`cubTG0 = C (2*a*b^3*h) * X0^2 - C (a*b^3*h) * X0`, `cubTG1 = C (-(b^4))`, `cubTG2 = C (a^4*h)`, `cubTD0 = C (a^3*b) * X0^2 - C (2*a^3*b) * X0 + C (a^3*b)`, `cubTD1 = C (-(a^2*b^2*h)) * X0^2`, `cubTD2 = C (-(a*b^3)) * X0 + C (2*a*b^3)`
(all in `MvPolynomial (Fin 1) K`, the variable `X0` being the coefficient variable, `X` the indeterminate of `Polynomial (MvPolynomial (Fin 1) K)`).

Route.  Put `d = Q.natDegree`, `c = Q.coeff d = Q.leadingCoeff ≠ 0` (`Polynomial.leadingCoeff_eq_zero`; `Q ≠ 0` follows from `hQ`).  Extract the coefficient of `X ^ (3 * d)` of the identity `cubTEval a b h Q = 0` with `congrArg (fun p => p.coeff (3 * d))` and `simpa`.  The only non-vanishing contribution comes from `C (cubTA a b h) * Q ^ 3`, because `coeff (Q ^ 3) (3 * d) = c ^ 3` (via `Polynomial.natDegree_pow'`, `Polynomial.leadingCoeff_pow'`, `Polynomial.coeff_natDegree`) while `natDegree (C (cubTB) * X * Q ^ 2) ≤ 1 + 2 * d`, `natDegree (cubTG * Q) ≤ 2 + d`, `natDegree (cubTD) ≤ 2`, all `< 3 * d` for `d ≥ 2` (use `Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.natDegree_mul_le`, `Polynomial.natDegree_add_le`, `Polynomial.natDegree_C_mul_X_pow_le`, and the explicit shape of `cubTG`, `cubTD`).  Hence `cubTA a b h * c ^ 3 = 0` in the domain `K[x₁]`; but `cubTA a b h = C (a^2*b^2*h) ≠ 0` and `c ≠ 0`. -/
theorem CubTRootFreeGe2 (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) (Q : Polynomial (MvPolynomial (Fin 1) K)) (hQ : 2 ≤ Q.natDegree) :
    Work.MotK.TGen.cubTEval a b h Q ≠ 0 := by
  intro hroot
  have hQne : Q ≠ 0 := by
    intro h; rw [h] at hQ; simp at hQ
  have hcne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQne
  have hcubTA : cubTA a b h ≠ 0 := cubTA_ne_zero a b h ha hb hh
  -- the `X ^ (3 * Q.natDegree)`-coefficient of the `Q ^ 3` term
  have h1 : (Polynomial.C (cubTA a b h) * Q ^ 3).coeff (3 * Q.natDegree)
      = cubTA a b h * Q.leadingCoeff ^ 3 := by
    rw [Polynomial.coeff_C_mul, ← Polynomial.natDegree_pow, Polynomial.coeff_natDegree,
      Polynomial.leadingCoeff_pow]
  -- all other terms vanish at that index, being of lower `natDegree`
  have h2 : (Polynomial.C (cubTB a b h) * Polynomial.X * Q ^ 2).coeff (3 * Q.natDegree) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hb1 : (Polynomial.C (cubTB a b h) * Polynomial.X).natDegree ≤ 1 := by
      simpa using Polynomial.natDegree_C_mul_X_pow_le (cubTB a b h) 1
    calc (Polynomial.C (cubTB a b h) * Polynomial.X * Q ^ 2).natDegree
        ≤ (Polynomial.C (cubTB a b h) * Polynomial.X).natDegree + (Q ^ 2).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 1 + 2 * Q.natDegree := by
          rw [Polynomial.natDegree_pow]
          exact add_le_add hb1 le_rfl
      _ < 3 * Q.natDegree := by omega
  have h3 : (cubTG a b h * Q).coeff (3 * Q.natDegree) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hg : (cubTG a b h).natDegree ≤ 2 := natDegree_cubTG_le a b h
    calc (cubTG a b h * Q).natDegree ≤ (cubTG a b h).natDegree + Q.natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 2 + Q.natDegree := by omega
      _ < 3 * Q.natDegree := by omega
  have h4 : (cubTD a b h).coeff (3 * Q.natDegree) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hd : (cubTD a b h).natDegree ≤ 2 := natDegree_cubTD_le a b h
    omega
  have hkey : (cubTEval a b h Q).coeff (3 * Q.natDegree) = cubTA a b h * Q.leadingCoeff ^ 3 := by
    simp only [cubTEval, Polynomial.coeff_add]
    rw [h1, h2, h3, h4]
    first | refl_ring1 | ring
  rw [hroot] at hkey
  simp only [Polynomial.coeff_zero] at hkey
  exact (mul_ne_zero hcubTA (pow_ne_zero 3 hcne)) hkey.symm

end Work.MotK.TGen
