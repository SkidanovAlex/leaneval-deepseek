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

set_option maxHeartbeats 800000

namespace Work.MotK.TGen

open MvPolynomial Polynomial

/-- **Root-free, case `natDegree Q = 1`.**  No `Q ∈ K[x₁][X]` of `X`-degree one is a root of the inner cubic form `cubTEval a b h`.

Definitions come from `Submission.Work.MotK.TGen.CubTSetup` (module `MotK/TGen/CubTSetup`):
`cubTEval a b h Q = C (cubTA) * Q^3 + C (cubTB) * X * Q^2 + cubTG * Q + cubTD` with `cubTA = C (a^2*b^2*h)`, `cubTB = C (-2*a^3*b*h)`, `cubTG = C (cubTG0) + C (cubTG1) * X + C (cubTG2) * X^2`, `cubTD = C (cubTD0) + C (cubTD1) * X + C (cubTD2) * X^2`, where `cubTG0 = C (2*a*b^3*h) * X0^2 - C (a*b^3*h) * X0`, `cubTG1 = C (-(b^4))`, `cubTG2 = C (a^4*h)`, `cubTD0 = C (a^3*b) * X0^2 - C (2*a^3*b) * X0 + C (a^3*b)`, `cubTD1 = C (-(a^2*b^2*h)) * X0^2`, `cubTD2 = C (-(a*b^3)) * X0 + C (2*a*b^3)` (all in `MvPolynomial (Fin 1) K`, with `X0` the coefficient variable).

Route.  With `c1 = Q.coeff 1`, `c0 = Q.coeff 0` one has `Q = C c1 * X + C c0` (`Polynomial.eq_X_add_C_of_natDegree_le_one`) and `c1 ≠ 0` (else `Q.natDegree = 0`).  Assume `cubTEval a b h Q = 0`, unfold `cubTEval`, `cubTG`, `cubTD`, `cubTA`, `cubTB`, `cubTG0`, … , `cubTD2`, rewrite `Q`, and prove by `ring` the normal form
  `C A3 * X ^ 3 + C A2 * X ^ 2 + C A1 * X + C A0 = 0`
with `A3 = a^2*b^2*h * c1^3 - 2*a^3*b*h * c1^2 + a^4*h * c1` and
`A2 = 3*a^2*b^2*h * c1^2 * c0 - 4*a^3*b*h * c1 * c0 + a^4*h * c0 - b^4 * c1 - (a*b^3) * X0 + 2*(a*b^3)`.
Extract the `X^3`- and `X^2`-coefficients (`congrArg (fun p => p.coeff 3)`, `congrArg (fun p => p.coeff 2)`, then `simpa` with `Polynomial.coeff_add`, `Polynomial.coeff_C_mul_X_pow`, `Polynomial.coeff_C_mul_X`, `Polynomial.coeff_C`): `A3 = 0` and `A2 = 0` in the domain `K[x₁]`.  `A3 = a^2*h*c1*(b*c1 - a)^2 = 0` gives `b * c1 = a`, i.e. `c1 = a / b`; substituting into `A2 = 0` leaves `(a*b^3) * (1 - X0) = 0`, whose image under `MvPolynomial.constantCoeff` is `a*b^3 = 0`, contradicting `ha`, `hb`. -/
theorem CubTRootFreeEq1 (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) (Q : Polynomial (MvPolynomial (Fin 1) K)) (hQ : Q.natDegree = 1) :
    Work.MotK.TGen.cubTEval a b h Q ≠ 0 := by
  intro heq
  -- Write `Q = C c1 * X + C c0` with `c1 = Q.coeff 1 ≠ 0`.
  set c1 : MvPolynomial (Fin 1) K := Q.coeff 1 with hc1
  set c0 : MvPolynomial (Fin 1) K := Q.coeff 0 with hc0
  have hQeq : Q = Polynomial.C c1 * Polynomial.X + Polynomial.C c0 := by
    rw [hc1, hc0]
    exact Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hQ)
  have hQne : Q ≠ 0 := by intro hh0; rw [hh0] at hQ; simp at hQ
  have hc1eq : c1 = Q.leadingCoeff := by
    rw [hc1, congrArg (fun n => Polynomial.coeff Q n) hQ.symm, Polynomial.coeff_natDegree]
  have hc1ne : c1 ≠ 0 := by
    rw [hc1eq]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQne
  -- The coefficients of the normal form.
  set A3 : MvPolynomial (Fin 1) K :=
    cubTA a b h * c1 ^ 3 + cubTB a b h * c1 ^ 2 + cubTG2 a b h * c1 with hA3
  set A2 : MvPolynomial (Fin 1) K :=
    3 * (cubTA a b h * c1 ^ 2 * c0) + 2 * (cubTB a b h * c1 * c0)
      + cubTG2 a b h * c0 + cubTG1 a b h * c1 + cubTD2 a b h with hA2
  set A1 : MvPolynomial (Fin 1) K :=
    3 * (cubTA a b h * c1 * c0 ^ 2) + cubTB a b h * c0 ^ 2
      + cubTG1 a b h * c0 + cubTG0 a b h * c1 + cubTD1 a b h with hA1
  set A0 : MvPolynomial (Fin 1) K :=
    cubTA a b h * c0 ^ 3 + cubTG0 a b h * c0 + cubTD0 a b h with hA0
  -- The normal form of `cubTEval a b h Q` at a linear `Q`.
  have hnf : Work.MotK.TGen.cubTEval a b h Q
      = Polynomial.C A3 * Polynomial.X ^ 3 + Polynomial.C A2 * Polynomial.X ^ 2
        + Polynomial.C A1 * Polynomial.X + Polynomial.C A0 := by
    conv_lhs => rw [hQeq]
    simp only [hA3, hA2, hA1, hA0, Work.MotK.TGen.cubTEval, Work.MotK.TGen.cubTG,
      Work.MotK.TGen.cubTD, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
      Polynomial.C_ofNat]
    first | refl_ring1 | ring
  rw [hnf] at heq
  -- Extract the `X ^ 3`- and `X ^ 2`-coefficients.
  have h3 : A3 = 0 := by
    have h := congrArg (fun p : Polynomial (MvPolynomial (Fin 1) K) => p.coeff 3) heq
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_zero] using h
  have h2 : A2 = 0 := by
    have h := congrArg (fun p : Polynomial (MvPolynomial (Fin 1) K) => p.coeff 2) heq
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_zero] using h
  -- `A3 = C (a^2 * h) * c1 * (C b * c1 - C a)^2`.
  have hA3fac : A3
      = MvPolynomial.C (a ^ 2 * h) * c1 * (MvPolynomial.C b * c1 - MvPolynomial.C a) ^ 2 := by
    rw [hA3]
    simp only [cubTA, cubTB, cubTG2, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_neg,
      map_ofNat]
    first | refl_ring1 | ring
  have hCa2h : (MvPolynomial.C (a ^ 2 * h) : MvPolynomial (Fin 1) K) ≠ 0 := by
    intro h0
    have h1 : a ^ 2 * h = 0 := by
      apply MvPolynomial.C_injective (Fin 1) K
      simpa using h0
    exact mul_ne_zero (pow_ne_zero 2 ha) hh h1
  -- Hence `b * c1 = a`.
  have hbc1 : MvPolynomial.C b * c1 = MvPolynomial.C a := by
    have hzero : MvPolynomial.C (a ^ 2 * h) * c1
        * (MvPolynomial.C b * c1 - MvPolynomial.C a) ^ 2 = 0 := by
      rw [← hA3fac]; exact h3
    have hsq : (MvPolynomial.C b * c1 - MvPolynomial.C a) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hzero with hh1 | hh1
      · rcases mul_eq_zero.mp hh1 with h2' | h2'
        · exact absurd h2' hCa2h
        · exact absurd h2' hc1ne
      · exact hh1
    have h0 : MvPolynomial.C b * c1 - MvPolynomial.C a = 0 := by
      have h2' : (MvPolynomial.C b * c1 - MvPolynomial.C a)
          * (MvPolynomial.C b * c1 - MvPolynomial.C a) = 0 := by
        simpa [pow_two] using hsq
      rcases mul_eq_zero.mp h2' with h3' | h3' <;> exact h3'
    rwa [sub_eq_zero] at h0
  -- Substituting `a = b * c1` into `A2` leaves `C (a * b^3) * (1 - X 0)`.
  have hA2v : A2 = MvPolynomial.C (a * b ^ 3) * (1 - MvPolynomial.X 0) := by
    rw [hA2]
    simp only [cubTA, cubTB, cubTG1, cubTG2, cubTD2, MvPolynomial.C_mul, MvPolynomial.C_pow,
      MvPolynomial.C_neg, map_ofNat]
    rw [← hbc1]
    first | refl_ring1 | ring
  have hcc : MvPolynomial.constantCoeff A2 = 0 := by rw [h2, map_zero]
  have hval : MvPolynomial.constantCoeff A2 = a * b ^ 3 := by
    rw [hA2v]
    simp only [map_mul, map_sub, map_one, MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_X,
      mul_one, sub_zero]
  rw [hval] at hcc
  exact (mul_ne_zero ha (pow_ne_zero 3 hb)) hcc

end Work.MotK.TGen
