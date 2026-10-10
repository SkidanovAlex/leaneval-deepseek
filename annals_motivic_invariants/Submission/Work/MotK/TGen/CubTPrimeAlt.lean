/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.CubTRedDefs
import Submission.Work.MotK.TGen.CubTSetup
import Submission.Work.MotK.TGen.CubTCubicIrred
import Submission.Work.MotK.TGen.CubTRootFreeGe2
import Submission.Work.MotK.TGen.CubTRootFreeEq1
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.CubTPrimeAlt` — a self-contained proof that `cubTRed a b h` is prime

This module is a drop-in replacement for `Work.MotK.TGen.CubTPrime` that does **not** depend on
`Work.MotK.TGen.CubTRootFreeEq0` (which was left with a `sorry` and stalled).  It re-proves the
missing root-free case (`natDegree Q = 0`) here, under the name `cubTRootFreeEq0_aux`, and then
repeats the standard assembly of the primality argument.

The primality statement is identical to `Work.MotK.TGen.CubTPrime`, but the declaration is named
`CubTPrimeAlt` so that both can coexist in the environment.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K]

/-- **Root-free, case `natDegree Q = 0`.**  No nonzero constant `Q ∈ K[x₁]` is a root of the
inner cubic form `cubTEval a b h`.

Writing `Q = C q` and expanding `cubTEval a b h Q` as a polynomial in the indeterminate `X`, the
coefficients of `X²` and `X¹` are

* `A2 = cubTG2 a b h * q + cubTD2 a b h`, i.e. `a⁴h·q + (2ab³ - ab³·X0)`,
* `A1 = cubTB a b h * q² + cubTG1 a b h * q + cubTD1 a b h`, i.e. `-2a³bh·q² - b⁴·q - a²b²h·X0²`.

`A2 = 0` gives `a⁴h·q = ab³·(X0 - 2)`; multiplying `A1 = 0` by `(a⁴h)²` and substituting that
relation produces `C (-(a⁵b²h)) · ((2b⁵ + a⁵h²)·X0² - 7b⁵·X0 + 6b⁵) = 0`, hence
`(2b⁵ + a⁵h²)·X0² - 7b⁵·X0 + 6b⁵ = 0` in `K[X0]`.  Reading off the `X0`- and `X0⁰`-coefficients
gives `7b⁵ = 0` and `6b⁵ = 0`, whence `7 = 6 = 0` in `K` (as `b ≠ 0`), i.e. `1 = 0` — absurd. -/
theorem cubTRootFreeEq0_aux (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) (Q : Polynomial (MvPolynomial (Fin 1) K)) (hQ : Q.natDegree = 0)
    (hQ0 : Q ≠ 0) : Work.MotK.TGen.cubTEval a b h Q ≠ 0 := by
  intro heq
  set q : MvPolynomial (Fin 1) K := Q.coeff 0 with hq
  have hQeq : Q = Polynomial.C q := by rw [hq]; exact Polynomial.eq_C_of_natDegree_eq_zero hQ
  set A2 : MvPolynomial (Fin 1) K :=
    Work.MotK.TGen.cubTG2 a b h * q + Work.MotK.TGen.cubTD2 a b h with hA2
  set A1 : MvPolynomial (Fin 1) K :=
    Work.MotK.TGen.cubTB a b h * q^2 + Work.MotK.TGen.cubTG1 a b h * q
      + Work.MotK.TGen.cubTD1 a b h with hA1
  set A0 : MvPolynomial (Fin 1) K :=
    Work.MotK.TGen.cubTA a b h * q^3 + Work.MotK.TGen.cubTG0 a b h * q
      + Work.MotK.TGen.cubTD0 a b h with hA0
  have hnf : Work.MotK.TGen.cubTEval a b h Q
      = Polynomial.C A2 * Polynomial.X^2 + Polynomial.C A1 * Polynomial.X + Polynomial.C A0 := by
    conv_lhs => rw [hQeq]
    simp only [hA2, hA1, hA0, Work.MotK.TGen.cubTEval, Work.MotK.TGen.cubTG,
      Work.MotK.TGen.cubTD, Work.MotK.TGen.cubTA, Work.MotK.TGen.cubTB,
      Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]
    first | refl_ring1 | ring
  rw [hnf] at heq
  have h2 : A2 = 0 := by
    have hh2 := congrArg (fun p : Polynomial (MvPolynomial (Fin 1) K) => p.coeff 2) heq
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_zero] using hh2
  have h1 : A1 = 0 := by
    have hh1 := congrArg (fun p : Polynomial (MvPolynomial (Fin 1) K) => p.coeff 1) heq
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_zero] using hh1
  have hA2v : A2 = MvPolynomial.C (a^4*h) * q + MvPolynomial.C (-(a*b^3)) * MvPolynomial.X 0
      + MvPolynomial.C (2*(a*b^3)) := by
    rw [hA2]; simp only [Work.MotK.TGen.cubTG2, Work.MotK.TGen.cubTD2]; ring_nf
  have h2a : MvPolynomial.C (a^4*h) * q + MvPolynomial.C (-(a*b^3)) * MvPolynomial.X 0
      + MvPolynomial.C (2*(a*b^3)) = 0 := by
    rw [← hA2v, h2]
  have h2' : MvPolynomial.C (a^4*h) * q
      + (MvPolynomial.C (-(a*b^3)) * MvPolynomial.X 0 + MvPolynomial.C (2*(a*b^3))) = 0 := by
    rw [add_assoc] at h2a; exact h2a
  have hrw : MvPolynomial.C (a^4*h) * q
      = MvPolynomial.C (a*b^3) * (MvPolynomial.X 0 - MvPolynomial.C 2) := by
    have h' : MvPolynomial.C (a^4*h) * q
        = -(MvPolynomial.C (-(a*b^3)) * MvPolynomial.X 0 + MvPolynomial.C (2*(a*b^3))) :=
      eq_neg_of_add_eq_zero_left h2'
    rw [h']
    simp only [map_ofNat, map_mul, map_add, map_pow, map_neg, map_sub]
    first | refl_ring1 | ring
  set P : MvPolynomial (Fin 1) K := MvPolynomial.C (2*b^5 + a^5*h^2) * MvPolynomial.X 0^2
      - MvPolynomial.C (7*b^5) * MvPolynomial.X 0 + MvPolynomial.C (6*b^5) with hP
  have hmul : (MvPolynomial.C (a^4*h))^2 * A1 = MvPolynomial.C (-(a^5*b^2*h)) * P := by
    have e1 : (MvPolynomial.C (a^4*h))^2 * A1
        = MvPolynomial.C (-2*a^3*b*h) * (MvPolynomial.C (a^4*h) * q)^2
          + MvPolynomial.C (-(b^4)) * (MvPolynomial.C (a^4*h) * (MvPolynomial.C (a^4*h) * q))
          + MvPolynomial.C (-(a^2*b^2*h)) * (MvPolynomial.C (a^4*h))^2 * MvPolynomial.X 0^2 := by
      rw [hA1]; simp only [Work.MotK.TGen.cubTB, Work.MotK.TGen.cubTG1, Work.MotK.TGen.cubTD1]
      first | refl_ring1 | ring
    rw [e1, hrw, hP]
    simp only [map_ofNat, map_mul, map_add, map_pow, map_neg, map_sub]
    first | refl_ring1 | ring
  have hCP : MvPolynomial.C (-(a^5*b^2*h)) * P = 0 := by rw [← hmul, h1, mul_zero]
  have hCne : (MvPolynomial.C (-(a^5*b^2*h)) : MvPolynomial (Fin 1) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (by
      intro h0
      exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 5 ha) (pow_ne_zero 2 hb)) hh)
        (neg_eq_zero.mp h0))
  have hP0 : P = 0 := by
    rcases mul_eq_zero.mp hCP with hh1 | hh1
    · exact absurd hh1 hCne
    · exact hh1
  have hcoeff1 : P.coeff (Finsupp.single (0:Fin 1) 1) = -(7*b^5) := by
    rw [hP]
    have hA : (MvPolynomial.C (2*b^5+a^5*h^2) * (MvPolynomial.X (0:Fin 1))^2
        : MvPolynomial (Fin 1) K).coeff (Finsupp.single 0 1) = 0 := by
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]; simp
    have hB : (MvPolynomial.C (7*b^5) * MvPolynomial.X (0:Fin 1)
        : MvPolynomial (Fin 1) K).coeff (Finsupp.single 0 1) = 7*b^5 := by
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]; simp
    have hC : (MvPolynomial.C (6*b^5) : MvPolynomial (Fin 1) K).coeff (Finsupp.single 0 1) = 0 := by
      rw [MvPolynomial.coeff_C]
      split_ifs with hh'
      · exact absurd (Finsupp.single_eq_zero.mp hh'.symm) Nat.one_ne_zero
      · rfl
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_sub, hA, hB, hC]
    first | refl_ring1 | ring
  have hcoeff0 : P.coeff (0 : Fin 1 →₀ ℕ) = 6*b^5 := by
    rw [hP]
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X, MvPolynomial.coeff_C]
    simp
  have h7 : (7:K) * b^5 = 0 := by
    have hh' := hcoeff1
    rw [hP0] at hh'
    simp only [MvPolynomial.coeff_zero] at hh'
    exact neg_eq_zero.mp hh'.symm
  have h6 : (6:K) * b^5 = 0 := by
    have hh' := hcoeff0
    rw [hP0] at hh'
    simp only [MvPolynomial.coeff_zero] at hh'
    exact hh'.symm
  have hb5 : b^5 ≠ 0 := pow_ne_zero 5 hb
  have h7z : (7:K) = 0 := (mul_eq_zero.mp h7).resolve_right hb5
  have h6z : (6:K) = 0 := (mul_eq_zero.mp h6).resolve_right hb5
  have h76 : (7:K) - (6:K) = 1 := by norm_num
  rw [h7z, h6z, sub_zero] at h76
  exact one_ne_zero h76.symm

/-- `cubTAl a b h = a²b²h ≠ 0`. -/
theorem cubTAl_ne_zero_alt (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    cubTAl a b h ≠ 0 := by
  intro h0
  have h1 : MvPolynomial.constantCoeff (cubTAl a b h) = a ^ 2 * b ^ 2 * h := by
    simp only [cubTAl, MvPolynomial.constantCoeff_C]
  rw [h0] at h1
  simp only [map_zero] at h1
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)) hh) h1.symm

/-- `cubTAl a b h` is a unit of `K[x₁,x₂]` (it is a nonzero constant). -/
theorem cubTAl_isUnit_alt (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    IsUnit (cubTAl a b h) := by
  rw [cubTAl]
  exact IsUnit.map MvPolynomial.C
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)) hh))

/-- The `X³`-coefficient of the normal form of `cubTRed` is its leading coefficient `α`. -/
theorem cubTPhi_coeff_three_alt (a b h : K) :
    (cubTPhi K (cubTRed a b h)).coeff 3 = cubTAl a b h := by
  rw [cubTPhi_cubTRed]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C]
  norm_num

/-- The normal form of `cubTRed` has `X`-degree `3`. -/
theorem cubTPhi_natDegree_alt (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    (cubTPhi K (cubTRed a b h)).natDegree = 3 := by
  rw [cubTPhi_cubTRed]
  compute_degree
  · exact cubTAl_ne_zero_alt a b h ha hb hh
  · norm_num
  · norm_num

/-- **`cubTRed a b h` is a prime element of `K[x₀,x₁,x₂]`.** -/
theorem CubTPrimeAlt (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Prime (Work.MotK.TGen.cubTRed a b h) := by
  have hno : ∀ p : MvPolynomial (Fin 2) K,
      Polynomial.eval p (cubTPhi K (cubTRed a b h)) ≠ 0 := by
    intro p hp
    have h1 : cubTEval a b h (cubTPsi K p) = 0 := by
      rw [← cubTPsi_eval_cubTPhi a b h p, hp, map_zero]
    rcases eq_or_ne p 0 with rfl | hp0
    · exact cubTEval_zero a b h ha hb h1
    · have hQne : cubTPsi K p ≠ 0 := fun h => hp0 ((cubTPsi K).injective (by rw [h, map_zero]))
      rcases Nat.lt_or_ge (cubTPsi K p).natDegree 2 with hlt | hge
      · have hcase : (cubTPsi K p).natDegree = 0 ∨ (cubTPsi K p).natDegree = 1 := by omega
        rcases hcase with h0 | h1'
        · exact cubTRootFreeEq0_aux K a b h ha hb hh (cubTPsi K p) h0 hQne h1
        · exact CubTRootFreeEq1 K a b h ha hb hh (cubTPsi K p) h1' h1
      · exact CubTRootFreeGe2 K a b h ha hb hh (cubTPsi K p) hge h1
  have hirr : Irreducible (cubTPhi K (cubTRed a b h)) :=
    CubTCubicIrred (cubTPhi_natDegree_alt a b h ha hb hh)
      (by rw [cubTPhi_coeff_three_alt]; exact cubTAl_isUnit_alt a b h ha hb hh) hno
  have hirr' : Irreducible (cubTRed a b h) := (MulEquiv.irreducible_iff (cubTPhi K)).mp hirr
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr'

end

end Work.MotK.TGen
