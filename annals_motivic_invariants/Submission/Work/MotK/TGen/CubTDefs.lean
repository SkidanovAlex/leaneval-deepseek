/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.CubTPara
import Submission.Work.MotK.TGen.CubTFactor
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.cubY` / `cubQd` — the cleared parametrisation of the cubic `cubTRed = 0`

The parametrisation `thetaMap a b h : K[x₀,x₁,x₂] →ₐ[K] K(u,v)` of the cubic surface
`D = {cubTRed a b h = 0}` (see `Submission/Work/MotK/TGen/CubTPara.lean`) is given by
`x_i ↦ paraCoord (i+1) / paraCoord 4`, where `paraCoord = kleinTwP (paraPt)` and

  `paraPt a b h = ![u, -(a·b·u - a²h·v)²/(a·b³·h), 2u - (a·h/b)·v, v, 1]`.

The entries of `paraPt` share the denominator `c = a·b³·h`; this file introduces the *cleared*
parametrising point `cubY a b h` (`paraPt = c⁻¹ • cubY`) and the cleared coordinates
`cubQd a b h i = P_i (cubY)`, so that `paraCoord i = C (c⁻¹)^2 · cubQd i` (the `P_i` are quadratic).

The main identities recorded here (all polynomial identities in `K[u,v]`, proved by `ring` after
the substitution `x_i ↦ cubQd (i+1)`), with `Λ(z) = -2ab·z₀ + a²h·z₃ + ab·z₂`:

* `cubQd_zero`      : `P₀ (cubY) = 0` (the parametrising point lies on the cone `kleinTwQ = 0`);
* `cubLamY`         : `Λ (cubY) = 0` (it also lies on the polar hyperplane of `p = pRa a b h`);
* `cubLamRvec`      : `Λ (rvec) = C (a·b·h) · cubTRed` (the "junk" cubic is the pullback of `Λ`),
  which is `CubTFactor` combined with `kleinTwBilin_pRa_eq`;
* `cubQd_four_ne_zero` : `cubQd a b h 4 ≠ 0` (its `u³`-coefficient is `-a⁵b⁵h`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

noncomputable section

/-- The *cleared* parametrising point `cubY = a·b³·h • paraPt` of the cone `S'`: with
`c = a·b³·h` one has `paraPt a b h = c⁻¹ • cubY a b h`. -/
def cubY (a b h : K) : Fin 5 → MvPolynomial (Fin 2) K :=
  ![C (a * b ^ 3 * h) * X 0,
    -(C (a * b) * X 0 - C (a ^ 2 * h) * X 1) ^ 2,
    C (a * b ^ 2 * h) * (C (2 * b) * X 0 - C (a * h) * X 1),
    C (a * b ^ 3 * h) * X 1,
    C (a * b ^ 3 * h)]

/-- The cleared coordinates `cubQd i = P_i (cubY)`; `paraCoord i = C (a·b³·h)⁻¹^2 · cubQd i`. -/
def cubQd (a b h : K) (i : Fin 5) : MvPolynomial (Fin 2) K :=
  aeval (cubY a b h) (kleinTwP (C a) (C b) (C h) (fun t => X t) i)

/-- The index map `Fin 3 → Fin 5`, `i ↦ i + 1`, identifying the affine coordinates `x₀,x₁,x₂`
with the coordinates `P₁/P₄, P₂/P₄, P₃/P₄` of the parametrisation. -/
def cubIx : Fin 3 → Fin 5 := ![1, 2, 3]

@[simp] theorem cubIx_zero : cubIx 0 = 1 := rfl
@[simp] theorem cubIx_one : cubIx 1 = 2 := rfl
@[simp] theorem cubIx_two : cubIx 2 = 3 := rfl

/-- **The parametrising point lies on the cone**: `kleinTwQ (cubY) = 0`. -/
theorem cubQd_zero (a b h : K) : cubQd a b h 0 = 0 := by
  simp only [cubQd, kleinTwP_zero, Fin.isValue]
  simp only [kleinTwP0, map_add, map_sub, map_mul, map_pow, map_neg, aeval_C, aeval_X]
  simp only [cubY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
    Fin.isValue, MvPolynomial.algebraMap_eq]
  simp only [map_mul, map_pow, map_ofNat]
  first | refl_ring1 | ring

/-- **The parametrising point lies on the polar hyperplane of `p = pRa a b h`**:
`Λ (cubY) = -2ab·cubY₀ + a²h·cubY₃ + ab·cubY₂ = 0`. -/
theorem cubLamY (a b h : K) :
    -(2 * C a * C b) * cubY a b h 0 + (C a ^ 2 * C h) * cubY a b h 3
      + (C a * C b) * cubY a b h 2 = 0 := by
  simp only [cubY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
    Fin.isValue]
  simp only [MvPolynomial.C_mul, MvPolynomial.C_pow, map_ofNat]
  first | refl_ring1 | ring

/-- **`Λ` is the pullback of the junk cubic**: with `Λ(z) = -2ab·z₀ + a²h·z₃ + ab·z₂` and
`rvec = kleinTwR (chart3)`, one has `Λ (rvec) = C (a·b·h) · cubTRed a b h`.

This is `Work.MotK.TGen.cubT = kleinTwBilin (pRa) (kleinTwR (chart3))` (`kleinTwBilin_pRa_eq`)
combined with the exact factorisation `cubT = C (a·b·h) · cubTRed` of
`Submission/Work/MotK/TGen/CubTFactor.lean`. -/
theorem cubLamRvec (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    -(2 * C a * C b) * rvec a b h 0 + (C a ^ 2 * C h) * rvec a b h 3
      + (C a * C b) * rvec a b h 2 = C (a * b * h) * cubTRed a b h := by
  have h1 : -(2 * C a * C b) * rvec a b h 0 + (C a ^ 2 * C h) * rvec a b h 3
      + (C a * C b) * rvec a b h 2 = cubT a b h := by
    rw [cubT, rvec]
    exact (kleinTwBilin_pRa_eq K a b h ha hh (kleinTwR (C a) (C b) (C h) (chart3 K))).symm
  rw [h1]
  exact CubTFactor K a b h ha hb hh

/-- **`s (cubY) ≠ 0`**: the secant quintic of the twisted Klein curve does not vanish at the
parametrising point.  Indeed the substitution `u = v = 0` sends `cubY` to `(0,0,0,0,a·b³·h)`, where
all terms of `s` vanish except `-a⁵b⁵h⁴·(y₄)⁵`, giving `-a¹⁰b²⁰h⁹ ≠ 0`. -/
theorem cubS_ne_zero {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    kleinTwS (C a) (C b) (C h) (cubY a b h) ≠ 0 := by
  have hval : MvPolynomial.aeval (fun _ : Fin 2 => (0 : K))
      (kleinTwS (C a) (C b) (C h) (cubY a b h)) = -(a ^ 10 * b ^ 20 * h ^ 9) := by
    simp only [kleinTwS, cubY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Fin.isValue, map_add, map_sub, map_mul, map_pow, map_neg, aeval_C, aeval_X,
      MvPolynomial.algebraMap_eq, mul_zero, add_zero, sub_zero, zero_mul, zero_add, mul_one,
      zero_pow (by norm_num : (5:ℕ) ≠ 0), map_ofNat, Algebra.algebraMap_self,
      RingHom.id_apply]
    first | refl_ring1 | ring
  intro h0
  rw [h0, map_zero] at hval
  have hne : a ^ 10 * b ^ 20 * h ^ 9 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 10 ha) (pow_ne_zero 20 hb)) (pow_ne_zero 9 hh)
  exact hne (neg_eq_zero.mp hval.symm)

end

end Work.MotK.TGen
