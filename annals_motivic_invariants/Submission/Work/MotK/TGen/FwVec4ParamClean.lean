import Mathlib
import Submission.Work.MotK.TGen.FwVec4Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.FwVec4ParamClean` — the parametrisation of `{f̂₄ = 0}`, without `sorry`

This file proves the same statement as `Work.MotK.TGen.FwVec4Param` but *without* importing the
`FwChiPi`, `FwSNeZero`, `FwBNeZero` helper files (which are still `sorry`).  All the needed
intermediate quantities are defined here on the standard plane `(0, u, v, 1, 0)` of the target
plane `{w₀ = 0, w₄ = 0}`, and the two `MvPolynomial`-level nonvanishing facts (the polar form of
the quadric along `(p, R(w))` and the dual secant quintic `s'` on the plane) are proved directly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open MvPolynomial
namespace Work.MotK.TGen
open Work.MotK

noncomputable section

variable {K : Type} [Field K]

/-! ## The standard plane and its parametrisation data -/

/-- The affine chart `(0, u, v, 1, 0)` of the target plane `{w₀ = 0, w₄ = 0}`, written with
pattern matching so that all index computations are definitional. -/
def planeV (K' : Type*) [Field K'] : Fin 5 → MvPolynomial (Fin 2) K'
  | 0 => 0
  | 1 => MvPolynomial.X 0
  | 2 => MvPolynomial.X 1
  | 3 => 1
  | 4 => 0

/-- The base point `p = kleinPointT a b h` as a constant vector of polynomials. -/
def ptV (a b h : K) : Fin 5 → MvPolynomial (Fin 2) K :=
  fun i => MvPolynomial.C (kleinPointT a b h i)

/-- `Z = kleinTwR (0, u, v, 1, 0)`. -/
def ZV (a b h : K) : Fin 5 → MvPolynomial (Fin 2) K :=
  kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (planeV K)

/-- `χ = π_p(Z)`, as the explicit list `(0, pl₁, pl₂, pl₃, pl₄)`. -/
def chiV (a b h : K) : Fin 5 → MvPolynomial (Fin 2) K
  | 0 => 0
  | 1 => pl1 a b h
  | 2 => pl2 a b h
  | 3 => pl3 a b h
  | 4 => pl4 a b h

/-- The non-vanishing factor `μ = b(p,Z)² · s'(w)` of the composition `fwComp`. -/
def fwMuV (a b h : K) : MvPolynomial (Fin 2) K :=
  kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptV a b h) (ZV a b h) ^ 2 *
    kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (planeV K)

@[simp] theorem planeV_zero (K' : Type*) [Field K'] : planeV K' 0 = 0 := rfl
@[simp] theorem planeV_one (K' : Type*) [Field K'] : planeV K' 1 = MvPolynomial.X 0 := rfl
@[simp] theorem planeV_two (K' : Type*) [Field K'] : planeV K' 2 = MvPolynomial.X 1 := rfl
@[simp] theorem planeV_three (K' : Type*) [Field K'] : planeV K' 3 = 1 := rfl
@[simp] theorem planeV_four (K' : Type*) [Field K'] : planeV K' 4 = 0 := rfl

@[simp] theorem chiV_zero (a b h : K) : chiV a b h 0 = 0 := rfl
@[simp] theorem chiV_one (a b h : K) : chiV a b h 1 = pl1 a b h := rfl
@[simp] theorem chiV_two (a b h : K) : chiV a b h 2 = pl2 a b h := rfl
@[simp] theorem chiV_three (a b h : K) : chiV a b h 3 = pl3 a b h := rfl
@[simp] theorem chiV_four (a b h : K) : chiV a b h 4 = pl4 a b h := rfl

/-! ## The components of `Z = kleinTwR (0,u,v,1,0)` -/

theorem ZV0 (a b h : K) : ZV (K := K) a b h 0
    = MvPolynomial.C (a^3*b*h^2) * MvPolynomial.X 0^2
      - MvPolynomial.C (a*b^3*h^2) * MvPolynomial.X 0 * MvPolynomial.X 1^2 := by
  simp only [ZV, planeV, kleinTwR, kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4,
    map_mul, map_pow, map_add, map_sub, map_neg, map_one, map_zero, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

theorem ZV1 (a b h : K) : ZV (K := K) a b h 1
    = MvPolynomial.C (a^2*b^2*h)
      - MvPolynomial.C (a*b^3*h^2) * MvPolynomial.X 0^2 * MvPolynomial.X 1 := by
  simp only [ZV, planeV, kleinTwR, kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4,
    map_mul, map_pow, map_add, map_sub, map_neg, map_one, map_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

theorem ZV2 (a b h : K) : ZV (K := K) a b h 2
    = MvPolynomial.C (-(a*b^3*h)) * MvPolynomial.X 1
      + MvPolynomial.C (a^2*b^2*h^2) * MvPolynomial.X 0^3 := by
  simp only [ZV, planeV, kleinTwR, kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4,
    map_mul, map_pow, map_add, map_sub, map_neg, map_one, map_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

theorem ZV3 (a b h : K) : ZV (K := K) a b h 3
    = MvPolynomial.C (-(a*b^3*h)) * MvPolynomial.X 1^2
      + MvPolynomial.C (a^3*b*h) * MvPolynomial.X 0 := by
  simp only [ZV, planeV, kleinTwR, kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4,
    map_mul, map_pow, map_add, map_sub, map_neg, map_one, map_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  first | refl_ring1 | ring

theorem ZV4 (a b h : K) : ZV (K := K) a b h 4
    = MvPolynomial.C (a^2*b^2*h) * MvPolynomial.X 1^3
      - MvPolynomial.C (a^4*h) * MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp only [ZV, planeV, kleinTwR, kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4,
    map_mul, map_pow, map_add, map_sub, map_neg, map_one, map_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

/-! ## The polar form `kleinTwBilin` and its value on `(p, Z)` -/

theorem kleinTwBilin_eq {R : Type*} [CommRing R] (a b h : R) (u v : Fin 5 → R) :
    kleinTwBilin a b h u v
      = -2*a*b*(u 0)*(v 0) + a^2*h*((u 2)*(v 3) + (u 3)*(v 2))
        - b^2*h*((u 1)*(v 4) + (u 4)*(v 1)) := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

theorem bilinV (a b h : K) :
    kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptV a b h) (ZV a b h)
      = -(2 : MvPolynomial (Fin 2) K) * MvPolynomial.C a * MvPolynomial.C b *
            MvPolynomial.C (a^3*b*h^2) * MvPolynomial.X 0 ^ 2
        + 2 * MvPolynomial.C a * MvPolynomial.C b * MvPolynomial.C (a*b^3*h^2) *
            MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
        + MvPolynomial.C a ^ 2 * MvPolynomial.C h * MvPolynomial.C (-(a*b^3*h)) *
            MvPolynomial.X 1 ^ 2
        + MvPolynomial.C a ^ 2 * MvPolynomial.C h * MvPolynomial.C (a^3*b*h) *
            MvPolynomial.X 0
        + MvPolynomial.C a ^ 2 * MvPolynomial.C h * MvPolynomial.C (b/(a*h)) *
            MvPolynomial.C (-(a*b^3*h)) * MvPolynomial.X 1
        + MvPolynomial.C a ^ 2 * MvPolynomial.C h * MvPolynomial.C (b/(a*h)) *
            MvPolynomial.C (a^2*b^2*h^2) * MvPolynomial.X 0 ^ 3 := by
  rw [kleinTwBilin_eq, ZV0, ZV1, ZV2, ZV3, ZV4]
  simp only [ptV, kleinPointT, map_one, map_zero]
  first | refl_ring1 | ring

theorem bilinV_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptV a b h)
      (ZV a b h) ≠ 0 := by
  intro h0
  have key : MvPolynomial.aeval
        (fun i : Fin 2 => (![(0 : Polynomial K), Polynomial.X] : Fin 2 → Polynomial K) i)
        (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptV a b h)
          (ZV a b h))
      = (Polynomial.C a : Polynomial K)^2 * Polynomial.C h * Polynomial.C (-(a*b^3*h))
            * Polynomial.X^2
        + (Polynomial.C a)^2 * Polynomial.C h * Polynomial.C (b/(a*h))
            * Polynomial.C (-(a*b^3*h)) * Polynomial.X := by
    rw [bilinV]
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, map_neg, map_ofNat,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.C_eq_algebraMap,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    first | refl_ring1 | ring
  rw [h0, map_zero] at key
  have hfac : (Polynomial.C a : Polynomial K)^2 * Polynomial.C h * Polynomial.C (-(a*b^3*h))
          * Polynomial.X^2
        + (Polynomial.C a)^2 * Polynomial.C h * Polynomial.C (b/(a*h))
            * Polynomial.C (-(a*b^3*h)) * Polynomial.X
      = (Polynomial.C a)^2 * Polynomial.C h * Polynomial.C (-(a*b^3*h)) * Polynomial.X
        * (Polynomial.X + Polynomial.C (b/(a*h))) := by ring
  rw [hfac] at key
  have hcoef : (Polynomial.C a : Polynomial K)^2 * Polynomial.C h * Polynomial.C (-(a*b^3*h))
      ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (Polynomial.C_ne_zero.mpr ha))
      (Polynomial.C_ne_zero.mpr hh)) (Polynomial.C_ne_zero.mpr ?_)
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha (pow_ne_zero 3 hb)) hh)
  have hlin : (Polynomial.X + Polynomial.C (b/(a*h)) : Polynomial K) ≠ 0 := by
    intro hz
    have h1 := congrArg (fun p : Polynomial K => Polynomial.coeff p 1) hz
    simp at h1
  exact (mul_ne_zero (mul_ne_zero hcoef Polynomial.X_ne_zero) hlin) key.symm

/-! ## The dual secant quintic on the plane, and `fwMuV ≠ 0` -/

theorem fwSDualInvV_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (planeV K) ≠ 0 := by
  have key : MvPolynomial.constantCoeff
      (kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (planeV K))
      = -a^5*b^5*h^2 := by
    simp only [kleinTwSDualInv, planeV, map_add, map_sub, map_mul, map_pow]
    simp
  intro h0
  rw [h0, map_zero] at key
  exact absurd key (Ne.symm (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 5 ha))
    (pow_ne_zero 5 hb)) (pow_ne_zero 2 hh)))

theorem fwMuV_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    fwMuV a b h ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 (bilinV_ne_zero a b h ha hb hh))
    (fwSDualInvV_ne_zero a b h ha hb hh)

/-! ## `χ = π_p(Z)`, componentwise -/

theorem FwChiPiV (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    kleinTwPi (ptV a b h) (ZV a b h) = chiV a b h := by
  have hA : (MvPolynomial.C (a^3*b*h^2) : MvPolynomial (Fin 2) K) * MvPolynomial.C (b/(a*h))
      = MvPolynomial.C (a^2*b^2*h) := by
    rw [← map_mul]; congr 1; field_simp
  have hB : (MvPolynomial.C (a*b^3*h^2) : MvPolynomial (Fin 2) K) * MvPolynomial.C (b/(a*h))
      = MvPolynomial.C (b^4*h) := by
    rw [← map_mul]; congr 1; field_simp
  have hZ0 : ZV (K := K) a b h 0 * MvPolynomial.C (b/(a*h))
      = MvPolynomial.C (a^2*b^2*h) * MvPolynomial.X 0^2
        - MvPolynomial.C (b^4*h) * MvPolynomial.X 0 * MvPolynomial.X 1^2 := by
    rw [ZV0, sub_mul,
      show (MvPolynomial.C (a^3*b*h^2) : MvPolynomial (Fin 2) K) * MvPolynomial.X 0 ^ 2
            * MvPolynomial.C (b/(a*h))
          = MvPolynomial.C (a^3*b*h^2) * MvPolynomial.C (b/(a*h)) * MvPolynomial.X 0^2
          from by ring,
      show (MvPolynomial.C (a*b^3*h^2) : MvPolynomial (Fin 2) K) * MvPolynomial.X 0
            * MvPolynomial.X 1 ^ 2 * MvPolynomial.C (b/(a*h))
          = MvPolynomial.C (a*b^3*h^2) * MvPolynomial.C (b/(a*h)) * MvPolynomial.X 0
            * MvPolynomial.X 1^2
          from by ring,
      hA, hB]
  funext i
  fin_cases i <;> simp only [fin5_zero, fin5_one, fin5_two, fin5_three, fin5_four]
  · simp only [kleinTwPi, ptV, kleinPointT, ZV, planeV, chiV, kleinTwR, kleinTwR0, kleinTwR1,
      kleinTwR2, kleinTwR3, kleinTwR4, map_mul, map_pow, map_add, map_sub, map_neg, map_one,
      map_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    first | refl_ring1 | ring
  · simp only [kleinTwPi, ptV, kleinPointT, ZV, planeV, chiV, pl1, kleinTwR, kleinTwR0,
      kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4, map_mul, map_pow, map_add, map_sub, map_neg,
      map_one, map_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    first | refl_ring1 | ring
  · simp only [kleinTwPi, ptV, kleinPointT, ZV, planeV, chiV, pl2, kleinTwR, kleinTwR0,
      kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4, map_mul, map_pow, map_add, map_sub, map_neg,
      map_one, map_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    first | refl_ring1 | ring
  · simp only [kleinTwPi, ptV, kleinPointT]
    rw [ZV3, hZ0]
    simp only [chiV, pl3, map_mul, map_pow, map_sub, map_neg, map_one]
    first | refl_ring1 | ring
  · simp only [kleinTwPi, ptV, kleinPointT, ZV, planeV, chiV, pl4, kleinTwR, kleinTwR0,
      kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4, map_mul, map_pow, map_add, map_sub, map_neg,
      map_one, map_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    first | refl_ring1 | ring

/-! ## The composed link identity and its consequences for `fwTheta` -/

theorem kleinTwQ_CV (a b h : K) (p : Fin 5 → K) :
    kleinTwQ (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun i => (MvPolynomial.C (p i) : MvPolynomial (Fin 2) K))
      = MvPolynomial.C (kleinTwQ a b h p) := by
  simp only [kleinTwQ, kleinTwP0, map_mul, map_pow, map_add, map_sub, map_neg]

theorem fwQ_ptV (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    kleinTwQ (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptV a b h) = 0 := by
  rw [show ptV a b h
      = fun i => (MvPolynomial.C (kleinPointT a b h i) : MvPolynomial (Fin 2) K) from rfl,
    kleinTwQ_CV a b h (kleinPointT a b h), kleinTwQ_kleinPointT a b h ha hh, map_zero]

theorem fwCompV (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptV a b h)
          (chiV a b h))
      = fun k => kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (ptV a b h) (ZV a b h) ^ 2
          * kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (planeV K)
          * planeV K k := by
  have hq : kleinTwQ (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptV a b h) = 0 :=
    fwQ_ptV a b h ha hh
  have hw : planeV K 0 = 0 := rfl
  have hmain := KleinTwLinkComp1 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (ptV a b h) (planeV K) hq hw
  rw [show kleinTwPi (ptV a b h)
        (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (planeV K))
      = chiV a b h from FwChiPiV a b h ha hb hh] at hmain
  exact hmain

theorem fwAeval_chiV (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (k : Fin 5) :
    MvPolynomial.aeval (chiV a b h) (fwPoly K a b h k) = fwMuV a b h * planeV K k := by
  rw [AevalFwPoly (A := MvPolynomial (Fin 2) K) a b h (chiV a b h) k, MvPolynomial.algebraMap_eq]
  show kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptV a b h)
        (chiV a b h)) k
    = fwMuV a b h * planeV K k
  rw [fwCompV a b h ha hb hh]
  rfl

/-- The chart `chart3` written with pattern matching, so that its values reduce definitionally. -/
def chart3V (K' : Type*) [Field K'] : Fin 5 → MvPolynomial (Fin 3) K'
  | 0 => 0
  | 1 => MvPolynomial.X 0
  | 2 => MvPolynomial.X 1
  | 3 => MvPolynomial.X 2
  | 4 => 1

theorem chart3_eq_chart3V : chart3 K = chart3V K := by
  funext i
  fin_cases i <;> rfl

theorem fwTheta_chart3V (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    (fun i : Fin 5 => fwTheta a b h (chart3 K i))
      = ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (pl4 a b h))⁻¹)
        • (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (chiV a b h i)) := by
  have h4 : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (pl4 a b h) ≠ 0 :=
    fun h0 => pl4_ne_zero a b h ha hb hh (IsFractionRing.injective (MvPolynomial (Fin 2) K)
      (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero]))
  rw [show chart3 K = chart3V K from chart3_eq_chart3V]
  funext i
  fin_cases i <;> simp only [fin5_zero, fin5_one, fin5_two, fin5_three, fin5_four]
  all_goals
    (simp only [Pi.smul_apply, smul_eq_mul, chiV, chart3V, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fwTheta,
      fwParam, MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_zero, map_one, mul_zero,
      zero_mul] <;>
      field_simp [h4])

theorem fwTheta_compV (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (k : Fin 5) :
    fwTheta a b h (fwVec a b h k)
      = ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (pl4 a b h))⁻¹) ^ 4 *
        algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (fwMuV a b h * planeV K k) := by
  have hvec := fwTheta_chart3V a b h ha hb hh
  rw [fwVec_eq_aeval (K := K) a b h k,
    Work.MotK.UnitChartCAux.algHom_aeval (fwTheta a b h) (chart3 K) (fwPoly K a b h k), hvec]
  rw [show (((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (pl4 a b h))⁻¹) •
        (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (chiV a b h i)))
      = (fun i => ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (pl4 a b h))⁻¹) *
          algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (chiV a b h i)) from rfl]
  rw [aeval_smul_fwPoly a b h
      ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (pl4 a b h))⁻¹)
      (fun j => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (chiV a b h j)) k,
    show (fun j => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (chiV a b h j))
        = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))) ∘
            (chiV a b h) from rfl,
    MvPolynomial.aeval_algebraMap_apply (FractionRing (MvPolynomial (Fin 2) K)) (chiV a b h)
      (fwPoly K a b h k),
    fwAeval_chiV a b h ha hb hh k]

end

theorem FwVec4ParamClean {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 4) = 0 ∧
    Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 3) ≠ 0 ∧
    Work.MotK.TGen.fwU K * Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 3)
      = Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 1) ∧
    Work.MotK.TGen.fwV K * Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 3)
      = Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 2) := by
  have h4 : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (pl4 a b h) ≠ 0 :=
    fun h0 => pl4_ne_zero a b h ha hb hh (IsFractionRing.injective (MvPolynomial (Fin 2) K)
      (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero]))
  have hMu : fwMuV a b h ≠ 0 := fwMuV_ne_zero a b h ha hb hh
  have hT3 : fwTheta a b h (fwVec a b h 3)
      = ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (pl4 a b h))⁻¹) ^ 4 *
        algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (fwMuV a b h * planeV K 3) :=
    fwTheta_compV a b h ha hb hh 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fwTheta_compV a b h ha hb hh 4, show planeV K 4 = 0 from rfl, mul_zero, map_zero, mul_zero]
  · rw [hT3, show planeV K 3 = 1 from rfl, mul_one]
    exact mul_ne_zero (pow_ne_zero 4 (inv_ne_zero h4))
      (fun h0 => hMu (IsFractionRing.injective (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero])))
  · rw [hT3, fwTheta_compV a b h ha hb hh 1, show planeV K 3 = 1 from rfl,
      show planeV K 1 = MvPolynomial.X 0 from rfl, mul_one]
    simp only [fwU, map_mul]
    first | refl_ring1 | ring
  · rw [hT3, fwTheta_compV a b h ha hb hh 2, show planeV K 3 = 1 from rfl,
      show planeV K 2 = MvPolynomial.X 1 from rfl, mul_one]
    simp only [fwV, map_mul]
    first | refl_ring1 | ring

end Work.MotK.TGen
