/-
Auxiliary lemmas for the `T`-twisted Crauder--Katz link on the cubic surface `{cubTRed = 0}`.

These are the two ingredients that the residue-field computation in
`Submission/Work/MotK/TGen/CubTResidue.lean` needs but that live at the level of the explicit
parametrisation (see `Submission/Work/MotK/TGen/CubTPara.lean`, `CubTDefs.lean`):

* `cubQd_four_ne_zero`   : the common denominator `cubQd a b h 4` of the parametrisation does not vanish;
* `thetaMap_rvec_mul`: `thetaMap a b h (rvec a b h j) · D³ = algebraMap (s (cubY) · cubY j)`, the
  identity expressing that the two "mutually inverse" descriptions of the link map agree.

The proof of `thetaMap_rvec_mul` goes through the proportionality `cubY = C (a·b³·h) • paraPt` (so that
`paraCoord k = C ((a·b³·h)⁻¹)² · cubQd k`), the homogeneity of `kleinTwR` in its vector argument,
the twisted inverse identity `KleinTwI1`, and the homogeneity of `cubQd`, `kleinTwS` under `aeval`.
-/
import Mathlib
import Submission.Work.MotK.TGen.CubTDefs
import Submission.Work.MotK.TGen.AevalFwPoly
import Submission.Work.MotK.KleinTwI1
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.TwAmbh
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

noncomputable section

/-! ## The `Fin.mk`-versus-`OfNat` bridge for `Fin 3` (the `Fin 5` case is `Work.MotK.fin5_*`) -/

theorem fin3_zero (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
theorem fin3_one (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
theorem fin3_two (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl

/-! ## The components of the chart `chart3` (reduction lemmas for the literal indices) -/

theorem cubChart3_zero : Work.MotK.chart3 K 0 = (0 : MvPolynomial (Fin 3) K) := rfl
theorem cubChart3_one : Work.MotK.chart3 K 1 = (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) := rfl
theorem cubChart3_two : Work.MotK.chart3 K 2 = (MvPolynomial.X 1 : MvPolynomial (Fin 3) K) := rfl
theorem cubChart3_three : Work.MotK.chart3 K 3 = (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) := rfl
theorem cubChart3_four : Work.MotK.chart3 K 4 = (1 : MvPolynomial (Fin 3) K) := rfl

/-! ## Explicit components of a length-five vector at a `Fin.mk` index

`fin_cases` produces `⟨k, _⟩`-indexed goals, for which Mathlib's `cons_val_succ` does not fire;
these `rfl`-lemmas do the job by definitional reduction. -/

theorem cubVec5_zero {α : Type*} (x0 x1 x2 x3 x4 : α) (h : 0 < 5) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) ⟨0, h⟩ = x0 := rfl
theorem cubVec5_one {α : Type*} (x0 x1 x2 x3 x4 : α) (h : 1 < 5) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) ⟨1, h⟩ = x1 := rfl
theorem cubVec5_two {α : Type*} (x0 x1 x2 x3 x4 : α) (h : 2 < 5) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) ⟨2, h⟩ = x2 := rfl
theorem cubVec5_three {α : Type*} (x0 x1 x2 x3 x4 : α) (h : 3 < 5) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) ⟨3, h⟩ = x3 := rfl
theorem cubVec5_four {α : Type*} (x0 x1 x2 x3 x4 : α) (h : 4 < 5) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) ⟨4, h⟩ = x4 := rfl

theorem cubVecN_zero {α : Type*} (x0 x1 x2 x3 x4 : α) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) 0 = x0 := rfl
theorem cubVecN_one {α : Type*} (x0 x1 x2 x3 x4 : α) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) 1 = x1 := rfl
theorem cubVecN_two {α : Type*} (x0 x1 x2 x3 x4 : α) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) 2 = x2 := rfl
theorem cubVecN_three {α : Type*} (x0 x1 x2 x3 x4 : α) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) 3 = x3 := rfl
theorem cubVecN_four {α : Type*} (x0 x1 x2 x3 x4 : α) :
    (![x0, x1, x2, x3, x4] : Fin 5 → α) 4 = x4 := rfl

/-! ## The denominator of the parametrisation -/

/-- **`cubQd a b h 4 ≠ 0`.**  The `u³`-coefficient of `cubQd a b h 4` is `-a⁵b⁵h`. -/
theorem cubQd_four_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    cubQd a b h 4 ≠ 0 := by
  intro h0
  have h1 : MvPolynomial.aeval (R := K) ![(Polynomial.X : Polynomial K), (0 : Polynomial K)]
      (cubQd a b h 4) = 0 := by rw [h0, map_zero]
  have h2 : MvPolynomial.aeval (R := K) ![(Polynomial.X : Polynomial K), (0 : Polynomial K)]
      (cubQd a b h 4)
      = Polynomial.C (-(a ^ 5 * b ^ 5 * h)) * Polynomial.X ^ 3
        + Polynomial.C (-(2 * a ^ 2 * b ^ 8 * h ^ 3)) * Polynomial.X := by
    simp only [cubQd, Work.MotK.kleinTwP_four, Work.MotK.kleinTwP4,
      cubY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Fin.isValue, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
      MvPolynomial.C_mul, MvPolynomial.C_pow, Polynomial.C_mul, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.algebraMap_eq] <;> ring
  rw [h2] at h1
  have h3 : (Polynomial.C (-(a ^ 5 * b ^ 5 * h)) * Polynomial.X ^ 3
      + Polynomial.C (-(2 * a ^ 2 * b ^ 8 * h ^ 3)) * Polynomial.X : Polynomial K).coeff 3
      = -(a ^ 5 * b ^ 5 * h) := by
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, if_pos rfl, Polynomial.coeff_C_mul_X,
      if_neg (by norm_num : ¬ (3 = 1)), add_zero]
  rw [h1] at h3
  simp only [Polynomial.coeff_zero] at h3
  have hne : a ^ 5 * b ^ 5 * h ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 5 ha) (pow_ne_zero 5 hb)) hh
  exact hne (neg_eq_zero.mp h3.symm)

/-! ## The proportionality `cubY = C (a·b³·h) • paraPt` -/

theorem cubY_eq_C_mul_paraPt (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    cubY a b h = fun j => MvPolynomial.C (a * b ^ 3 * h) * paraPt a b h j := by
  have hc : a * b ^ 3 * h ≠ 0 := mul_ne_zero (mul_ne_zero ha (pow_ne_zero 3 hb)) hh
  funext j
  fin_cases j
  · show MvPolynomial.C (a * b ^ 3 * h) * MvPolynomial.X 0
        = MvPolynomial.C (a * b ^ 3 * h) * MvPolynomial.X 0
    first | refl_ring1 | ring
  · show -(MvPolynomial.C (a * b) * MvPolynomial.X 0
          - MvPolynomial.C (a ^ 2 * h) * MvPolynomial.X 1) ^ 2
        = MvPolynomial.C (a * b ^ 3 * h)
          * (MvPolynomial.C (-(1 / (a * b ^ 3 * h)))
            * (MvPolynomial.C (a * b) * MvPolynomial.X 0
              - MvPolynomial.C (a ^ 2 * h) * MvPolynomial.X 1) ^ 2)
    have h1 : a * b ^ 3 * h * (-(1 / (a * b ^ 3 * h))) = -1 := by
      rw [one_div, mul_neg, mul_inv_cancel₀ hc]
    rw [← mul_assoc, ← MvPolynomial.C_mul, h1, MvPolynomial.C_neg, MvPolynomial.C_1]
    first | refl_ring1 | ring
  · show MvPolynomial.C (a * b ^ 2 * h)
        * (MvPolynomial.C (2 * b) * MvPolynomial.X 0 - MvPolynomial.C (a * h) * MvPolynomial.X 1)
        = MvPolynomial.C (a * b ^ 3 * h)
          * (MvPolynomial.C 2 * MvPolynomial.X 0 - MvPolynomial.C (a * h / b) * MvPolynomial.X 1)
    have hb3 : b ^ 3 * b⁻¹ = b ^ 2 := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    have h2a : a * b ^ 2 * h * (2 * b) = a * b ^ 3 * h * 2 := by ring
    have h2b : a * b ^ 2 * h * (a * h) = a * b ^ 3 * h * (a * h / b) := by
      rw [div_eq_mul_inv, ← hb3]
      first | refl_ring1 | ring
    rw [mul_sub, mul_sub]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul, ← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
    rw [h2a, h2b]
  · show MvPolynomial.C (a * b ^ 3 * h) * MvPolynomial.X 1
        = MvPolynomial.C (a * b ^ 3 * h) * MvPolynomial.X 1
    first | refl_ring1 | ring
  · show MvPolynomial.C (a * b ^ 3 * h) = MvPolynomial.C (a * b ^ 3 * h) * 1
    first | refl_ring1 | ring

/-- `paraPt` is the scalar multiple `C ((a·b³·h)⁻¹)` of `cubY`. -/
theorem paraPt_eq (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    paraPt a b h = fun j => MvPolynomial.C ((a * b ^ 3 * h)⁻¹) * cubY a b h j := by
  have hc : a * b ^ 3 * h ≠ 0 := mul_ne_zero (mul_ne_zero ha (pow_ne_zero 3 hb)) hh
  funext j
  have h := congrFun (cubY_eq_C_mul_paraPt a b h ha hb hh) j
  rw [h, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc, MvPolynomial.C_1, one_mul]

/-- Every `kleinTwP k` is a quadratic form in the vector argument. -/
theorem aeval_smul_kleinTwP (a b h : K) (lam : MvPolynomial (Fin 2) K)
    (y : Fin 5 → MvPolynomial (Fin 2) K) (k : Fin 5) :
    MvPolynomial.aeval (fun j => lam * y j)
        (Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun t => (MvPolynomial.X t : MvPolynomial (Fin 5) K)) k)
      = lam ^ 2 * MvPolynomial.aeval y
          (Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (fun t => (MvPolynomial.X t : MvPolynomial (Fin 5) K)) k) := by
  fin_cases k <;>
    simp only [Work.MotK.fin5_zero, Work.MotK.fin5_one, Work.MotK.fin5_two, Work.MotK.fin5_three,
      Work.MotK.fin5_four, Work.MotK.kleinTwP_zero', Work.MotK.kleinTwP_one',
      Work.MotK.kleinTwP_two', Work.MotK.kleinTwP_three', Work.MotK.kleinTwP_four',
      Work.MotK.kleinTwP_zero, Work.MotK.kleinTwP_one, Work.MotK.kleinTwP_two,
      Work.MotK.kleinTwP_three, Work.MotK.kleinTwP_four, Work.MotK.kleinTwP0,
      Work.MotK.kleinTwP1, Work.MotK.kleinTwP2, Work.MotK.kleinTwP3, Work.MotK.kleinTwP4,
      map_add, map_sub, map_mul, map_neg, map_pow, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X] <;>
    first | refl_ring1 | ring

/-- The cleared coordinates are the parametrised ones up to the constant factor
`C ((a·b³·h)⁻¹)²`. -/
theorem paraCoord_eq (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (k : Fin 5) :
    paraCoord a b h k =
      MvPolynomial.C ((a * b ^ 3 * h)⁻¹) ^ 2 * cubQd a b h k := by
  have hp := paraPt_eq a b h ha hb hh
  simp only [paraCoord, cubQd]
  rw [hp, aeval_smul_kleinTwP]

/-! ## The bridge `thetaMap (X i) · D = cubQd (cubIx i)` -/

theorem thetaMap_X_mul (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (i : Fin 3) :
    thetaMap a b h (MvPolynomial.X i)
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubQd a b h 4)
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (cubQd a b h (cubIx i)) := by
  have hc : a * b ^ 3 * h ≠ 0 := mul_ne_zero (mul_ne_zero ha (pow_ne_zero 3 hb)) hh
  have hunit : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.C ((a * b ^ 3 * h)⁻¹))
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.C (a * b ^ 3 * h)) = 1 := by
    rw [← map_mul, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc, MvPolynomial.C_1, map_one]
  have hne : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (MvPolynomial.C ((a * b ^ 3 * h)⁻¹)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hunit
    exact one_ne_zero hunit.symm
  have hCst : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (MvPolynomial.C ((a * b ^ 3 * h)⁻¹))) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hD : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubQd a b h 4)) ≠ 0 := fun h0 => cubQd_four_ne_zero a b h ha hb hh
        (IsFractionRing.injective (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (by rw [h0, map_zero]))
  have hk : ∀ k : Fin 5,
      algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (paraCoord a b h k)
        = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (MvPolynomial.C ((a * b ^ 3 * h)⁻¹))) ^ 2
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (cubQd a b h k) := by
    intro k
    rw [paraCoord_eq a b h ha hb hh k, map_mul, map_pow]
  rw [thetaMap, MvPolynomial.aeval_X]
  fin_cases i <;>
  · simp only [fin3_zero, fin3_one, fin3_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, cubIx_zero,
      cubIx_one, cubIx_two, hk 1, hk 2, hk 3, hk 4]
    rw [mul_div_mul_left _ _ hCst, div_mul_cancel₀ _ hD]

/-! ## `thetaMap ∘ chart3` -/

theorem thetaMap_chart3_point (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (t : Fin 5) :
    thetaMap a b h (Work.MotK.chart3 K t)
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubQd a b h t)
        / algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubQd a b h 4) := by
  have hD : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubQd a b h 4)) ≠ 0 := fun h0 => cubQd_four_ne_zero a b h ha hb hh
        (IsFractionRing.injective (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (by rw [h0, map_zero]))
  fin_cases t
  · simp only [Work.MotK.chart3, Work.MotK.fin5_zero, Matrix.cons_val_zero, Matrix.head_cons,
      Fin.isValue]
    rw [map_zero, cubQd_zero, map_zero, zero_div]
  · simp only [Work.MotK.chart3, Work.MotK.fin5_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Fin.isValue, cubIx_zero]
    rw [eq_div_iff hD]
    exact thetaMap_X_mul a b h ha hb hh 0
  · simp only [Work.MotK.chart3, Work.MotK.fin5_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue, cubIx_one]
    rw [eq_div_iff hD]
    exact thetaMap_X_mul a b h ha hb hh 1
  · simp only [Work.MotK.chart3, Work.MotK.fin5_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue,
      cubIx_two]
    rw [eq_div_iff hD]
    exact thetaMap_X_mul a b h ha hb hh 2
  · simp only [Work.MotK.chart3, Work.MotK.fin5_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons, Fin.isValue]
    rw [map_one, div_self hD]

/-! ## Pushing `thetaMap` through `kleinTwR` -/

theorem thetaMap_rvec (a b h : K) (j : Fin 5) :
    thetaMap a b h (rvec a b h j)
      = Work.MotK.kleinTwR
          (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
          (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
          (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
          (fun i => thetaMap a b h (Work.MotK.chart3 K i)) j := by
  have hfun : (fun i : Fin 5 => thetaMap a b h (Work.MotK.chart3 K i))
      = ![thetaMap a b h 0, thetaMap a b h (MvPolynomial.X 0), thetaMap a b h (MvPolynomial.X 1),
          thetaMap a b h (MvPolynomial.X 2), thetaMap a b h 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun]
  fin_cases j <;>
  · simp only [rvec, Work.MotK.kleinTwR_zero', Work.MotK.kleinTwR_one',
      Work.MotK.kleinTwR_two', Work.MotK.kleinTwR_three', Work.MotK.kleinTwR_four',
      Work.MotK.kleinTwR_zero, Work.MotK.kleinTwR_one, Work.MotK.kleinTwR_two,
      Work.MotK.kleinTwR_three, Work.MotK.kleinTwR_four, Work.MotK.kleinTwR,
      Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2, Work.MotK.kleinTwR3,
      Work.MotK.kleinTwR4, cubVec5_zero, cubVec5_one, cubVec5_two, cubVec5_three, cubVec5_four,
      cubVecN_zero, cubVecN_one, cubVecN_two, cubVecN_three, cubVecN_four,
      cubChart3_zero, cubChart3_one, cubChart3_two, cubChart3_three, cubChart3_four,
      map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one,
      MvPolynomial.C_eq_algebraMap, AlgHom.commutes] <;>
    first | refl_ring1 | ring

/-! ## `aeval (cubY)` commutes with the twisted data -/

/-- `aeval (cubY)` and `algebraMap` intertwined. -/
theorem algebraMap_aeval_cubY (a b h : K) (F : MvPolynomial (Fin 5) K) :
    algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (MvPolynomial.aeval (cubY a b h) F)
      = MvPolynomial.aeval
          (fun t => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubY a b h t)) F := by
  induction F using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 2) K)
      (FractionRing (MvPolynomial (Fin 2) K)) r).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p t hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]

/-- Evaluation commutes with the twisted secant quintic `s`. -/
theorem aeval_kleinTwS_gen {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a b h : K) (y : Fin 5 → A) :
    MvPolynomial.aeval y
        (Work.MotK.kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun t => (MvPolynomial.X t : MvPolynomial (Fin 5) K)))
      = Work.MotK.kleinTwS (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) y := by
  simp only [Work.MotK.kleinTwS, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]

/-- `algebraMap ∘ cubQd` is the value of `kleinTwP` at `algebraMap ∘ cubY`. -/
theorem algebraMap_cubQd_eq_kleinTwP (a b h : K) :
    (fun i : Fin 5 => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (cubQd a b h i))
      = Work.MotK.kleinTwP
          (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
          (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
          (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
          (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubY a b h i)) := by
  funext k
  rw [cubQd, algebraMap_aeval_cubY,
    aeval_kleinTwP_gen a b h (fun t => (MvPolynomial.X t : MvPolynomial (Fin 5) K))
      (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (cubY a b h i)) k]
  simp only [MvPolynomial.aeval_X, Function.comp_apply]

/-- `kleinTwS` at `algebraMap ∘ cubY` is `algebraMap` of `kleinTwS` at `cubY`. -/
theorem algebraMap_kleinTwS (a b h : K) :
    Work.MotK.kleinTwS
        (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
        (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
        (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
        (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (cubY a b h i))
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (Work.MotK.kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (cubY a b h)) := by
  rw [← aeval_kleinTwS_gen a b h
    (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubY a b h i))]
  rw [← algebraMap_aeval_cubY a b h
    (Work.MotK.kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun t => (MvPolynomial.X t : MvPolynomial (Fin 5) K)))]
  rw [aeval_kleinTwS_gen (K := K) (A := MvPolynomial (Fin 2) K) a b h (cubY a b h)]
  simp only [MvPolynomial.aeval_X, ← MvPolynomial.C_eq_algebraMap]

/-! ## The main identity -/

/-- **The parametrisation on the inverse link map.**  With `rvec` the components of the inverse
link map on the target chart and `D = cubQd a b h 4`, one has
`thetaMap a b h (rvec a b h j) · D³ = algebraMap (s (cubY) · cubY j)`. -/
theorem thetaMap_rvec_mul (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (j : Fin 5) :
    thetaMap a b h (rvec a b h j)
        * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubQd a b h 4)) ^ 3
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (Work.MotK.kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (cubY a b h) * cubY a b h j) := by
  have hD : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubQd a b h 4)) ≠ 0 := fun h0 => cubQd_four_ne_zero a b h ha hb hh
        (IsFractionRing.injective (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (by rw [h0, map_zero]))
  have hW := algebraMap_cubQd_eq_kleinTwP (K := K) a b h
  have hS := algebraMap_kleinTwS (K := K) a b h
  have hEW : (fun i : Fin 5 => (algebraMap (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K)) (cubQd a b h 4))
        * thetaMap a b h (Work.MotK.chart3 K i))
      = (fun i : Fin 5 => algebraMap (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K)) (cubQd a b h i)) := by
    funext i
    rw [thetaMap_chart3_point a b h ha hb hh i, mul_div_cancel₀ _ hD]
  calc
    thetaMap a b h (rvec a b h j)
        * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubQd a b h 4)) ^ 3
        = Work.MotK.kleinTwR (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
              (fun i => thetaMap a b h (Work.MotK.chart3 K i)) j
            * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                (cubQd a b h 4)) ^ 3 := by rw [thetaMap_rvec]
    _ = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubQd a b h 4)) ^ 3
          * Work.MotK.kleinTwR (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
              (fun i => thetaMap a b h (Work.MotK.chart3 K i)) j := by ring
    _ = Work.MotK.kleinTwR (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
              (fun i => (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                (cubQd a b h 4)) * thetaMap a b h (Work.MotK.chart3 K i)) j := by
          rw [← congrFun (Work.MotK.kleinTwR_homog _ _ _
            (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (cubQd a b h 4))
            (fun i => thetaMap a b h (Work.MotK.chart3 K i))) j]
    _ = Work.MotK.kleinTwR (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
              (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                (cubQd a b h i)) j := by rw [hEW]
    _ = Work.MotK.kleinTwS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
              (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                (cubY a b h i))
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (cubY a b h j) := by
          simp only [hW, Work.MotK.KleinTwI1]
    _ = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (Work.MotK.kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (cubY a b h) * cubY a b h j) := by
          rw [map_mul, ← hS]

end

end Work.MotK.TGen
