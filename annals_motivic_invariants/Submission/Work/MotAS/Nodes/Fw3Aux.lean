import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASRulV2M.Defs
import Submission.Work.MotAS.ASRulV2M.HcAuxRelaxed
import Submission.Work.MotK.TGen.FwTopDefs
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Nodes.Fw3` — the explicit data for `fwVecAS2 a b g 3`

The forward chart denominator of the AS link is

`fwVecAS2 a b g 3 = kleinPAS3 (kleinStereoAS (pAS0) (chart3))`,

and (CAS, verified over `ℤ`) it factors as

`fwVecAS2 a b g 3 = C 4 · C A² · asH`,     `A = a ^ 2 - a * b - b ^ 2`,

where `asH` is the polynomial defined below.  Writing

`asQ = A·(X 1² + 2 X 0 X 2) - 2(a² + b²)·X 2²`  (the conic, homogeneous of degree `2`),

the degree-`3` part of `asH` is `asH3 = -(X 2 · asQ)` and the degree-`≤ 2` part is `asHlo`; in
particular `asH` is *linear in `X 0`*

`asH = (2A·(X 1 - X 2²) + (a² + b²))·X 0 + (-A·X 1²X 2 + 2(a²+b²)·X 2³ - (4a²+ab-4b²)·X 2 + A·g)`.

The file also fixes the quintic-form polynomial `secPoly` in five variables whose `aeval` at the
stereographic vector is `sAS2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace Work.MotAS.Nodes.Fw3

open MvPolynomial

/-- `A = a² - ab - b²`, the discriminant of the Klein quintic (nonzero in the AS branch). -/
noncomputable def asA {K : Type*} [CommRing K] (a b : K) : K := a ^ 2 - a * b - b ^ 2

/-- `B = a² + b²`. -/
noncomputable def asB {K : Type*} [CommRing K] (a b : K) : K := a ^ 2 + b ^ 2

/-- The conic `asQ = A·(X 1² + 2 X 0 X 2) - 2B·X 2²`. -/
noncomputable def asQ {K : Type*} [CommRing K] (a b : K) : MvPolynomial (Fin 3) K :=
  C (asA a b) * (X 1 ^ 2 + C 2 * X 0 * X 2) - C (2 * asB a b) * X 2 ^ 2

/-- The degree-`3` part of `asH`: `asH3 = -(X 2 · asQ)`. -/
noncomputable def asH3 {K : Type*} [CommRing K] (a b : K) : MvPolynomial (Fin 3) K :=
  -(X 2 * asQ a b)

/-- The degree-`≤ 2` part of `asH`. -/
noncomputable def asHlo {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  C (2 * asA a b) * (X 0 * X 1) + C (asB a b) * X 0 + C (-(3 * asB a b)) * X 1 * X 2
    + C (-(4 * a ^ 2 + a * b - 4 * b ^ 2)) * X 2 + C (asA a b * g)

/-- The cubic `asH` with `fwVecAS2 a b g 3 = C 4 · C A² · asH`.  It is linear in `X 0`. -/
noncomputable def asH {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  asHlo a b g + asH3 a b

/-- `asH` decomposes into its degree-`≤ 2` part and the degree-`3` form `asH3`. -/
theorem asH_eq_lo_add {K : Type*} [CommRing K] (a b g : K) :
    asH a b g = asHlo a b g + asH3 a b := rfl

/-- The explicit shape of `asH`: linear in `X 0`. -/
theorem asH_eq_linear {K : Type*} [CommRing K] (a b g : K) :
    asH a b g
      = C (2 * asA a b) * (X 0 * X 1) + C (asB a b) * X 0
        + C (-(3 * asB a b)) * X 1 * X 2 + C (-(4 * a ^ 2 + a * b - 4 * b ^ 2)) * X 2
        + C (asA a b * g) + -(X 2 * asQ a b) := rfl

/-- `asQ` is homogeneous of degree `2`. -/
theorem asQ_isHomogeneous {K : Type*} [CommRing K] (a b : K) : (asQ a b).IsHomogeneous 2 := by
  have h2 : ((X 1 : MvPolynomial (Fin 3) K) ^ 2).IsHomogeneous 2 :=
    (isHomogeneous_X K 1).pow 2
  have h02 : (C (2 : K) * X 0 * X 2 : MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
    (((isHomogeneous_C (Fin 3) (2 : K)).mul (isHomogeneous_X K 0)).mul
      (isHomogeneous_X K 2))
  have h22 : ((X 2 : MvPolynomial (Fin 3) K) ^ 2).IsHomogeneous 2 :=
    (isHomogeneous_X K 2).pow 2
  have hbr : (X 1 ^ 2 + C (2 : K) * X 0 * X 2 : MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
    h2.add h02
  have hleft : (C (asA a b) * (X 1 ^ 2 + C (2 : K) * X 0 * X 2) :
      MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
    (isHomogeneous_C (Fin 3) (asA a b)).mul hbr
  have hright : (C (2 * asB a b) * X 2 ^ 2 : MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
    (isHomogeneous_C (Fin 3) (2 * asB a b)).mul h22
  rw [asQ]
  exact hleft.sub hright

/-- `asH3` is homogeneous of degree `3`. -/
theorem asH3_isHomogeneous {K : Type*} [CommRing K] (a b : K) : (asH3 a b).IsHomogeneous 3 := by
  rw [asH3]
  exact (IsHomogeneous.mul (isHomogeneous_X K 2) (asQ_isHomogeneous a b)).neg

/-- `asHlo` has total degree at most `2`. -/
theorem asHlo_totalDegree_le {K : Type*} [CommRing K] [Nontrivial K] (a b g : K) :
    (asHlo a b g).totalDegree ≤ 2 := by
  have hX : ∀ i : Fin 3, ((X i : MvPolynomial (Fin 3) K)).IsHomogeneous 1 := fun i =>
    isHomogeneous_X K i
  have h1 : Work.MotAS.ASRulV2M.HcR.Bound
      (C (2 * asA a b) * (X 0 * X 1) : MvPolynomial (Fin 3) K) 2 :=
    Work.MotAS.ASRulV2M.HcR.Bound.C_mul (2 * asA a b)
      ((Work.MotAS.ASRulV2M.HcR.Bound.of_isHomogeneous (hX 0)).mul
        (Work.MotAS.ASRulV2M.HcR.Bound.of_isHomogeneous (hX 1)))
  have h2 : Work.MotAS.ASRulV2M.HcR.Bound (C (asB a b) * X 0 : MvPolynomial (Fin 3) K) 2 :=
    (Work.MotAS.ASRulV2M.HcR.Bound.C_mul (asB a b)
      (Work.MotAS.ASRulV2M.HcR.Bound.of_isHomogeneous (hX 0))).mono (by norm_num)
  have h3 : Work.MotAS.ASRulV2M.HcR.Bound
      (C (-(3 * asB a b)) * X 1 * X 2 : MvPolynomial (Fin 3) K) 2 :=
    (Work.MotAS.ASRulV2M.HcR.Bound.C_mul (-(3 * asB a b))
      (Work.MotAS.ASRulV2M.HcR.Bound.of_isHomogeneous (hX 1))).mul
      (Work.MotAS.ASRulV2M.HcR.Bound.of_isHomogeneous (hX 2))
  have h4 : Work.MotAS.ASRulV2M.HcR.Bound
      (C (-(4 * a ^ 2 + a * b - 4 * b ^ 2)) * X 2 : MvPolynomial (Fin 3) K) 2 :=
    (Work.MotAS.ASRulV2M.HcR.Bound.C_mul (-(4 * a ^ 2 + a * b - 4 * b ^ 2))
      (Work.MotAS.ASRulV2M.HcR.Bound.of_isHomogeneous (hX 2))).mono (by norm_num)
  have h5 : Work.MotAS.ASRulV2M.HcR.Bound
      (C (asA a b * g) : MvPolynomial (Fin 3) K) 2 :=
    (Work.MotAS.ASRulV2M.HcR.Bound.of_isHomogeneous
      (isHomogeneous_C (Fin 3) (asA a b * g))).mono (by norm_num)
  rw [asHlo]
  exact Work.MotAS.ASRulV2M.HcR.Bound.totalDegree_le
    (Work.MotAS.ASRulV2M.HcR.Bound.add
      (Work.MotAS.ASRulV2M.HcR.Bound.add
        (Work.MotAS.ASRulV2M.HcR.Bound.add
          (Work.MotAS.ASRulV2M.HcR.Bound.add h1 h2) h3) h4) h5)

/-- The degree-`3` homogeneous component of `asH` is `asH3`. -/
theorem homogeneousComponent_three_asH {K : Type*} [CommRing K] [Nontrivial K] (a b g : K) :
    MvPolynomial.homogeneousComponent 3 (asH a b g) = asH3 a b := by
  rw [asH_eq_lo_add, map_add,
    MvPolynomial.homogeneousComponent_eq_zero 3 (asHlo a b g)
      (lt_of_le_of_lt (asHlo_totalDegree_le a b g) (by norm_num)), zero_add,
    MvPolynomial.homogeneousComponent_eq_self (asH3_isHomogeneous a b)]

/-- Evaluation at `(0, 1, 0)` kills `asH3`. -/
theorem eval_asH3 {K : Type*} [CommRing K] (a b : K) :
    MvPolynomial.eval (![0, 1, 0] : Fin 3 → K) (asH3 a b) = 0 := by
  rw [asH3, asQ]
  simp only [map_neg, map_mul, map_sub, map_add, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

/-- Evaluation at `(0, 1, 0)` gives `A` on `asQ`. -/
theorem eval_asQ {K : Type*} [CommRing K] (a b : K) :
    MvPolynomial.eval (![0, 1, 0] : Fin 3 → K) (asQ a b) = asA a b := by
  simp only [asQ, asA, asB, map_sub, map_add, map_mul, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

/-- `asQ ≠ 0` when `A ≠ 0`. -/
theorem asQ_ne_zero {K : Type*} [CommRing K] (a b : K) (hA : asA a b ≠ 0) : asQ a b ≠ 0 := by
  intro h
  have h1 := eval_asQ a b
  rw [h, map_zero] at h1
  exact hA h1.symm

/-- `asH3 ≠ 0` when `A ≠ 0`. -/
theorem asH3_ne_zero {K : Type*} [Field K] (a b : K) (hA : asA a b ≠ 0) : asH3 a b ≠ 0 := by
  rw [asH3]
  exact neg_ne_zero.mpr (mul_ne_zero (MvPolynomial.X_ne_zero 2) (asQ_ne_zero a b hA))

/-- `asH` has total degree `3` (when `A ≠ 0`). -/
theorem asH_totalDegree {K : Type*} [Field K] (a b g : K) (hA : asA a b ≠ 0) :
    (asH a b g).totalDegree = 3 := by
  have h3ne := asH3_ne_zero a b hA
  have hcomp := homogeneousComponent_three_asH a b g
  have hle : (asH a b g).totalDegree ≤ 3 := by
    rw [asH_eq_lo_add]
    refine (MvPolynomial.totalDegree_add _ _).trans ?_
    exact max_le
      ((asHlo_totalDegree_le a b g).trans (by norm_num))
      (asH3_isHomogeneous a b).totalDegree_le
  have hge : 3 ≤ (asH a b g).totalDegree := by
    by_contra hcon
    have hcon' : (asH a b g).totalDegree < 3 := Nat.lt_of_not_le hcon
    rw [MvPolynomial.homogeneousComponent_eq_zero 3 (asH a b g) hcon'] at hcomp
    exact h3ne hcomp.symm
  exact le_antisymm hle hge

/-- The top form of `asH` is `asH3`. -/
theorem topForm_asH {K : Type*} [Field K] (a b g : K) (hA : asA a b ≠ 0) :
    Work.MotK.TGen.topForm (asH a b g) = asH3 a b := by
  rw [Work.MotK.TGen.topForm, asH_totalDegree a b g hA]
  exact homogeneousComponent_three_asH a b g

/-- `asH ≠ 0` when `A ≠ 0`. -/
theorem asH_ne_zero {K : Type*} [Field K] (a b g : K) (hA : asA a b ≠ 0) : asH a b g ≠ 0 := by
  intro h
  have := asH_totalDegree a b g hA
  rw [h, MvPolynomial.totalDegree_zero] at this
  exact absurd this (by norm_num)

/-- `X 2` does not divide `asQ` when `A ≠ 0`. -/
theorem not_dvd_X2_asQ {K : Type*} [Field K] (a b : K) (hA : asA a b ≠ 0) : ¬ (X 2 ∣ asQ a b) := by
  rintro ⟨m, hm⟩
  have h := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → K)) hm
  simp only [map_mul] at h
  have hX2 : MvPolynomial.eval (![0, 1, 0] : Fin 3 → K) (X 2 : MvPolynomial (Fin 3) K) = 0 := by
    simp [MvPolynomial.eval_X]
  rw [eval_asQ, hX2, zero_mul] at h
  exact hA h

/-- The secant quintic of the AS chart as a polynomial in its five arguments with coefficients in
the base field. -/
noncomputable def secPoly (K : Type) [CommRing K] (a b g : K) : MvPolynomial (Fin 5) K :=
  Work.MotAS.kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (fun i => MvPolynomial.X i)

end Work.MotAS.Nodes.Fw3
