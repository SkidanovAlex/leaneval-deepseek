import Mathlib
import Submission.Work.MotAS.ASRul.Matrices
import Submission.Work.MotAS.ASResidual
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000

namespace Work.MotAS.ASRul

open Matrix MvPolynomial

/-! ## The explicit AS ruling vectors (polynomials) -/

/-- **The first AS ruling vector** (the `Work.MotAS.ASrulV` polynomial, denominators cleared). -/
noncomputable def kbRv {K : Type*} [Field K] (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![C (a + 2 * b) * (C (2 * a) * X 0 * X 1 - C a * X 1 * X 2 - C a * X 2 - C b * X 0 * X 1
        + C (2 * b) * X 1 * X 2 - C (2 * b) * X 2),
    C (2 * a - b) * (C (2 * a) * X 1 ^(2:ℕ) + C a * X 2 ^(2:ℕ) - C b * X 1 ^(2:ℕ)
        - C (2 * b) * X 2 ^(2:ℕ)),
    C (2 * a - b) * C (a + 2 * b) * (X 1 * X 2),
    C (2 * a - b) * C (a + 2 * b) * X 2 ^(2:ℕ),
    0]

/-- **The second AS ruling vector** (the `Work.MotAS.ASrulW` polynomial, denominators cleared). -/
noncomputable def kbRw {K : Type*} [Field K] (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![-C (a + 2 * b) * (C (4 * a ^(2:ℕ)) * X 0 ^(2:ℕ) + C (4 * a ^(2:ℕ)) * X 0 * X 2
        - C (3 * a ^(2:ℕ)) * X 2 ^(2:ℕ) - C (4 * a * b) * X 0 ^(2:ℕ) + C (10 * a * b) * X 0 * X 2
        - C (a * b) * X 2 ^(2:ℕ) + C (b ^(2:ℕ)) * X 0 ^(2:ℕ) - C (b ^(2:ℕ)) * X 0 * X 2
        - C (2 * b ^(2:ℕ)) * X 2 ^(2:ℕ)),
    -C (2 * a - b) * (C (4 * a ^(2:ℕ)) * X 0 * X 1 + C (6 * a ^(2:ℕ)) * X 1 * X 2
        + C (2 * a ^(2:ℕ)) * X 2 - C (4 * a * b) * X 0 * X 1 + C (5 * a * b) * X 1 * X 2
        + C (3 * a * b) * X 2 + C (b ^(2:ℕ)) * X 0 * X 1 + C (b ^(2:ℕ)) * X 1 * X 2
        - C (2 * b ^(2:ℕ)) * X 2),
    -C (a + 2 * b) * C (2 * a - b) * X 2
        * (C (2 * a) * X 0 + C (2 * a) * X 2 - C b * X 0 + C b * X 2),
    0,
    C (a + 2 * b) ^(2:ℕ) * C (2 * a - b) * X 2 ^(2:ℕ)]

/-- The evaluated first AS ruling vector. -/
noncomputable def rvEv {K : Type*} [Field K] (a b g u v w : K) : Fin 5 → K :=
  ![(a + 2 * b) * (2 * a * u * v - a * v * w - a * w - b * u * v + 2 * b * v * w - 2 * b * w),
    (2 * a - b) * ((2 * a - b) * v ^(2:ℕ) + (a - 2 * b) * w ^(2:ℕ)),
    (2 * a - b) * (a + 2 * b) * (v * w),
    (2 * a - b) * (a + 2 * b) * w ^(2:ℕ),
    0]

/-- The evaluated second AS ruling vector. -/
noncomputable def rwEv {K : Type*} [Field K] (a b g u v w : K) : Fin 5 → K :=
  ![-(a + 2 * b) * ((4 * a ^(2:ℕ) - 4 * a * b + b ^(2:ℕ)) * u ^(2:ℕ)
        + (4 * a ^(2:ℕ) + 10 * a * b - b ^(2:ℕ)) * u * w
        + (-3 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ)) * w ^(2:ℕ)),
    -(2 * a - b) * ((4 * a ^(2:ℕ) - 4 * a * b + b ^(2:ℕ)) * u * v
        + (6 * a ^(2:ℕ) + 5 * a * b + b ^(2:ℕ)) * v * w
        + (2 * a ^(2:ℕ) + 3 * a * b - 2 * b ^(2:ℕ)) * w),
    -(a + 2 * b) * (2 * a - b) * w * ((2 * a - b) * u + (2 * a + b) * w),
    0,
    (2 * a - b) * (a + 2 * b) ^(2:ℕ) * w ^(2:ℕ)]

/-! ## The explicit chart matrix and its rows -/

/-- The AS ruling matrix at the chart point `(1,u,v,w,0)`, in explicit form. -/
theorem AmatAS_chartPt_eq {K : Type*} [CommRing K] (a b g u v w : K) :
    AmatAS a b g ![1, u, v, w, 0]
      = !![0, 0, -a * w - 2 * b * w, a * v + 2 * b * v, -2 * a * u - 2 * a * w + b * u - b * w;
           0, a * w + 2 * b * w, -2 * a * v + b * v, -a * w + 2 * b * w,
             2 * a * v + 2 * a + b * v - b;
           -2 * a * w + b * w, 0, 2 * a * u - a * w - b * u + 2 * b * w, -a - 2 * b,
             -2 * a * u + a * w - b * u + 2 * b * w;
           2 * a * v - b * v, -a * u - 2 * b * u, a * v + a - 2 * b * v + 2 * b, a * u - 2 * b * u,
             -a * v + 2 * a - 2 * b * v + b;
           a * u - a * w + 2 * b * u + 2 * b * w, 2 * a * v - 2 * a + b * v + b,
             a * u - 2 * a * w - 2 * b * u + b * w,
             2 * a * g * w - 2 * a * v - 2 * a - b * g * w + b * v - b,
             -a * g * v - a * u + 2 * a * w - 2 * b * g * v - 2 * b * u + b * w] := by
  ext i l
  fin_cases i <;> fin_cases l <;>
  · simp only [AmatAS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Fin.isValue,
      Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one]
    try ring

/-- The zeroth row of the AS ruling matrix at the chart point. -/
theorem AmatAS_row0 {K : Type*} [CommRing K] (a b g u v w : K) (z : Fin 5 → K) :
    (Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0]) z) 0
      = -a * w * z 2 - 2 * b * w * z 2 + (a * v * z 3 + 2 * b * v * z 3)
        + (-2 * a * u) * z 4 - 2 * a * w * z 4 + b * u * z 4 - b * w * z 4 := by
  rw [AmatAS_chartPt_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_eq] <;> ring

/-- The first row of the AS ruling matrix at the chart point. -/
theorem AmatAS_row1 {K : Type*} [CommRing K] (a b g u v w : K) (z : Fin 5 → K) :
    (Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0]) z) 1
      = (a * w * z 1 + 2 * b * w * z 1) - 2 * a * v * z 2 + b * v * z 2
        + (-a * w * z 3 + 2 * b * w * z 3)
        + (2 * a * v * z 4 + 2 * a * z 4 + b * v * z 4 - b * z 4) := by
  rw [AmatAS_chartPt_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_eq] <;> ring

/-- The second row of the AS ruling matrix at the chart point. -/
theorem AmatAS_row2 {K : Type*} [CommRing K] (a b g u v w : K) (z : Fin 5 → K) :
    (Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0]) z) 2
      = -2 * a * w * z 0 + b * w * z 0 + (2 * a * u * z 2 - a * w * z 2 - b * u * z 2
          + 2 * b * w * z 2) + (-a - 2 * b) * z 3
        + (-2 * a * u + a * w - b * u + 2 * b * w) * z 4 := by
  rw [AmatAS_chartPt_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_eq] <;> ring

/-! ## Evaluation of the ruling vectors -/

/-- The evaluation of `kbRv` at `(u,v,w)` is `rvEv`. -/
theorem eval_kbRv {K : Type*} [Field K] (a b g u v w : K) :
    (fun i => MvPolynomial.eval ![u, v, w] (kbRv a b g i)) = rvEv a b g u v w := by
  funext i
  fin_cases i <;>
  · simp [kbRv, rvEv, Matrix.cons_val', Matrix.of_apply, MvPolynomial.eval_C,
      MvPolynomial.eval_X, true_or, or_true]
    all_goals (try ring; try exact Or.inl trivial; try tauto)

/-- The evaluation of `kbRw` at `(u,v,w)` is `rwEv`. -/
theorem eval_kbRw {K : Type*} [Field K] (a b g u v w : K) :
    (fun i => MvPolynomial.eval ![u, v, w] (kbRw a b g i)) = rwEv a b g u v w := by
  funext i
  fin_cases i <;>
  · simp [kbRw, rwEv, Matrix.cons_val', Matrix.of_apply, MvPolynomial.eval_C,
      MvPolynomial.eval_X, true_or, or_true]
    all_goals (try ring; try exact Or.inl trivial; try tauto)

/-! ## The base curve equations, expanded -/

/-- The fourth base-curve cubic, expanded. -/
theorem eval_zcubAS_four {K : Type*} [Field K] (a b g u v w : K) :
    MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g 4)
      = -a ^(4:ℕ) * g * w ^(3:ℕ) + 2 * a ^(4:ℕ) * u ^(2:ℕ) * v - a ^(4:ℕ) * u * v * w - a ^(4:ℕ) * u * w
        - 2 * a ^(4:ℕ) * v ^(3:ℕ) + 2 * a ^(4:ℕ) * v ^(2:ℕ) + 2 * a ^(4:ℕ) * v * w ^(2:ℕ) - 2 * a ^(4:ℕ) * w ^(2:ℕ)
        + 2 * a ^(3:ℕ) * b * g * w ^(3:ℕ) + a ^(3:ℕ) * b * u ^(2:ℕ) * v + a ^(3:ℕ) * b * u * v * w
        + 2 * a ^(3:ℕ) * b * u * w + 2 * a ^(3:ℕ) * b * v ^(3:ℕ) + a ^(3:ℕ) * b * v ^(2:ℕ)
        + a ^(3:ℕ) * b * v * w ^(2:ℕ) + 2 * a ^(3:ℕ) * b * w ^(2:ℕ) + a ^(2:ℕ) * b ^(2:ℕ) * g * w ^(3:ℕ)
        - 2 * a ^(2:ℕ) * b ^(2:ℕ) * u ^(2:ℕ) * v + a ^(2:ℕ) * b ^(2:ℕ) * u * w - 2 * a ^(2:ℕ) * b ^(2:ℕ) * v ^(2:ℕ)
        - 2 * a ^(2:ℕ) * b ^(2:ℕ) * v * w ^(2:ℕ) - 2 * a * b ^(3:ℕ) * g * w ^(3:ℕ) - a * b ^(3:ℕ) * u ^(2:ℕ) * v
        + a * b ^(3:ℕ) * u * v * w - 2 * a * b ^(3:ℕ) * u * w + 2 * a * b ^(3:ℕ) * v ^(3:ℕ)
        - a * b ^(3:ℕ) * v ^(2:ℕ) - a * b ^(3:ℕ) * v * w ^(2:ℕ) + 2 * a * b ^(3:ℕ) * w ^(2:ℕ) - b ^(4:ℕ) * g * w ^(3:ℕ)
        + 2 * b ^(4:ℕ) * u ^(2:ℕ) * v + b ^(4:ℕ) * u * v * w - b ^(4:ℕ) * u * w + 2 * b ^(4:ℕ) * v ^(3:ℕ)
        + 2 * b ^(4:ℕ) * v ^(2:ℕ) + 2 * b ^(4:ℕ) * v * w ^(2:ℕ) + 2 * b ^(4:ℕ) * w ^(2:ℕ) := by
  simp only [Work.MotAS.zcubAS, Work.MotAS.kleinRAS, Work.MotAS.kleinRAS4]
  simp [Matrix.cons_val', Matrix.of_apply, MvPolynomial.eval_C, MvPolynomial.eval_X] <;> ring

/-- The third base-curve cubic, expanded. -/
theorem eval_zcubAS_three {K : Type*} [Field K] (a b g u v w : K) :
    MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g 3)
      = 2 * a ^(4:ℕ) * g * v * w ^(2:ℕ) - a ^(4:ℕ) * u ^(3:ℕ) - a ^(4:ℕ) * u ^(2:ℕ) * w + a ^(4:ℕ) * u * v ^(2:ℕ)
        - a ^(4:ℕ) * u * v + a ^(4:ℕ) * u * w ^(2:ℕ) - a ^(4:ℕ) * v ^(2:ℕ) * w - a ^(4:ℕ) * v * w + a ^(4:ℕ) * w ^(3:ℕ)
        + 2 * a ^(4:ℕ) * w + a ^(3:ℕ) * b * g * v * w ^(2:ℕ) + 2 * a ^(3:ℕ) * b * u ^(3:ℕ)
        + a ^(3:ℕ) * b * u ^(2:ℕ) * w - a ^(3:ℕ) * b * u * v ^(2:ℕ) + 2 * a ^(3:ℕ) * b * u * v
        - a ^(3:ℕ) * b * u * w ^(2:ℕ) + a ^(3:ℕ) * b * v * w - 2 * a ^(3:ℕ) * b * w ^(3:ℕ) + a ^(3:ℕ) * b * w
        - 2 * a ^(2:ℕ) * b ^(2:ℕ) * g * v * w ^(2:ℕ) + a ^(2:ℕ) * b ^(2:ℕ) * u ^(3:ℕ) + a ^(2:ℕ) * b ^(2:ℕ) * u * v
        - 2 * a ^(2:ℕ) * b ^(2:ℕ) * u * w ^(2:ℕ) - 2 * a ^(2:ℕ) * b ^(2:ℕ) * v ^(2:ℕ) * w - 2 * a ^(2:ℕ) * b ^(2:ℕ) * w
        - a * b ^(3:ℕ) * g * v * w ^(2:ℕ) - 2 * a * b ^(3:ℕ) * u ^(3:ℕ) + a * b ^(3:ℕ) * u ^(2:ℕ) * w
        - a * b ^(3:ℕ) * u * v ^(2:ℕ) - 2 * a * b ^(3:ℕ) * u * v + a * b ^(3:ℕ) * u * w ^(2:ℕ)
        + a * b ^(3:ℕ) * v * w - 2 * a * b ^(3:ℕ) * w ^(3:ℕ) - a * b ^(3:ℕ) * w + 2 * b ^(4:ℕ) * g * v * w ^(2:ℕ)
        - b ^(4:ℕ) * u ^(3:ℕ) + b ^(4:ℕ) * u ^(2:ℕ) * w - b ^(4:ℕ) * u * v ^(2:ℕ) - b ^(4:ℕ) * u * v + b ^(4:ℕ) * u * w ^(2:ℕ)
        - b ^(4:ℕ) * v ^(2:ℕ) * w + b ^(4:ℕ) * v * w - b ^(4:ℕ) * w ^(3:ℕ) + 2 * b ^(4:ℕ) * w := by
  simp only [Work.MotAS.zcubAS, Work.MotAS.kleinRAS, Work.MotAS.kleinRAS3]
  simp [Matrix.cons_val', Matrix.of_apply, MvPolynomial.eval_C, MvPolynomial.eval_X] <;> ring

/-! ## The annihilation lemmas -/

/-- `kbRv` evaluated at a base point is killed by the AS ruling matrix. -/
theorem AmatAS_mulVec_kbRv_zero {K : Type*} [Field K] [CharP K 5] (a b g u v w : K)
    (hA : 2 * a - b ≠ 0)
    (h4 : MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g 4) = 0) :
    Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0]) (rvEv a b g u v w) = 0 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  funext i
  fin_cases i
  · rw [AmatAS_chartPt_eq]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [rvEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq] <;> ring
  · rw [AmatAS_chartPt_eq]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [rvEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq] <;> ring
  · rw [AmatAS_chartPt_eq]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [rvEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq] <;> ring
  · rw [AmatAS_chartPt_eq]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [rvEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq] <;> ring
  · have hkey : (2 * a - b) * ((Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0])
        (rvEv a b g u v w)) 4)
        = 2 * MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g 4) := by
      rw [AmatAS_chartPt_eq, eval_zcubAS_four]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      simp [rvEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, Matrix.empty_eq]
      linear_combination (norm := refl_ring1) (2 * a ^(4:ℕ) * g * w ^(3:ℕ) + 4 * a ^(4:ℕ) * v ^(3:ℕ) - 4 * a ^(4:ℕ) * v ^(2:ℕ)
        - 2 * a ^(4:ℕ) * v * w ^(2:ℕ) - 2 * a ^(4:ℕ) * w ^(2:ℕ) + 2 * a ^(3:ℕ) * b * u ^(2:ℕ) * v
        - a ^(3:ℕ) * b * u * v * w - 3 * a ^(3:ℕ) * b * u * w - 4 * a ^(3:ℕ) * b * v ^(3:ℕ)
        + 6 * a ^(3:ℕ) * b * v ^(2:ℕ) - 7 * a ^(3:ℕ) * b * v * w ^(2:ℕ) + 3 * a ^(3:ℕ) * b * w ^(2:ℕ)
        - 4 * a ^(2:ℕ) * b ^(2:ℕ) * g * w ^(3:ℕ) + a ^(2:ℕ) * b ^(2:ℕ) * u ^(2:ℕ) * v + 2 * a ^(2:ℕ) * b ^(2:ℕ) * u * v * w
        - 4 * a ^(2:ℕ) * b ^(2:ℕ) * u * w - 4 * a ^(2:ℕ) * b ^(2:ℕ) * v ^(2:ℕ) + 8 * a ^(2:ℕ) * b ^(2:ℕ) * v * w ^(2:ℕ)
        - 6 * a ^(2:ℕ) * b ^(2:ℕ) * w ^(2:ℕ) + 3 * a * b ^(3:ℕ) * g * w ^(3:ℕ) - 2 * a * b ^(3:ℕ) * u ^(2:ℕ) * v
        + 2 * a * b ^(3:ℕ) * u * v * w + 2 * a * b ^(3:ℕ) * v ^(2:ℕ) + a * b ^(3:ℕ) * v * w ^(2:ℕ)
        - 2 * b ^(4:ℕ) * u * v * w + 2 * b ^(4:ℕ) * u * w - b ^(4:ℕ) * v ^(3:ℕ) - b ^(4:ℕ) * v ^(2:ℕ)
        - 2 * b ^(4:ℕ) * v * w ^(2:ℕ)) * h5
    rw [h4, mul_zero] at hkey
    simpa using (mul_eq_zero.mp hkey).resolve_left hA

/-- `kbRw` evaluated at a base point is killed by the AS ruling matrix. -/
theorem AmatAS_mulVec_kbRw_zero {K : Type*} [Field K] [CharP K 5] (a b g u v w : K)
    (h3 : MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g 3) = 0) :
    Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0]) (rwEv a b g u v w) = 0 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  funext i
  fin_cases i
  · rw [AmatAS_chartPt_eq]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [rwEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq] <;> ring
  · rw [AmatAS_chartPt_eq]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [rwEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq] <;> ring
  · rw [AmatAS_chartPt_eq]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [rwEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq] <;> ring
  · rw [AmatAS_chartPt_eq]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [rwEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq] <;> ring
  · have hkey : ((Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0]) (rwEv a b g u v w)) 4)
        = - MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g 3) := by
      rw [AmatAS_chartPt_eq, eval_zcubAS_three]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      simp [rwEv, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, Matrix.empty_eq]
      linear_combination (norm := refl_ring1) (-a ^(4:ℕ) * u ^(3:ℕ) - a ^(4:ℕ) * u ^(2:ℕ) * w - 3 * a ^(4:ℕ) * u * v ^(2:ℕ)
        + 3 * a ^(4:ℕ) * u * v + 2 * a ^(4:ℕ) * u * w ^(2:ℕ) - 5 * a ^(4:ℕ) * v ^(2:ℕ) * w + 3 * a ^(4:ℕ) * v * w
        + 2 * a ^(4:ℕ) * w ^(3:ℕ) + 2 * a ^(4:ℕ) * w - 2 * a ^(3:ℕ) * b * g * v * w ^(2:ℕ) - 2 * a ^(3:ℕ) * b * u ^(3:ℕ)
        - 5 * a ^(3:ℕ) * b * u ^(2:ℕ) * w + 3 * a ^(3:ℕ) * b * u * v ^(2:ℕ) - 6 * a ^(3:ℕ) * b * u * v
        + 3 * a ^(3:ℕ) * b * u * w ^(2:ℕ) - 4 * a ^(3:ℕ) * b * v ^(2:ℕ) * w - 3 * a ^(3:ℕ) * b * v * w
        + 5 * a ^(3:ℕ) * b * w ^(3:ℕ) + a ^(3:ℕ) * b * w - 4 * a ^(2:ℕ) * b ^(2:ℕ) * g * v * w ^(2:ℕ)
        - 11 * a ^(2:ℕ) * b ^(2:ℕ) * u ^(2:ℕ) * w + 5 * a ^(2:ℕ) * b ^(2:ℕ) * u * v - 4 * a ^(2:ℕ) * b ^(2:ℕ) * u * w ^(2:ℕ)
        + 3 * a ^(2:ℕ) * b ^(2:ℕ) * w ^(3:ℕ) - 4 * a ^(2:ℕ) * b ^(2:ℕ) * w - a * b ^(3:ℕ) * g * v * w ^(2:ℕ)
        + 2 * a * b ^(3:ℕ) * u ^(3:ℕ) - 7 * a * b ^(3:ℕ) * u ^(2:ℕ) * w - a * b ^(3:ℕ) * u * v ^(2:ℕ)
        - 2 * a * b ^(3:ℕ) * u * v - 4 * a * b ^(3:ℕ) * u * w ^(2:ℕ) + a * b ^(3:ℕ) * v ^(2:ℕ) * w
        + a * b ^(3:ℕ) * v * w - a * b ^(3:ℕ) * w ^(3:ℕ) + 2 * a * b ^(3:ℕ) * w + 2 * b ^(4:ℕ) * g * v * w ^(2:ℕ)
        - b ^(4:ℕ) * u ^(3:ℕ) + b ^(4:ℕ) * u ^(2:ℕ) * w + 3 * b ^(4:ℕ) * u * w ^(2:ℕ) + b ^(4:ℕ) * w ^(3:ℕ)) * h5
    rw [h3, neg_zero] at hkey
    simpa using hkey

/-! ## The kernel computation -/

/-- A kernel vector of the chart ruling matrix with vanishing last two coordinates is zero. -/
theorem AmatAS_kernel_eq_zero {K : Type*} [Field K] (a b g u v w : K)
    (hA : 2 * a - b ≠ 0) (hB : a + 2 * b ≠ 0) (hw : w ≠ 0) (z : Fin 5 → K)
    (hz3 : z 3 = 0) (hz4 : z 4 = 0)
    (hzm : Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0]) z = 0) : z = 0 := by
  have h2 : z 2 = 0 := by
    have h0 := AmatAS_row0 a b g u v w z
    rw [hzm, Pi.zero_apply, hz3, hz4] at h0
    have h0' : -a * w * z 2 - 2 * b * w * z 2 = 0 := by simpa using h0.symm
    have h0'' : (a + 2 * b) * w * z 2 = 0 := by
      have := h0'
      linear_combination (norm := refl_ring1) -this
    exact (mul_eq_zero.mp h0'').resolve_left (mul_ne_zero hB hw)
  have h1 : z 1 = 0 := by
    have h0 := AmatAS_row1 a b g u v w z
    rw [hzm, Pi.zero_apply, h2, hz3, hz4] at h0
    have h0' : a * w * z 1 + 2 * b * w * z 1 = 0 := by simpa using h0.symm
    have h0'' : (a + 2 * b) * w * z 1 = 0 := by
      have := h0'
      linear_combination (norm := refl_ring1) this
    exact (mul_eq_zero.mp h0'').resolve_left (mul_ne_zero hB hw)
  have h0z : z 0 = 0 := by
    have h0 := AmatAS_row2 a b g u v w z
    rw [hzm, Pi.zero_apply, h2, hz3, hz4] at h0
    have h0' : -2 * a * w * z 0 + b * w * z 0 = 0 := by simpa using h0.symm
    have h0'' : (2 * a - b) * w * z 0 = 0 := by
      have := h0'
      linear_combination (norm := refl_ring1) -this
    exact (mul_eq_zero.mp h0'').resolve_left (mul_ne_zero hA hw)
  funext i
  fin_cases i
  · exact h0z
  · exact h1
  · exact h2
  · exact hz3
  · exact hz4

/-- **The AS ruling vectors: the kernel basis of the AS ruling matrix on the residual curve.**
There are two polynomial vectors `rv, rw : Fin 5 → K[X₀,X₁,X₂]` whose evaluations at every base
point `(u,v,w)` of the residual curve `V(ZIAS)` (= the common zeros of the five cubics `zcubAS a b g`)
with `w ≠ 0` span the kernel of the AS ruling matrix `AmatAS a b g ![1,u,v,w,0]` — that kernel is
the ruling line over the base point `(1 : u : v : w : 0) ∈ V(ZIAS)`.  This is the Artin–Schreier
analogue of the T-route's `Work.MotK.TGen.AmatP_ker_iff`; the natural witnesses are the explicitly
defined vectors `Work.MotAS.ASrulV` / `Work.MotAS.ASrulW` (`ASRulingVec.lean`), whose 4th and 5th
slots are `(δ_V, 0)` resp. `(0, δ_W)` with `δ_V = X₂²(2a−b)(a+2b)`, `δ_W = X₂²(a+2b)²(2a−b)`. -/
theorem kernel_basis {K : Type} [Field K] [CharP K 5] (a b g : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : b ≠ 2 * a) (hg : g ≠ 0) :
    ∃ rv rw : Fin 5 → MvPolynomial (Fin 3) K,
      ∀ u v w : K, w ≠ 0 →
        (∀ j : Fin 5, MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g j) = 0) →
        ∀ y : Fin 5 → K,
          Matrix.mulVec (Work.MotAS.ASRul.AmatAS a b g ![1, u, v, w, 0]) y = 0 ↔
            ∃ c d : K, y = c • (fun i => MvPolynomial.eval ![u, v, w] (rv i))
                     + d • (fun i => MvPolynomial.eval ![u, v, w] (rw i)) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hA : 2 * a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hB : a + 2 * b ≠ 0 := by
    intro h
    apply hA
    linear_combination (norm := refl_ring1 (mod := 5)) (-3) * h
  refine ⟨kbRv a b g, kbRw a b g, ?_⟩
  intro u v w hw hbase y
  rw [eval_kbRv a b g u v w, eval_kbRw a b g u v w]
  have hrv := AmatAS_mulVec_kbRv_zero a b g u v w hA (hbase 4)
  have hrw := AmatAS_mulVec_kbRw_zero a b g u v w (hbase 3)
  have hdv : (2 * a - b) * (a + 2 * b) * w ^(2:ℕ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hA hB) (pow_ne_zero 2 hw)
  have hdw : (2 * a - b) * (a + 2 * b) ^(2:ℕ) * w ^(2:ℕ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hA (pow_ne_zero 2 hB)) (pow_ne_zero 2 hw)
  constructor
  · intro hy
    refine ⟨y 3 / ((2 * a - b) * (a + 2 * b) * w ^(2:ℕ)),
      y 4 / ((2 * a - b) * (a + 2 * b) ^(2:ℕ) * w ^(2:ℕ)), ?_⟩
    have hz3 : (y - ((y 3 / ((2 * a - b) * (a + 2 * b) * w ^(2:ℕ))) • rvEv a b g u v w
        + (y 4 / ((2 * a - b) * (a + 2 * b) ^(2:ℕ) * w ^(2:ℕ))) • rwEv a b g u v w)) 3 = 0 := by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, rvEv, rwEv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Fin.isValue,
        div_mul_cancel₀ _ hdv, mul_zero, add_zero, sub_self]
    have hz4 : (y - ((y 3 / ((2 * a - b) * (a + 2 * b) * w ^(2:ℕ))) • rvEv a b g u v w
        + (y 4 / ((2 * a - b) * (a + 2 * b) ^(2:ℕ) * w ^(2:ℕ))) • rwEv a b g u v w)) 4 = 0 := by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, rvEv, rwEv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Fin.isValue,
        div_mul_cancel₀ _ hdw, mul_zero, zero_add, add_zero, sub_self]
    have hzk : Matrix.mulVec (AmatAS a b g ![1, u, v, w, 0])
        (y - ((y 3 / ((2 * a - b) * (a + 2 * b) * w ^(2:ℕ))) • rvEv a b g u v w
          + (y 4 / ((2 * a - b) * (a + 2 * b) ^(2:ℕ) * w ^(2:ℕ))) • rwEv a b g u v w)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hy, hrv,
        hrw]
      simp
    have hzz := AmatAS_kernel_eq_zero a b g u v w hA hB hw
      (y - ((y 3 / ((2 * a - b) * (a + 2 * b) * w ^(2:ℕ))) • rvEv a b g u v w
        + (y 4 / ((2 * a - b) * (a + 2 * b) ^(2:ℕ) * w ^(2:ℕ))) • rwEv a b g u v w))
      hz3 hz4 hzk
    exact sub_eq_zero.mp hzz
  · rintro ⟨c, d, rfl⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hrv, hrw]
    simp

end Work.MotAS.ASRul
