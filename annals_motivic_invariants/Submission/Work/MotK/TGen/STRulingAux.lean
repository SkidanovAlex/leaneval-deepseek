import Mathlib
import Submission.Work.MotK.TwCensus.STRulingDefs
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.KleinTwLink
import Submission.Work.MotK.TwAmbh
import Submission.Work.MotK.TGen.ChartDefs
import Submission.Work.MotK.TwCensus.Amat_mulVec
import Submission.Work.MotK.TGen.KleinTwFibre_eq_ker
import Submission.Work.MotK.TwCensus.K5Ruling
import Submission.Work.MotK.KleinTwData.map_data
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.STRulingAux` — algebraic helpers for the source-ruling divisor `sT`

This file collects the algebraic facts needed by `Work.MotK.TGen.STRulingDiv`:

* naturality of the twisted Klein data under a ring homomorphism (wrappers around
  `Work.MotK.KleinTwData.map_data`);
* `Zcub_eval_eq`: the five cubic chart equations of the base curve, evaluated at a point;
* the explicit ruling matrix of the chart point (`AmatP_chartPt_eq`);
* the two membership identities `AmatP(chartPt)·rv = h·Pt1·e₀`, `AmatP(chartPt)·rw = h·Pt2·e₀`
  together with the normal forms `Zcub 4 = a·b²·Pt1`, `Zcub 3 = -a·b²·Pt2`, all in *evaluated*
  (field) form so that the divisions in `Pt1/Pt2` and `rv/rw` are handled by `field_simp`;
* `kleinTwQ_ruling` : the ruling point `t·rv + rw` lies on the twisted quadric.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Work.MotK.TGen

open MvPolynomial Matrix

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

/-! ## 1. Naturality wrappers -/

/-- **Naturality of the twisted quadric.** -/
theorem map_kleinTwQ' (f : R →+* S) (a b h : R) (y : Fin 5 → R) :
    f (Work.MotK.kleinTwQ a b h y)
      = Work.MotK.kleinTwQ (f a) (f b) (f h) (fun i => f (y i)) :=
  (Work.MotK.KleinTwData.map_data f a b h).1 y

/-- **Naturality of the polar form.** -/
theorem map_kleinTwBilin' (f : R →+* S) (a b h : R) (u v : Fin 5 → R) :
    f (Work.MotK.kleinTwBilin a b h u v)
      = Work.MotK.kleinTwBilin (f a) (f b) (f h) (fun i => f (u i)) (fun i => f (v i)) :=
  (Work.MotK.KleinTwData.map_data f a b h).2.1 u v

/-- **Naturality of the inverse stereographic projection.** -/
theorem map_kleinTwStereo' (f : R →+* S) (a b h : R) (p v : Fin 5 → R) :
    (fun i => f (Work.MotK.kleinTwStereo a b h p v i))
      = Work.MotK.kleinTwStereo (f a) (f b) (f h) (fun i => f (p i)) (fun i => f (v i)) := by
  funext i
  exact (Work.MotK.KleinTwData.map_data f a b h).2.2.1 p v i

/-- **Naturality of the twisted secant quintic.** -/
theorem map_kleinTwS' (f : R →+* S) (a b h : R) (y : Fin 5 → R) :
    f (Work.MotK.kleinTwS a b h y)
      = Work.MotK.kleinTwS (f a) (f b) (f h) (fun i => f (y i)) :=
  (Work.MotK.KleinTwData.map_data f a b h).2.2.2.1 y

/-- **Naturality of the twisted Pfaffian (quadro) map.** -/
theorem map_kleinTwP' (f : R →+* S) (a b h : R) (y : Fin 5 → R) :
    (fun k => f (Work.MotK.kleinTwP a b h y k))
      = Work.MotK.kleinTwP (f a) (f b) (f h) (fun i => f (y i)) := by
  funext k
  exact (Work.MotK.KleinTwData.map_data f a b h).2.2.2.2.1 y k

/-- **Naturality of the twisted inverse (cubic) map.** -/
theorem map_kleinTwR' (f : R →+* S) (a b h : R) (y : Fin 5 → R) :
    (fun k => f (Work.MotK.kleinTwR a b h y k))
      = Work.MotK.kleinTwR (f a) (f b) (f h) (fun i => f (y i)) := by
  funext k
  exact (Work.MotK.KleinTwData.map_data f a b h).2.2.2.2.2 y k

/-! ## 2. Evaluation of the chart data -/

section Eval

variable {K : Type} [Field K]

/-- The five chart cubics of the base curve, evaluated at `(u,v,w)`, are the components of
`kleinTwR a b h ![0,u,v,w,1]`. -/
theorem Zcub_eval_eq' (a b h u v w : K) (j : Fin 5) :
    MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub a b h j)
      = Work.MotK.kleinTwR a b h ![0, u, v, w, 1] j := by
  rw [Work.MotK.TwCensus.Zcub]
  fin_cases j
  · show MvPolynomial.eval ![u, v, w]
        (Work.MotK.kleinTwR0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (Work.MotK.chart3 K)) = Work.MotK.kleinTwR0 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR0, Work.MotK.chart3, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · show MvPolynomial.eval ![u, v, w]
        (Work.MotK.kleinTwR1 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (Work.MotK.chart3 K)) = Work.MotK.kleinTwR1 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR1, Work.MotK.chart3, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · show MvPolynomial.eval ![u, v, w]
        (Work.MotK.kleinTwR2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (Work.MotK.chart3 K)) = Work.MotK.kleinTwR2 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR2, Work.MotK.chart3, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · show MvPolynomial.eval ![u, v, w]
        (Work.MotK.kleinTwR3 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (Work.MotK.chart3 K)) = Work.MotK.kleinTwR3 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR3, Work.MotK.chart3, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · show MvPolynomial.eval ![u, v, w]
        (Work.MotK.kleinTwR4 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (Work.MotK.chart3 K)) = Work.MotK.kleinTwR4 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR4, Work.MotK.chart3, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

end Eval

/-! ## 3. The explicit ruling matrix -/

section Matrix

variable {K : Type} [Field K]

/-- **The explicit ruling matrix of the chart point** `![0,u,v,w,1]`.  Its rows `1,2,3` are
triangular with pivots `-b, b, a`, which is what makes the kernel computation possible. -/
theorem AmatP_chartPt_eq (a b h u v w : K) :
    Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1]
      = !![0, h * a * u, h * b * v, -(h * b * w), -(h * a);
           -b, 0, 0, h * a * v, h * b * w;
           a * w, b, 0, -(h * a * u), 0;
           -(a * v), 0, a, 0, -(h * b * u);
           b * u, -(b * v), -(a * w), 0, 0] := by
  ext i l
  fin_cases i <;> fin_cases l <;>
  · simp only [Work.MotK.TwCensus.AmatP, Work.MotK.TwCensus.kc, Work.MotK.TwCensus.twW,
      Fin.val_add, Fin.val_mul, Fin.val_sub, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val]
    norm_num

end Matrix

/-! ## 4. The membership identities, in evaluated form -/

section Members

variable {K : Type} [Field K]

/-- **`rv` lies in the kernel of the ruling matrix** (evaluated form). -/
theorem AmatP_eval_rv (a b h u v w : K) (hb : b ≠ 0) :
    Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1])
        (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
      = (fun i : Fin 5 => if i = 0 then
          h * MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Pt1 a b h) else 0) := by
  rw [AmatP_chartPt_eq]
  funext i
  fin_cases i <;>
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [Work.MotK.TwCensus.rv, Work.MotK.TwCensus.Pt1, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero]
    field_simp
    first | refl_ring1 | ring

/-- **`rw` lies in the kernel of the ruling matrix** (evaluated form). -/
theorem AmatP_eval_rw (a b h u v w : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1])
        (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h i))
      = (fun i : Fin 5 => if i = 0 then
          h * MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Pt2 a b h) else 0) := by
  rw [AmatP_chartPt_eq]
  funext i
  fin_cases i <;>
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simp [Work.MotK.TwCensus.rw, Work.MotK.TwCensus.Pt2, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero]
    field_simp
    first | refl_ring1 | ring

/-- `Zcub 4 = a·b²·Pt1`, in evaluated form. -/
theorem Zcub_eval_four (a b h u v w : K) (hb : b ≠ 0) :
    MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub a b h 4)
      = a * b ^ 2 * MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Pt1 a b h) := by
  simp only [Work.MotK.TwCensus.Zcub, Work.MotK.kleinTwR, Work.MotK.kleinTwR4,
    Work.MotK.chart3, Work.MotK.TwCensus.Pt1, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  field_simp
  first | refl_ring1 | ring

/-- `Zcub 3 = -a·b²·Pt2`, in evaluated form. -/
theorem Zcub_eval_three (a b h u v w : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub a b h 3)
      = -(a * b ^ 2) * MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Pt2 a b h) := by
  simp only [Work.MotK.TwCensus.Zcub, Work.MotK.kleinTwR, Work.MotK.kleinTwR3,
    Work.MotK.chart3, Work.MotK.TwCensus.Pt2, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  field_simp
  first | refl_ring1 | ring

/-- **The ruling point `t·rv + rw` lies on the twisted quadric** (evaluated form). -/
theorem kleinTwQ_eval_ruling (a b h t u v w : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Work.MotK.kleinTwQ a b h
        (fun i => t * MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i)
          + MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h i)) = 0 := by
  simp only [Work.MotK.kleinTwQ, Work.MotK.kleinTwP0, Work.MotK.TwCensus.rv,
    Work.MotK.TwCensus.rw, MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.add_apply,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero,
    Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_eq]
  field_simp
  first | refl_ring1 | ring

/-- The evaluated ruling vector `rv`. -/
theorem eval_rv_eq (a b h u v w : K) :
    (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
      = ![h * a / b * v, h * a / b * u - h * a ^ 2 / b ^ 2 * v * w, h * a / b * v ^ 2, 1, 0] := by
  funext i
  fin_cases i <;>
  · simp [Work.MotK.TwCensus.rv, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The evaluated ruling vector `rw`. -/
theorem eval_rw_eq (a b h u v w : K) :
    (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h i))
      = ![h * w, -(h * a / b * w ^ 2), h * v * w + h * b / a * u, 0, 1] := by
  funext i
  fin_cases i <;>
  · simp [Work.MotK.TwCensus.rw, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The rows `1,2,3` of the ruling matrix, as dot products. -/
theorem AmatP_row_one (a b h u v w : K) (z : Fin 5 → K) :
    (Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1]) z) 1
      = -b * z 0 + (h * a * v) * z 3 + (h * b * w) * z 4 := by
  rw [AmatP_chartPt_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_eq] <;> ring

/-- The second of the three triangular rows. -/
theorem AmatP_row_two (a b h u v w : K) (z : Fin 5 → K) :
    (Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1]) z) 2
      = (a * w) * z 0 + b * z 1 - (h * a * u) * z 3 := by
  rw [AmatP_chartPt_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_eq] <;> ring

/-- The third of the three triangular rows. -/
theorem AmatP_row_three (a b h u v w : K) (z : Fin 5 → K) :
    (Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1]) z) 3
      = -(a * v) * z 0 + a * z 2 - (h * b * u) * z 4 := by
  rw [AmatP_chartPt_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_eq]
  first | refl_ring1 | ring

/-- **The kernel of the ruling matrix on the base curve.**  For `a b h ≠ 0` and a point `(u,v,w)`
at which `Zcub a b h 3` and `Zcub a b h 4` vanish, a vector `y` is killed by the ruling matrix
`AmatP a b h ![0,u,v,w,1]` exactly when it is a linear combination of the two ruling vectors `rv`,
`rw` evaluated at `(u,v,w)`. -/
theorem AmatP_ker_iff (a b h u v w : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h3 : MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub a b h 3) = 0)
    (h4 : MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub a b h 4) = 0) :
    ∀ y : Fin 5 → K,
      Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1]) y = 0 ↔
        ∃ c d : K, y = c • (fun i => MvPolynomial.eval ![u, v, w]
            (Work.MotK.TwCensus.rv a b h i))
          + d • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h i)) := by
  have hPt1 : MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Pt1 a b h) = 0 := by
    have hZ := Zcub_eval_four a b h u v w hb
    rw [hZ] at h4
    exact (mul_eq_zero.mp h4).resolve_left (mul_ne_zero ha (pow_ne_zero 2 hb))
  have hPt2 : MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Pt2 a b h) = 0 := by
    have hZ := Zcub_eval_three a b h u v w ha hb
    rw [hZ] at h3
    have h' : (a * b ^ 2) * MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Pt2 a b h) = 0 := by
      simpa using h3
    exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero ha (pow_ne_zero 2 hb))
  have hrveq : (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
      = ![h * a / b * v, h * a / b * u - h * a ^ 2 / b ^ 2 * v * w, h * a / b * v ^ 2, 1,
          0] := eval_rv_eq a b h u v w
  have hrweq : (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h i))
      = ![h * w, -(h * a / b * w ^ 2), h * v * w + h * b / a * u, 0, 1] := eval_rw_eq a b h u v w
  have hmemv : Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1])
      (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i)) = 0 := by
    rw [AmatP_eval_rv a b h u v w hb, hPt1]
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  have hmemw : Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1])
      (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h i)) = 0 := by
    rw [AmatP_eval_rw a b h u v w ha hb, hPt2]
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  intro y
  constructor
  · intro hy
    have hzv : (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w]
          (Work.MotK.TwCensus.rv a b h i))
        - y 4 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h i))) 3 = 0 := by
      simp [hrveq, hrweq, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
    have hzw : (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w]
          (Work.MotK.TwCensus.rv a b h i))
        - y 4 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h i))) 4 = 0 := by
      simp [hrveq, hrweq, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
    have hzker : Matrix.mulVec (Work.MotK.TwCensus.AmatP a b h ![0, u, v, w, 1])
        (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i))) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hy,
        hmemv, hmemw]
      simp
    have h0 : (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i))) 0 = 0 := by
      have hr := AmatP_row_one a b h u v w
        (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i)))
      rw [hzker, Pi.zero_apply, hzv, hzw] at hr
      have h2 : -b * (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w]
            (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i))) 0 = 0 := by simpa using hr
      exact (mul_eq_zero.mp h2).resolve_left (neg_ne_zero.mpr hb)
    have h1 : (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i))) 1 = 0 := by
      have hr := AmatP_row_two a b h u v w
        (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i)))
      rw [hzker, Pi.zero_apply, h0, hzv] at hr
      have h2 : b * (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w]
            (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i))) 1 = 0 := by simpa using hr
      exact (mul_eq_zero.mp h2).resolve_left hb
    have h2 : (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i))) 2 = 0 := by
      have hr := AmatP_row_three a b h u v w
        (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i)))
      rw [hzker, Pi.zero_apply, h0, hzw] at hr
      have h3' : a * (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w]
            (Work.MotK.TwCensus.rv a b h i))
          - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i))) 2 = 0 := by simpa using hr
      exact (mul_eq_zero.mp h3').resolve_left ha
    have hz0 : y - y 3 • (fun i => MvPolynomial.eval ![u, v, w]
          (Work.MotK.TwCensus.rv a b h i))
        - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
            (Work.MotK.TwCensus.rw a b h i)) = 0 := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact hzv
      · exact hzw
    refine ⟨y 3, y 4, ?_⟩
    have hz1 : y - (y 3 • (fun i => MvPolynomial.eval ![u, v, w]
            (Work.MotK.TwCensus.rv a b h i))
          + y 4 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw a b h i))) = 0 := by
      rw [show y - (y 3 • (fun i => MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rv a b h i))
            + y 4 • (fun i => MvPolynomial.eval ![u, v, w]
                (Work.MotK.TwCensus.rw a b h i)))
          = (y - y 3 • (fun i => MvPolynomial.eval ![u, v, w]
                (Work.MotK.TwCensus.rv a b h i))
              - y 4 • (fun i => MvPolynomial.eval ![u, v, w]
                  (Work.MotK.TwCensus.rw a b h i))) from by abel]
      exact hz0
    exact sub_eq_zero.mp hz1
  · rintro ⟨c, d, hy'⟩
    rw [hy', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hmemv, hmemw]
    simp

/-- **Linearity of the ruling matrix in the base point.** -/
theorem AmatP_smul_right {R : Type*} [CommRing R] (a b h c : R) (y : Fin 5 → R) :
    Work.MotK.TwCensus.AmatP a b h (c • y) = c • Work.MotK.TwCensus.AmatP a b h y := by
  ext i l
  simp only [Work.MotK.TwCensus.AmatP, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  first | refl_ring1 | ring

/-- The index `Fin 3 → Fin 5` given by `j ↦ j + 1`. -/
def ch3' {K : Type*} [Field K] (j : Fin 3) : Fin 5 := ⟨j.val + 1, by omega⟩

/-- The first ruling vector, projected to the chart `z₄ = 1`, as a polynomial in the base point. -/
noncomputable def RVS (a b h : K) (i : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotK.TwCensus.rv a b h i
    - MvPolynomial.C (Work.MotK.kleinPointT a b h i) * Work.MotK.TwCensus.rv a b h 0

/-- The second ruling vector, projected to the chart `z₄ = 1`. -/
noncomputable def RWS (a b h : K) (i : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotK.TwCensus.rw a b h i
    - MvPolynomial.C (Work.MotK.kleinPointT a b h i) * Work.MotK.TwCensus.rw a b h 0

/-- The `3`rd component of the evaluated ruling vector `rv` is `1`. -/
theorem eval_rv_three (a b h u v w : K) :
    MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h 3) = 1 := by
  simp [Work.MotK.TwCensus.rv, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The `4`th component of the evaluated ruling vector `rv` is `0`. -/
theorem eval_rv_four (a b h u v w : K) :
    MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv a b h 4) = 0 := by
  simp [Work.MotK.TwCensus.rv]

/-- The `3`rd component of the evaluated ruling vector `rw` is `0`. -/
theorem eval_rw_three (a b h u v w : K) :
    MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h 3) = 0 := by
  simp [Work.MotK.TwCensus.rw]

/-- The `4`th component of the evaluated ruling vector `rw` is `1`. -/
theorem eval_rw_four (a b h u v w : K) :
    MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw a b h 4) = 1 := by
  simp [Work.MotK.TwCensus.rw, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- **`AmatP` and `Amat` agree.**  The closed form `AmatP` of the ruling matrix is the same
matrix as the row-wise definition `Amat`. -/
theorem AmatP_eq_Amat' {K : Type} [Field K] (a b h : K) (c' : Fin 5 → K) :
    Work.MotK.TwCensus.AmatP a b h c' = Work.MotK.TwCensus.Amat a b h c' := by
  ext i l
  show h ^ Work.MotK.TwCensus.twW i (l - i) * Work.MotK.TwCensus.kc a b (l - 2 * i)
      * c' (l - i)
    = h ^ Work.MotK.TwCensus.twW i (l - i)
        * Work.MotK.kleinM a b (Pi.single l (1 : K)) i (l - i) * c' (l - i)
  rw [Work.MotK.TwCensus.kleinM_eq]
  have h1 : i + (l - i) = l := by simp
  rw [h1, Pi.single_eq_same, mul_one]
  have h2 : l - 2 * i = l - i - i := by fin_cases i <;> fin_cases l <;> decide
  rw [h2]
  rfl

end Members

end Work.MotK.TGen
