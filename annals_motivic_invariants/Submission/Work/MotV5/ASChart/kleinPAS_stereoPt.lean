import Mathlib
import Submission.Work.MotAS.ASLink
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotV5.ASChart.Stereo
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `kleinPAS` at the AS stereographic point

The stereographic point `stereoPt w := (asM w)† · e₀` of the AS (characteristic-5) chart is the
image under the Galois-coordinate substitution `x = asM w · y` of the *split* stereographic point
`288 • e₀ = (288, …, 288)`.  Hence the twisted Pfaffians at `stereoPt w` are obtained by pushing
the split Pfaffians at `288 • e₀` back through the transport identity `asTransportP` and
cancelling the invertible Vandermonde matrix `asN w`.

The two polynomial inputs are therefore purely about the split model:

* `kleinP a b` is homogeneous of degree two (`kleinP_smul_vec`);
* at the all-ones vector all five split Pfaffians equal `a² − ab − b²` (`kleinP_ones`),
  so at `288 • e₀` they all equal `288² (a²−ab−b²) = −(a²−ab−b²)` because `288² + 1 = 5 · 16589`.

Since the transport `asN w` only sees the `j = 0` coordinate of the answer
(`asN_mulVec_single`), the resulting twisted vector is `(−(a²−ab−b²), 0, 0, 0, 0)`, as needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotV5.ASChart

open Work.MotAS

variable {R : Type*} [CommRing R]

/-- The split Pfaffian vector `kleinP a b` is homogeneous of degree two. -/
theorem kleinP_smul_vec (a b c : R) (x : Fin 5 → R) :
    Work.MotK.kleinP a b (c • x) = c ^ 2 • Work.MotK.kleinP a b x := by
  funext k
  fin_cases k
  · show Work.MotK.kleinP0 a b (c • x) = c ^ 2 * Work.MotK.kleinP0 a b x
    simp only [Work.MotK.kleinP0, Pi.smul_apply, smul_eq_mul]; ring
  · show Work.MotK.kleinP1 a b (c • x) = c ^ 2 * Work.MotK.kleinP1 a b x
    simp only [Work.MotK.kleinP1, Pi.smul_apply, smul_eq_mul]; ring
  · show Work.MotK.kleinP2 a b (c • x) = c ^ 2 * Work.MotK.kleinP2 a b x
    simp only [Work.MotK.kleinP2, Pi.smul_apply, smul_eq_mul]; ring
  · show Work.MotK.kleinP3 a b (c • x) = c ^ 2 * Work.MotK.kleinP3 a b x
    simp only [Work.MotK.kleinP3, Pi.smul_apply, smul_eq_mul]; ring
  · show Work.MotK.kleinP4 a b (c • x) = c ^ 2 * Work.MotK.kleinP4 a b x
    simp only [Work.MotK.kleinP4, Pi.smul_apply, smul_eq_mul]; ring

/-- All five split Pfaffians take the value `a² − ab − b²` at the all-ones vector. -/
theorem kleinP_ones (a b : R) :
    Work.MotK.kleinP a b (onesVec : Fin 5 → R) = fun _ => a ^ 2 - a * b - b ^ 2 := by
  funext k
  fin_cases k
  · show Work.MotK.kleinP0 a b (onesVec : Fin 5 → R) = a ^ 2 - a * b - b ^ 2
    simp only [Work.MotK.kleinP0, onesVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]; ring
  · show Work.MotK.kleinP1 a b (onesVec : Fin 5 → R) = a ^ 2 - a * b - b ^ 2
    simp only [Work.MotK.kleinP1, onesVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]; ring
  · show Work.MotK.kleinP2 a b (onesVec : Fin 5 → R) = a ^ 2 - a * b - b ^ 2
    simp only [Work.MotK.kleinP2, onesVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]; ring
  · show Work.MotK.kleinP3 a b (onesVec : Fin 5 → R) = a ^ 2 - a * b - b ^ 2
    simp only [Work.MotK.kleinP3, onesVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]; ring
  · show Work.MotK.kleinP4 a b (onesVec : Fin 5 → R) = a ^ 2 - a * b - b ^ 2
    simp only [Work.MotK.kleinP4, onesVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]; ring

/-- The matrix `asN w` reads off only the zeroth coordinate: its columns `1, (w+2k), (w+2k)², …`
multiply the vector `(c, 0, 0, 0, 0)` to the constant vector `(c, …, c)`. -/
theorem asN_mulVec_single (w c : R) :
    (asN w).mulVec (fun j : Fin 5 => if j = 0 then c else 0) = fun _ => c := by
  funext i
  simp only [Matrix.mulVec, dotProduct, asN, Matrix.of_apply, Fin.sum_univ_five]
  simp +decide

theorem kleinPAS_stereoPt {R : Type*} [CommRing R] (a b g w : R) (h5 : (5 : R) = 0)
    (hw : w ^ 5 = w + g) (k : Fin 5) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.stereoPt w) k
      = if k = 0 then -(a ^ 2 - a * b - b ^ 2) else 0 := by
  -- `288² = −1` in characteristic `5`, since `288² + 1 = 5 · 16589`.
  have h288 : (288 : R) ^ 2 = -(1 : R) := by
    have h : ((288 : R) ^ 2 + 1) = 0 := by
      have hcast : ((288 : R) ^ 2 + 1) = ((5 : R) * 16589) := by ring
      rw [hcast, h5, zero_mul]
    linear_combination (norm := first | refl_ring1 | ring1) h
  -- the split Pfaffians at `288 • e₀` are all `−(a² − ab − b²)`
  have hP : Work.MotK.kleinP a b ((288 : R) • (onesVec : Fin 5 → R))
      = fun _ => -(a ^ 2 - a * b - b ^ 2) := by
    rw [kleinP_smul_vec, kleinP_ones]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h288, neg_one_mul]
  -- the split Pfaffians at the transported source point
  have hleft : Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * (stereoPt w) j)
      = fun _ => -(a ^ 2 - a * b - b ^ 2) := by
    have hstep : (fun i => ∑ j, asM w i j * (stereoPt w) j)
        = (288 : R) • (onesVec : Fin 5 → R) := asM_mulVec_stereoPt w
    rw [hstep]; exact hP
  -- transport `asTransportP` and cancel the invertible `asN w`
  have hT := asTransportP a b g w h5 hw (stereoPt w)
  have hX : (asN w).mulVec (kleinPAS a b g (stereoPt w))
      = (asN w).mulVec (fun j : Fin 5 => if j = 0 then -(a ^ 2 - a * b - b ^ 2) else 0) := by
    rw [← hT, hleft, asN_mulVec_single]
  have heq : kleinPAS a b g (stereoPt w)
      = fun j : Fin 5 => if j = 0 then -(a ^ 2 - a * b - b ^ 2) else 0 :=
    asN_mulVec_injective h5 w hX
  exact congrFun heq k

end Work.MotV5.ASChart
