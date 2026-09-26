import Mathlib
import Submission.Work.SG.minVecDefs

namespace Work.SG

/-! ## The norm formula for a superbase

For a symmetric form `Q` and a unimodular `W`, the value `qf Q (W.mulVec y)` of the quadratic form
of `Wᵀ Q W` at `y` can be written in terms of the superbase coordinates `x = cons0 y` as
`∑_{m<n} sQ Q W m n * (x m - x n)^2`, where `sQ Q W m n = - bf Q (sb W m) (sb W n)`.  This is the
algebraic identity underlying the Selling-reduction reduction argument. -/

open scoped Matrix BigOperators

/-- **Superbase quadratic-form identity.** For a symmetric integer matrix `B` on the four superbase
indices whose row sums vanish (`∑ n, B m n = 0`, the reflection of `∑ m, sb W m = 0`), the double
sum `∑ m, ∑ n, x m * x n * B m n` equals the Selling sum `∑_{m<n} (-B m n) * (x m - x n)^2`. -/
lemma quad_superbase (B : Fin 4 → Fin 4 → ℤ) (x : Fin 4 → ℤ)
    (hsym : ∀ m n, B m n = B n m) (hsum : ∀ m, ∑ n, B m n = 0) :
    ∑ m, ∑ n, x m * x n * B m n
      = ∑ p ∈ pairSet, (- B p.1 p.2) * (x p.1 - x p.2) ^ 2 := by
  have h00 : B 0 0 = -(B 0 1 + B 0 2 + B 0 3) := by
    have h := hsum 0; simp only [Fin.sum_univ_four] at h; linarith
  have h11 : B 1 1 = -(B 1 0 + B 1 2 + B 1 3) := by
    have h := hsum 1; simp only [Fin.sum_univ_four] at h; linarith
  have h22 : B 2 2 = -(B 2 0 + B 2 1 + B 2 3) := by
    have h := hsum 2; simp only [Fin.sum_univ_four] at h; linarith
  have h33 : B 3 3 = -(B 3 0 + B 3 1 + B 3 2) := by
    have h := hsum 3; simp only [Fin.sum_univ_four] at h; linarith
  simp only [Fin.sum_univ_four, pairSet_sum, h00, h11, h22, h33,
    hsym 1 0, hsym 2 0, hsym 2 1, hsym 3 0, hsym 3 1, hsym 3 2]
  ring

/-- **The norm formula.** With `x = cons0 y` the superbase coordinates of `y`, the quadratic form
of `Wᵀ Q W` at `y` is `∑_{m<n} sQ Q W m n * (x m - x n)^2`. -/
theorem norm_formula (Q W : IMat) (hsym : Q.transpose = Q) (y : IVec) :
    qf Q (W.mulVec y) = ∑ p ∈ pairSet, sQ Q W p.1 p.2 * (cons0 y p.1 - cons0 y p.2) ^ 2 := by
  set x := cons0 y with hx
  have hmv : W.mulVec y = linComb4 x (sb W) := mulVec_eq_linComb4 W y
  have h1 : qf Q (W.mulVec y) = ∑ m, ∑ n, x m * x n * bf Q (sb W m) (sb W n) := by
    rw [hmv, qf, bf_linComb4]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [bf_comm Q hsym, bf_linComb4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hsumB : ∀ m, ∑ n, bf Q (sb W m) (sb W n) = 0 := by
    intro m
    have hlin : linComb4 (fun _ : Fin 4 => (1 : ℤ)) (sb W) = ∑ n, sb W n := by
      funext k; simp [linComb4]
    have key : ∑ n, bf Q (sb W m) (sb W n) = bf Q (sb W m) (∑ n, sb W n) := by
      rw [← hlin, bf_linComb4]; simp
    rw [key, sb_sum_zero]; simp [bf]
  have h2 : ∑ m, ∑ n, x m * x n * bf Q (sb W m) (sb W n)
      = ∑ p ∈ pairSet, (- bf Q (sb W p.1) (sb W p.2)) * (x p.1 - x p.2) ^ 2 :=
    quad_superbase (fun m n => bf Q (sb W m) (sb W n)) x
      (fun m n => bf_comm Q hsym (sb W m) (sb W n)) hsumB
  rw [h1, h2]
  simp only [sQ]

end Work.SG
