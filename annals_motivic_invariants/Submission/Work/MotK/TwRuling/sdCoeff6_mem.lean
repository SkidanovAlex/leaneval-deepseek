import Mathlib
import Submission.Work.MotK.TwRuling.TwSixCoeffDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Homogeneity of `sdCoeff6`

`sdCoeff6 R a b h j` is the coefficient of `T^j` in `R₀(A + T·B)`, where `A = qA`, `B = qB` are
the two ruling vectors of the twisted Crauder–Katz link (`kleinTwRuleA`, `kleinTwRuleB`) and
`R₀ = kleinTwR0` is the inverse map (a cubic form).  Since `qA k` and `qB k` are quadratic forms
in the variables `X i`, every coefficient of `T^j` is a form of degree `6`.

The proof has two halves.

* `qA_isHomogeneous` / `qB_isHomogeneous`: the two ruling vectors are homogeneous of degree `2`.
  We first record the explicit quadratic forms (`qA_zero … qB_four`), obtained by evaluating the
  polarisation `kleinTwPolarP` at the tangent vector `kleinTwTan · 1` resp. `kleinTwTan · 2`,
  whose components are `-(b²h·c₄)e₀ + 2ab·c₀·e₁` resp. `a²h·c₃·e₀ + 2ab·c₀·e₂`
  (`kleinTwTan_one`, `kleinTwTan_two`).

* `coeffHomog`: the predicate "every `T`-coefficient is homogeneous of degree `d`" on
  `Polynomial (MvPolynomial (Fin 5) R)`; it is stable under `+`, `-`, `*`, `^`, and `C`.  Since
  `z k = C (qA k) + T · C (qB k)` has all coefficients homogeneous of degree `2`, each monomial of
  the cubic `kleinTwR0` has coefficients of degree `6`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.MotK.TwRuling

open MvPolynomial

variable {R : Type*} [CommRing R]

/-! ## The tangent vectors of the twisted quadric -/

theorem kleinTwTan_one (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwTan a b h c 1 = fun i =>
      -(b ^ 2 * h * c 4) * Work.MotK.kleinE 0 i + (2 * a * b * c 0) * Work.MotK.kleinE 1 i := by
  funext i
  fin_cases i <;>
    simp only [Work.MotK.kleinTwTan, Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ,
      Work.MotK.kleinTwP0, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply] <;>
    norm_num <;>
    first | refl_ring1 | ring

theorem kleinTwTan_two (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwTan a b h c 2 = fun i =>
      (a ^ 2 * h * c 3) * Work.MotK.kleinE 0 i + (2 * a * b * c 0) * Work.MotK.kleinE 2 i := by
  funext i
  fin_cases i <;>
    simp only [Work.MotK.kleinTwTan, Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ,
      Work.MotK.kleinTwP0, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply] <;>
    norm_num <;>
    first | refl_ring1 | ring

/-! ## The explicit quadratic forms -/

theorem qA_zero (a b h : R) : qA R a b h 0 = 0 := by
  simp only [qA]
  simp only [Work.MotK.kleinTwRuleA, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_one]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero,
    Work.MotK.kleinTwP0, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qA_one (a b h : R) :
    qA R a b h 1 =
      -((C (a ^ 2 * b ^ 2 * h)) * (X 4) ^ 2) - ((2 * C (a * b ^ 3)) * ((X 0) * (X 3))) := by
  simp only [qA]
  simp only [Work.MotK.kleinTwRuleA, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_one]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero, Matrix.cons_val_one,
    Work.MotK.kleinTwP1, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qA_two (a b h : R) :
    qA R a b h 2 =
      ((2 * C (a ^ 3 * b)) * ((X 0) * (X 2))) + ((C (b ^ 4 * h)) * ((X 3) * (X 4))) := by
  simp only [qA]
  simp only [Work.MotK.kleinTwRuleA, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_one]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Work.MotK.kleinTwP2, Work.MotK.kleinE, Pi.single_apply,
    Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qA_three (a b h : R) :
    qA R a b h 3 =
      -((4 * C (a ^ 2 * b ^ 2)) * ((X 0) * (X 1))) + ((C (b ^ 4 * h)) * ((X 2) * (X 4))) := by
  simp only [qA]
  simp only [Work.MotK.kleinTwRuleA, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_one]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Work.MotK.kleinTwP3,
    Work.MotK.kleinE, Pi.single_apply, Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qA_four (a b h : R) :
    qA R a b h 4 =
      ((2 * C (a ^ 3 * b)) * ((X 0) ^ 2)) - ((C (a ^ 2 * b ^ 2 * h)) * ((X 1) * (X 4))) := by
  simp only [qA]
  simp only [Work.MotK.kleinTwRuleA, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_one]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Work.MotK.kleinTwP4, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qB_zero (a b h : R) : qB R a b h 0 = 0 := by
  simp only [qB]
  simp only [Work.MotK.kleinTwRuleB, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_two]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero,
    Work.MotK.kleinTwP0, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qB_one (a b h : R) :
    qB R a b h 1 =
      ((C (a ^ 4 * h)) * ((X 3) * (X 4))) - ((4 * C (a ^ 2 * b ^ 2)) * ((X 0) * (X 2))) := by
  simp only [qB]
  simp only [Work.MotK.kleinTwRuleB, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_two]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero, Matrix.cons_val_one,
    Work.MotK.kleinTwP1, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qB_two (a b h : R) :
    qB R a b h 2 =
      ((2 * C (a ^ 3 * b)) * ((X 0) * (X 1))) - ((C (a ^ 2 * b ^ 2 * h)) * ((X 3) ^ 2)) := by
  simp only [qB]
  simp only [Work.MotK.kleinTwRuleB, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_two]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Work.MotK.kleinTwP2, Work.MotK.kleinE, Pi.single_apply,
    Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qB_three (a b h : R) :
    qB R a b h 3 =
      -((C (a ^ 2 * b ^ 2 * h)) * ((X 2) * (X 3))) - ((2 * C (a * b ^ 3)) * ((X 0) ^ 2)) := by
  simp only [qB]
  simp only [Work.MotK.kleinTwRuleB, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_two]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Work.MotK.kleinTwP3,
    Work.MotK.kleinE, Pi.single_apply, Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

theorem qB_four (a b h : R) :
    qB R a b h 4 =
      ((C (a ^ 4 * h)) * ((X 1) * (X 3))) - ((2 * C (a * b ^ 3 * h)) * ((X 0) * (X 4))) := by
  simp only [qB]
  simp only [Work.MotK.kleinTwRuleB, Work.MotK.kleinTwPolarP]
  rw [kleinTwTan_two]
  simp only [Work.MotK.kleinTwP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Work.MotK.kleinTwP4, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply]
  norm_num
  first | refl_ring1 | ring

/-! ## Homogeneity of the ruling vectors -/

lemma mv_isHomogeneous_natCast (n : ℕ) :
    (((n : ℕ) : MvPolynomial (Fin 5) R)).IsHomogeneous 0 := by
  induction n with
  | zero => simpa using (isHomogeneous_zero (σ := Fin 5) (R := R) 0)
  | succ n ih =>
      rw [Nat.cast_succ]
      exact ih.add (isHomogeneous_one (σ := Fin 5) (R := R))

lemma h0_mvC (r : R) : (MvPolynomial.C r : MvPolynomial (Fin 5) R).IsHomogeneous 0 :=
  isHomogeneous_C (σ := Fin 5) r

lemma h2_mul_Xsq (c : MvPolynomial (Fin 5) R) (hc : c.IsHomogeneous 0) (i : Fin 5) :
    (c * X i ^ 2).IsHomogeneous 2 :=
  hc.mul (isHomogeneous_X_pow i 2)

lemma h2_mul_XX (c : MvPolynomial (Fin 5) R) (hc : c.IsHomogeneous 0) (i j : Fin 5) :
    (c * (X i * X j)).IsHomogeneous 2 :=
  hc.mul ((isHomogeneous_X (R := R) i).mul (isHomogeneous_X (R := R) j))

theorem qA_isHomogeneous (a b h : R) (k : Fin 5) : (qA R a b h k).IsHomogeneous 2 := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    fin_cases k <;> decide
  rcases hk with hk0 | hk1 | hk2 | hk3 | hk4
  · rw [hk0, qA_zero]
    exact isHomogeneous_zero (σ := Fin 5) (R := R) 2
  · rw [hk1, qA_one]
    exact (h2_mul_Xsq (C (a ^ 2 * b ^ 2 * h)) (h0_mvC _) 4).neg.sub
      (h2_mul_XX (2 * C (a * b ^ 3)) ((mv_isHomogeneous_natCast 2).mul (h0_mvC _)) 0 3)
  · rw [hk2, qA_two]
    exact (h2_mul_XX (2 * C (a ^ 3 * b)) ((mv_isHomogeneous_natCast 2).mul (h0_mvC _)) 0 2).add
      (h2_mul_XX (C (b ^ 4 * h)) (h0_mvC _) 3 4)
  · rw [hk3, qA_three]
    exact (h2_mul_XX (4 * C (a ^ 2 * b ^ 2)) ((mv_isHomogeneous_natCast 4).mul (h0_mvC _)) 0 1).neg.add
      (h2_mul_XX (C (b ^ 4 * h)) (h0_mvC _) 2 4)
  · rw [hk4, qA_four]
    exact (h2_mul_Xsq (2 * C (a ^ 3 * b)) ((mv_isHomogeneous_natCast 2).mul (h0_mvC _)) 0).sub
      (h2_mul_XX (C (a ^ 2 * b ^ 2 * h)) (h0_mvC _) 1 4)

theorem qB_isHomogeneous (a b h : R) (k : Fin 5) : (qB R a b h k).IsHomogeneous 2 := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    fin_cases k <;> decide
  rcases hk with hk0 | hk1 | hk2 | hk3 | hk4
  · rw [hk0, qB_zero]
    exact isHomogeneous_zero (σ := Fin 5) (R := R) 2
  · rw [hk1, qB_one]
    exact (h2_mul_XX (C (a ^ 4 * h)) (h0_mvC _) 3 4).sub
      (h2_mul_XX (4 * C (a ^ 2 * b ^ 2)) ((mv_isHomogeneous_natCast 4).mul (h0_mvC _)) 0 2)
  · rw [hk2, qB_two]
    exact (h2_mul_XX (2 * C (a ^ 3 * b)) ((mv_isHomogeneous_natCast 2).mul (h0_mvC _)) 0 1).sub
      (h2_mul_Xsq (C (a ^ 2 * b ^ 2 * h)) (h0_mvC _) 3)
  · rw [hk3, qB_three]
    exact (h2_mul_XX (C (a ^ 2 * b ^ 2 * h)) (h0_mvC _) 2 3).neg.sub
      (h2_mul_Xsq (2 * C (a * b ^ 3)) ((mv_isHomogeneous_natCast 2).mul (h0_mvC _)) 0)
  · rw [hk4, qB_four]
    exact (h2_mul_XX (C (a ^ 4 * h)) (h0_mvC _) 1 3).sub
      (h2_mul_XX (2 * C (a * b ^ 3 * h)) ((mv_isHomogeneous_natCast 2).mul (h0_mvC _)) 0 4)

/-! ## Coefficients of a `T`-polynomial -/

/-- `coeffHomog d P` says that every `T`-coefficient of `P` is a form of degree `d`. -/
def coeffHomog (d : ℕ) (P : Polynomial (MvPolynomial (Fin 5) R)) : Prop :=
  ∀ j, (P.coeff j).IsHomogeneous d

lemma coeffHomog_C {d : ℕ} {r : MvPolynomial (Fin 5) R} (hr : r.IsHomogeneous d) :
    coeffHomog d (Polynomial.C r) := by
  intro j
  rw [Polynomial.coeff_C]
  split_ifs with h
  · exact hr
  · exact isHomogeneous_zero (σ := Fin 5) (R := R) d

lemma coeffHomog_X : coeffHomog (0 : ℕ) (Polynomial.X : Polynomial (MvPolynomial (Fin 5) R)) := by
  intro j
  rw [Polynomial.coeff_X]
  split_ifs with h
  · exact isHomogeneous_one (σ := Fin 5) (R := R)
  · exact isHomogeneous_zero (σ := Fin 5) (R := R) 0

lemma coeffHomog_add {d : ℕ} {P Q : Polynomial (MvPolynomial (Fin 5) R)}
    (hP : coeffHomog d P) (hQ : coeffHomog d Q) : coeffHomog d (P + Q) := fun j => by
  rw [Polynomial.coeff_add]
  exact (hP j).add (hQ j)

lemma coeffHomog_neg {d : ℕ} {P : Polynomial (MvPolynomial (Fin 5) R)}
    (hP : coeffHomog d P) : coeffHomog d (-P) := fun j => by
  rw [Polynomial.coeff_neg]
  exact (hP j).neg

lemma coeffHomog_sub {d : ℕ} {P Q : Polynomial (MvPolynomial (Fin 5) R)}
    (hP : coeffHomog d P) (hQ : coeffHomog d Q) : coeffHomog d (P - Q) := fun j => by
  rw [Polynomial.coeff_sub]
  exact (hP j).sub (hQ j)

lemma coeffHomog_mul {d e : ℕ} {P Q : Polynomial (MvPolynomial (Fin 5) R)}
    (hP : coeffHomog d P) (hQ : coeffHomog e Q) : coeffHomog (d + e) (P * Q) := fun j => by
  rw [Polynomial.coeff_mul]
  apply IsHomogeneous.sum
  intro x _
  exact (hP x.1).mul (hQ x.2)

lemma coeffHomog_pow {d : ℕ} {P : Polynomial (MvPolynomial (Fin 5) R)}
    (hP : coeffHomog d P) (n : ℕ) : coeffHomog (d * n) (P ^ n) := by
  induction n with
  | zero =>
      simpa using coeffHomog_C (d := 0)
        (isHomogeneous_one (σ := Fin 5) (R := R))
  | succ n ih =>
      rw [pow_succ, Nat.mul_succ]
      exact coeffHomog_mul ih hP

/-! ## The degree-6 coefficient forms -/

/-- `coeffHomog` is preserved by the cubic `kleinTwR0`. -/
lemma coeffHomog_kleinTwR0 {A B H : Polynomial (MvPolynomial (Fin 5) R)}
    {Q : Fin 5 → Polynomial (MvPolynomial (Fin 5) R)}
    (hA : coeffHomog 0 A) (hB : coeffHomog 0 B) (hH : coeffHomog 0 H)
    (hQ : ∀ k, coeffHomog 2 (Q k)) :
    coeffHomog 6 (Work.MotK.kleinTwR0 A B H Q) := by
  simp only [Work.MotK.kleinTwR0]
  refine coeffHomog_sub (coeffHomog_sub (coeffHomog_add (coeffHomog_add (coeffHomog_add
    (coeffHomog_sub ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact coeffHomog_mul (coeffHomog_mul (coeffHomog_mul
      (coeffHomog_mul (coeffHomog_neg hA) (coeffHomog_pow hB 3)) hH)
      (coeffHomog_pow (hQ 3) 2)) (hQ 4)
  · exact coeffHomog_mul (coeffHomog_mul (coeffHomog_mul
      (coeffHomog_mul hA (coeffHomog_pow hB 3)) (coeffHomog_pow hH 2)) (hQ 1))
      (coeffHomog_pow (hQ 2) 2)
  · exact coeffHomog_mul (coeffHomog_mul (coeffHomog_pow hA 2) (coeffHomog_pow hB 2))
      (coeffHomog_pow (hQ 0) 3)
  · exact coeffHomog_mul (coeffHomog_mul (coeffHomog_mul
      (coeffHomog_mul (coeffHomog_pow hA 3) hB) hH) (hQ 2)) (coeffHomog_pow (hQ 4) 2)
  · exact coeffHomog_mul (coeffHomog_mul (coeffHomog_mul
      (coeffHomog_mul (coeffHomog_pow hA 3) hB) (coeffHomog_pow hH 2)) (coeffHomog_pow (hQ 1) 2))
      (hQ 3)
  · exact coeffHomog_mul (coeffHomog_mul (coeffHomog_mul
      (coeffHomog_mul (coeffHomog_pow hA 4) hH) (hQ 0)) (hQ 1)) (hQ 4)
  · exact coeffHomog_mul (coeffHomog_mul (coeffHomog_mul
      (coeffHomog_mul (coeffHomog_pow hB 4) hH) (hQ 0)) (hQ 2)) (hQ 3)

theorem sdCoeff6_mem (R : Type*) [CommRing R] (a b h : R) (j : ℕ) :
    Work.MotK.TwRuling.sdCoeff6 R a b h j ∈ MvPolynomial.homogeneousSubmodule (Fin 5) R 6 := by
  rw [MvPolynomial.mem_homogeneousSubmodule, sdCoeff6_eq]
  have hA : coeffHomog 0 (Polynomial.C (MvPolynomial.C a : MvPolynomial (Fin 5) R)) :=
    coeffHomog_C (isHomogeneous_C (σ := Fin 5) a)
  have hB : coeffHomog 0 (Polynomial.C (MvPolynomial.C b : MvPolynomial (Fin 5) R)) :=
    coeffHomog_C (isHomogeneous_C (σ := Fin 5) b)
  have hH : coeffHomog 0 (Polynomial.C (MvPolynomial.C h : MvPolynomial (Fin 5) R)) :=
    coeffHomog_C (isHomogeneous_C (σ := Fin 5) h)
  have hz : ∀ k : Fin 5, coeffHomog 2 (Polynomial.C (qA R a b h k)
      + Polynomial.X * Polynomial.C (qB R a b h k)) := fun k =>
    coeffHomog_add (coeffHomog_C (qA_isHomogeneous a b h k))
      (coeffHomog_mul coeffHomog_X (coeffHomog_C (qB_isHomogeneous a b h k)))
  have hgood : coeffHomog 6 (coeffPoly R a b h) :=
    coeffHomog_kleinTwR0 hA hB hH hz
  exact hgood j

end Work.MotK.TwRuling
