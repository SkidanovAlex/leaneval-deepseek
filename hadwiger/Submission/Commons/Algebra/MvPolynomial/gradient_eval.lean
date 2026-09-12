import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic

noncomputable section

namespace Commons.Algebra.MvPolynomial

/-- Candidate for the Fréchet derivative of the polynomial function
`y ↦ MvPolynomial.eval (fun i => y i) P` at `x`, written as an element of the dual. -/
private def evalDeriv {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
  ∑ i : Fin n, MvPolynomial.eval (fun j => x j) (MvPolynomial.pderiv i P) • EuclideanSpace.proj i

private lemma evalDeriv_add {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    evalDeriv (P + Q) x = evalDeriv P x + evalDeriv Q x := by
  simp only [evalDeriv, map_add, add_smul, Finset.sum_add_distrib]

private lemma evalDeriv_C {n : ℕ} (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    evalDeriv (MvPolynomial.C a) x = 0 := by
  simp only [evalDeriv, MvPolynomial.pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]

private lemma evalDeriv_X {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    evalDeriv (MvPolynomial.X i) x = EuclideanSpace.proj i := by
  simp only [evalDeriv, MvPolynomial.pderiv_X]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma evalDeriv_mul {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    evalDeriv (P * Q) x = MvPolynomial.eval (fun j => x j) Q • evalDeriv P x
      + MvPolynomial.eval (fun j => x j) P • evalDeriv Q x := by
  ext v
  simp only [evalDeriv, sum_apply, smul_apply, add_apply, smul_eq_mul, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.pderiv_mul, EuclideanSpace.proj, PiLp.proj_apply,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `Good x P` records that the polynomial function of `P` is differentiable at `x`
with derivative `evalDeriv P x`.  It is a `def` so that the instance arguments occurring in
the `HasFDerivAt` statement are fixed once and for all -- the type `EuclideanSpace ℝ (Fin n)`
carries several (definitionally distinct) instance paths, so re-elaborating the statement
in goals and hypotheses separately would produce mismatches. -/
private def Good {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (P : MvPolynomial (Fin n) ℝ) : Prop :=
  HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
    (evalDeriv P x) x

private lemma Good.C {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    Good x (MvPolynomial.C a) := by
  unfold Good
  rw [evalDeriv_C]
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => y i) (MvPolynomial.C a)) = fun _ : EuclideanSpace ℝ (Fin n) => a := by
    ext y; exact MvPolynomial.eval_C a
  rw [hfun]
  exact hasFDerivAt_const a x

private lemma Good.X {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    Good x (MvPolynomial.X i) := by
  unfold Good
  rw [evalDeriv_X]
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => y i) (MvPolynomial.X i))
      = ⇑(EuclideanSpace.proj (𝕜 := ℝ) i) := by
    ext y; simp only [MvPolynomial.eval_X, EuclideanSpace.coe_proj]
  rw [hfun]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)

private lemma Good.add {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} {P Q : MvPolynomial (Fin n) ℝ}
    (hP : Good x P) (hQ : Good x Q) : Good x (P + Q) := by
  unfold Good at hP hQ ⊢
  rw [evalDeriv_add]
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) (P + Q))
      = (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
        + (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) Q) := by
    ext y; exact MvPolynomial.eval_add
  rw [hfun]
  exact hP.add hQ

private lemma Good.mul {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} {P Q : MvPolynomial (Fin n) ℝ}
    (hP : Good x P) (hQ : Good x Q) : Good x (P * Q) := by
  unfold Good at hP hQ ⊢
  rw [evalDeriv_mul]
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) (P * Q))
      = (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) Q)
        * (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) := by
    ext y
    simp only [Pi.mul_apply, MvPolynomial.eval_mul]
    ring
  rw [hfun]
  exact hQ.mul hP

private lemma good_of {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (P : MvPolynomial (Fin n) ℝ) :
    Good x P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact Good.C x a
  | add P Q hP hQ => exact Good.add hP hQ
  | mul_X P i hP => exact Good.mul hP (Good.X x i)

private lemma toDual_single {n : ℕ} (i : Fin n) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        (EuclideanSpace.single i (1 : ℝ)) = EuclideanSpace.proj i := by
  ext v
  rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simp

private lemma toDual_sum_single {n : ℕ} (c : Fin n → ℝ) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        (∑ i : Fin n, c i • EuclideanSpace.single i (1 : ℝ))
      = ∑ i : Fin n, c i • EuclideanSpace.proj i := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, toDual_single]

theorem gradient_eval
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (𝕜 := ℝ) (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x =
      ∑ i : Fin n, MvPolynomial.eval (fun j => x j) (MvPolynomial.pderiv i P) • EuclideanSpace.single i 1 := by
  have h : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
      (evalDeriv P x) x := good_of x P
  have hg : HasGradientAt
      (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
      (∑ i : Fin n, MvPolynomial.eval (fun j => x j) (MvPolynomial.pderiv i P) • EuclideanSpace.single i 1) x := by
    rw [hasGradientAt_iff_hasFDerivAt, toDual_sum_single]
    exact h
  exact hg.gradient

end Commons.Algebra.MvPolynomial