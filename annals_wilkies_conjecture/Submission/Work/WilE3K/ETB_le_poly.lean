import Mathlib
import Submission.Work.WilE3K.Elim

namespace Work.WilE3K

noncomputable section

/-- One elimination-step substitution on polynomials: `p ↦ p.comp (c·X + 11·c)`, chosen so that
`(step c p).eval D = p.eval (c * (D + 11))`.  Iterating it `rt` times turns the single-argument
degree growth of the `ETB` recursion into a genuine polynomial in `D`. -/
private def step (F : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  p.comp (Polynomial.C (F + 9) * Polynomial.X + Polynomial.C ((F + 9) * 11))

private lemma step_eval (F : ℕ) (p : Polynomial ℕ) (D : ℕ) :
    (step F p).eval D = p.eval ((F + 9) * (D + 11)) := by
  rw [step, Polynomial.eval_comp]
  congr 1
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- Evaluation at a natural number is monotone for polynomials with coefficients in `ℕ`. -/
private lemma eval_mono_nat (p : Polynomial ℕ) : Monotone (fun x => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    intro x y hxy
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left hxy n)

/-- The recursion bound `ETB q rt N D` is dominated by the `rt`-fold iterate of the step
substitution, uniformly in `N` as long as `N + 1 + rt ≤ F`. -/
private lemma ETB_le_iterate (q : Polynomial ℕ) (F : ℕ) :
    ∀ rt N D, N + 1 + rt ≤ F →
      Work.WilE3K.ETB q rt N D ≤ ((step F)^[rt] q).eval D := by
  intro rt
  induction rt with
  | zero => intro N D _; simp [ETB]
  | succ rt ih =>
    intro N D h
    have h' : N + 1 + 1 + rt ≤ F := by omega
    have h1 : Work.WilE3K.ETB q rt (N + 1) ((N + 9) * (D + 11))
        ≤ ((step F)^[rt] q).eval ((N + 9) * (D + 11)) := ih (N + 1) _ h'
    have hle : (N + 9) * (D + 11) ≤ (F + 9) * (D + 11) :=
      Nat.mul_le_mul_right (D + 11) (by omega)
    have h2 := (eval_mono_nat ((step F)^[rt] q)) hle
    have h3 : ((step F)^[rt] q).eval ((F + 9) * (D + 11)) = ((step F)^[rt + 1] q).eval D := by
      simp only [Function.iterate_succ_apply', step_eval]
    calc Work.WilE3K.ETB q (rt + 1) N D
        = Work.WilE3K.ETB q rt (N + 1) ((N + 9) * (D + 11)) := by
          simp only [ETB]
      _ ≤ ((step F)^[rt] q).eval ((N + 9) * (D + 11)) := h1
      _ ≤ ((step F)^[rt] q).eval ((F + 9) * (D + 11)) := h2
      _ = ((step F)^[rt + 1] q).eval D := h3

theorem ETB_le_poly (q : Polynomial ℕ) (F : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (rt N D : ℕ), N + 1 + rt ≤ F →
      Work.WilE3K.ETB q rt N D ≤ p.eval D := by
  refine ⟨∑ i ∈ Finset.range F, (step F)^[i] q, ?_⟩
  intro rt N D h
  have hrt : rt ∈ Finset.range F := Finset.mem_range.mpr (by omega)
  have hb := ETB_le_iterate q F rt N D h
  have hle : ((step F)^[rt] q).eval D
      ≤ (∑ i ∈ Finset.range F, (step F)^[i] q).eval D := by
    rw [Polynomial.eval_finsetSum (Finset.range F) (fun i => (step F)^[i] q) D]
    exact Finset.single_le_sum (s := Finset.range F)
      (f := fun i => ((step F)^[i] q).eval D) (fun i _ => Nat.zero_le _) hrt
  exact le_trans hb hle

end

end Work.WilE3K
