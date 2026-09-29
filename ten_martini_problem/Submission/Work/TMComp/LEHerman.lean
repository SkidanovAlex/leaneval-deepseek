import Mathlib
import Submission.Work.TMComp.LEBridge
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Cocycle.intervalIntegrable_log_frob
import Submission.Work.TMC7Core.Trig

/-!
# `LEHerman` — Herman's bound (component C4, part 1)

`Real.log |λ| ≤ L(E)` for every frequency `α`, coupling `λ` and complex energy `E`
(AJ §9, [H]).  The proof is Herman's subharmonicity (Jensen) trick:

* `z ↦ z^n A_n(z)` is a matrix of *polynomials* in `z` (`Work.TMC7Core.iterPoly`), whose
  value at `z = 0` is `!![(-λ)^n, 0; 0, 0]` (`TMLECore/iterPoly_const_term`), and
  `|(A_n(x))₀₀| = |p_n(e^{2πix})|` (`TMLECore/abs_iterC_eq_iterPoly`);
* Jensen's inequality for polynomials (`TMLECore/jensen_poly`) gives
  `log |p_n(0)| ≤ ∫₀¹ log |p_n(e^{2πix})| dx`;
* `log ‖A₀₀‖ ≤ log ‖A‖_F` for determinant-one matrices, and `lyap` is the infimum of the
  averaged `log ‖A_n‖_F`.

This file proves the assembly from the four Jensen/algebra inputs, which are stated here as
explicit hypotheses so that the assembly is independent of them.
-/

noncomputable section

namespace Work.TMComp

open MeasureTheory

/-- `‖(r : ℂ)‖ = |r|`. -/
theorem norm_ofReal_cast (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- For a determinant-one `2 × 2` matrix, `log ‖A 0 0‖ ≤ log (frob A)`. -/
theorem log_entry_le_log_frob (A : Matrix (Fin 2) (Fin 2) ℂ) (hdet : A.det = 1) :
    Real.log ‖A 0 0‖ ≤ Real.log (Work.TMC7Core.frob A) := by
  have hle : ‖A 0 0‖ ≤ Work.TMC7Core.frob A := Work.TMC7Core.frob_entry A 0 0
  have h2 : Real.sqrt 2 ≤ Work.TMC7Core.frob A :=
    Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one hdet
  have h1 : (1 : ℝ) ≤ Work.TMC7Core.frob A :=
    le_trans (Real.one_le_sqrt.mpr (by norm_num)) h2
  rcases eq_or_lt_of_le (norm_nonneg (A 0 0)) with h | h
  · rw [← h, Real.log_zero]
    exact Real.log_nonneg h1
  · exact Real.log_le_log h hle

/-- **Herman's bound at a single scale**: `n log |λ| ≤ ∫₀¹ log ‖A_n(x)‖_F dx`. -/
theorem integral_log_frob_iterC_ge
    (jensen : ∀ p : Polynomial ℂ, Polynomial.eval 0 p ≠ 0 →
      Real.log ‖Polynomial.eval 0 p‖ ≤
        ∫ x in (0 : ℝ)..1,
          Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) p‖)
    (integ : ∀ p : Polynomial ℂ, IntervalIntegrable
      (fun x : ℝ =>
        Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) p‖)
      volume (0 : ℝ) 1)
    (const_term : ∀ (α lam : ℝ) (E : ℂ) (n : ℕ),
      Polynomial.eval 0 (Work.TMC7Core.iterPoly α lam E n 0 0) = (-(lam : ℂ)) ^ n)
    (abs_eq : ∀ (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ),
      ‖Work.TMC7Core.iterC α lam E n x 0 0‖
        = ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x))
            (Work.TMC7Core.iterPoly α lam E n 0 0)‖)
    (α lam : ℝ) (E : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log |lam|
      ≤ ∫ x in (0 : ℝ)..1,
          Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x)) := by
  rcases eq_or_ne lam 0 with h0 | h0
  · subst h0
    simp only [abs_zero, Real.log_zero, mul_zero]
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro x _
    refine Real.log_nonneg ?_
    have h2 := Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
      (Work.TMC7Core.det_iterC α 0 E n x)
    linarith [Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)]
  · have hp0 : Polynomial.eval 0 (Work.TMC7Core.iterPoly α lam E n 0 0) ≠ 0 := by
      rw [const_term α lam E n]
      exact pow_ne_zero n (neg_ne_zero.mpr (by exact_mod_cast h0))
    have hj := jensen _ hp0
    have hval : Real.log ‖Polynomial.eval 0 (Work.TMC7Core.iterPoly α lam E n 0 0)‖
        = (n : ℝ) * Real.log |lam| := by
      rw [const_term α lam E n, norm_pow, norm_neg, norm_ofReal_cast, Real.log_pow]
    have hstep : Real.log ‖Polynomial.eval 0 (Work.TMC7Core.iterPoly α lam E n 0 0)‖
        ≤ ∫ x in (0 : ℝ)..1, Real.log ‖Work.TMC7Core.iterC α lam E n x 0 0‖ := by
      have hcongr : (∫ x in (0 : ℝ)..1,
            Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x))
              (Work.TMC7Core.iterPoly α lam E n 0 0)‖)
          = ∫ x in (0 : ℝ)..1, Real.log ‖Work.TMC7Core.iterC α lam E n x 0 0‖ := by
        refine intervalIntegral.integral_congr ?_
        intro x _
        dsimp only
        rw [abs_eq α lam E n x]
      rw [← hcongr]
      exact hj
    have hstep2 : (∫ x in (0 : ℝ)..1, Real.log ‖Work.TMC7Core.iterC α lam E n x 0 0‖)
        ≤ ∫ x in (0 : ℝ)..1,
            Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x)) := by
      refine intervalIntegral.integral_mono (by norm_num) ?_ ?_ (fun x => ?_)
      · exact (intervalIntegrable_congr (f := fun x : ℝ =>
            Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x))
              (Work.TMC7Core.iterPoly α lam E n 0 0)‖)
          (g := fun x : ℝ => Real.log ‖Work.TMC7Core.iterC α lam E n x 0 0‖)
          (fun x _ => by dsimp only; rw [abs_eq α lam E n x])).mp (integ _)
      · exact Work.TMC7Core.Cocycle.intervalIntegrable_log_frob α lam E n
      · exact log_entry_le_log_frob _ (Work.TMC7Core.det_iterC α lam E n x)
    rw [← hval]
    exact le_trans hstep hstep2

/-- **Herman's bound** (AJ §9, [H]): `log |λ| ≤ L(E)`, for all `α`, `λ` and complex `E`. -/
theorem herman_of_pieces
    (jensen : ∀ p : Polynomial ℂ, Polynomial.eval 0 p ≠ 0 →
      Real.log ‖Polynomial.eval 0 p‖ ≤
        ∫ x in (0 : ℝ)..1,
          Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) p‖)
    (integ : ∀ p : Polynomial ℂ, IntervalIntegrable
      (fun x : ℝ =>
        Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) p‖)
      volume (0 : ℝ) 1)
    (const_term : ∀ (α lam : ℝ) (E : ℂ) (n : ℕ),
      Polynomial.eval 0 (Work.TMC7Core.iterPoly α lam E n 0 0) = (-(lam : ℂ)) ^ n)
    (abs_eq : ∀ (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ),
      ‖Work.TMC7Core.iterC α lam E n x 0 0‖
        = ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x))
            (Work.TMC7Core.iterPoly α lam E n 0 0)‖)
    (α lam : ℝ) (E : ℂ) :
    Real.log |lam| ≤ Work.TMC7Core.lyap α lam E := by
  rw [Work.TMC7Core.lyap_eq_iInf_lyapAvg]
  refine le_ciInf (fun N => ?_)
  simp only [Work.TMC7Core.lyapAvg]
  rw [le_div_iff₀ (by positivity)]
  have h := integral_log_frob_iterC_ge jensen integ const_term abs_eq α lam E (N + 1)
    (Nat.succ_le_succ (Nat.zero_le N))
  calc Real.log |lam| * ((N + 1 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) * Real.log |lam| := by
        ring
    _ ≤ ∫ x in (0 : ℝ)..1,
          Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E (N + 1) x)) := h

end Work.TMComp
