import Mathlib
import Submission.Work.A3.Circle
import Submission.Work.A3.exp_phase_variation_bound

namespace Work.A3

/-- Lipschitz bound for the `β`-phase `φ(x) = e^{-2πiβ Q(x)}` of the transition-arc estimate: on `[0,M]` it is Lipschitz with constant `2π|β| A d M^{d-1}` where `d = Q.natDegree` and `A` is a constant depending only on the coefficients of `Q`, and it has modulus `1`.  Proof: `Commons.Analysis.Polynomial.abs_eval_sub_eval_le` applied to `Qreal Q`, combined with `norm_exp_neg_two_pi_I_mul_sub_le` in `Submission/Work/A3/exp_phase_variation_bound.lean` (or the corresponding `expTwoPiI` version in `Commons.Analysis.ExponentialSums.quadratic_major_arc_approx`). -/
lemma transitionPhaseLipschitz (Q : Polynomial ℤ) (hd : 1 ≤ Polynomial.natDegree Q) :
    ∃ A : ℝ, 0 < A ∧ ∀ (β M : ℝ), 1 ≤ M →
      (∀ x ∈ Set.Icc (0:ℝ) M, ∀ y ∈ Set.Icc (0:ℝ) M,
        ‖Complex.exp (-(2 * Real.pi * Complex.I * (β * (Work.A3.Qreal Q).eval x)))
          - Complex.exp (-(2 * Real.pi * Complex.I * (β * (Work.A3.Qreal Q).eval y)))‖
        ≤ (2 * Real.pi * |β| * A * (Q.natDegree : ℝ) * M ^ (Q.natDegree - 1)) * |x - y|)
      ∧ (∀ x : ℝ, ‖Complex.exp (-(2 * Real.pi * Complex.I * (β * (Work.A3.Qreal Q).eval x)))‖ = 1) := by
  set S : ℝ := ∑ i ∈ Finset.range (Polynomial.natDegree Q + 1), |(Work.A3.Qreal Q).coeff i| with hS
  refine ⟨S + 1, by positivity, ?_⟩
  intro β M hM
  refine ⟨?_, fun x => ?_⟩
  · intro x hx y hy
    have hdeg : (Work.A3.Qreal Q).natDegree ≤ Polynomial.natDegree Q := by
      rw [Work.A3.Qreal]; exact Polynomial.natDegree_map_le
    have hlip := Commons.Analysis.Polynomial.abs_eval_sub_eval_le (Work.A3.Qreal Q)
      (Polynomial.natDegree Q) hd hdeg hx.1 hy.1 hx.2 hy.2 hM
    have hexp := Work.A3.norm_exp_neg_two_pi_I_mul_sub_le β
      ((Work.A3.Qreal Q).eval x) ((Work.A3.Qreal Q).eval y)
    have h2 : 0 ≤ 2 * Real.pi * |β| := by positivity
    have hdnn : 0 ≤ (Polynomial.natDegree Q : ℝ) := Nat.cast_nonneg _
    have hMnn : 0 ≤ M := le_trans zero_le_one hM
    have hMpow : 0 ≤ M ^ (Polynomial.natDegree Q - 1) := pow_nonneg hMnn _
    have hxy : 0 ≤ |x - y| := abs_nonneg _
    have hSle : S ≤ S + 1 := le_add_of_nonneg_right zero_le_one
    calc ‖Complex.exp (-(2 * Real.pi * Complex.I * (β * (Work.A3.Qreal Q).eval x)))
          - Complex.exp (-(2 * Real.pi * Complex.I * (β * (Work.A3.Qreal Q).eval y)))‖
        ≤ 2 * Real.pi * |β| * |(Work.A3.Qreal Q).eval x - (Work.A3.Qreal Q).eval y| := hexp
      _ ≤ 2 * Real.pi * |β| *
            (S * (Polynomial.natDegree Q : ℝ) * M ^ (Polynomial.natDegree Q - 1) * |x - y|) := by
          apply mul_le_mul_of_nonneg_left _ h2
          simpa [hS] using hlip
      _ ≤ 2 * Real.pi * |β| *
            ((S + 1) * (Polynomial.natDegree Q : ℝ) * M ^ (Polynomial.natDegree Q - 1) * |x - y|) := by
          apply mul_le_mul_of_nonneg_left _ h2
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSle hdnn) hMpow) hxy
      _ = (2 * Real.pi * |β| * (S + 1) * (Polynomial.natDegree Q : ℝ)
            * M ^ (Polynomial.natDegree Q - 1)) * |x - y| := by
          ring
  · have h : -(2 * Real.pi * Complex.I * (β * (Work.A3.Qreal Q).eval x))
        = Complex.I * ((-(2 * Real.pi * (β * (Work.A3.Qreal Q).eval x))) : ℝ) := by
      push_cast; ring
    rw [h, Complex.norm_exp_I_mul_ofReal]

end Work.A3
