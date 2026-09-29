import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17y.gen_main
import Submission.Work.C17y.dstable_const

namespace Work.C17

open Polynomial

/-- The `y''`-coefficient `P₂` of `M` is nonzero (over `ℂ`). -/
private lemma P2C_ne_zero (a b : ℚ) : P2C a b ≠ 0 := by
  rw [P2C, Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective]
  show (X - 1) * X * (X + 1) * Q4x a b ≠ 0
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · simpa using (Polynomial.monic_X_sub_C (1 : ℚ)).ne_zero
  · exact Polynomial.X_ne_zero
  · simpa using (Polynomial.monic_X_add_C (1 : ℚ)).ne_zero
  · intro h
    have := congrArg (fun p : Polynomial ℚ => p.eval 0) h
    simp [Q4x] at this

/-- The denominators `rdC i` are nonzero. -/
private lemma rdC_ne_zero (i : Fin 6) : rdC i ≠ 0 := by
  rw [rdC, Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective]
  exact RatFunc.denom_ne_zero _

theorem y1_periods_indep_gen (a b : ℚ) (hA : Work.C17.AdmQ a b)
    (hric : ∀ u : RatFunc ℂ,
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P2C a b))
          * (Submission.CDT.dRat u + u ^ 2)
        + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P1C a b)) * u
        + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P0C a b)) ≠ 0)
    (hadj : ∀ (β : RatFunc ℂ) (c : Fin 6 → ℂ),
      Submission.CDT.dRat
            (Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P2C a b) * β))
          - Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P1C a b) * β)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P0C a b) * β
        = ∑ i : Fin 6, (algebraMap ℂ (RatFunc ℂ) (c i)) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rnC i)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rdC i)) →
      β = 0 ∧ c = 0)
    (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball (((Work.C17.xs a b : ℝ) : ℂ)) δ))
    (hy1ne : y1 (((Work.C17.xs a b : ℝ) : ℂ)) ≠ 0)
    (hode : ∀ z ∈ Metric.ball (((Work.C17.xs a b : ℝ) : ℂ)) δ,
      (Work.C17.P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
        + (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        + (Work.C17.P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0)
    (J : Fin 6 → ℂ → ℂ)
    (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball (((Work.C17.xs a b : ℝ) : ℂ)) δ))
    (hJ0 : ∀ i, J i (((Work.C17.xs a b : ℝ) : ℂ)) = 0)
    (hJderiv : ∀ i, ∀ z ∈ Metric.ball (((Work.C17.xs a b : ℝ) : ℂ)) δ,
      HasDerivAt (J i) (((Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
        / ((Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ).denom.eval₂ (algebraMap ℚ ℂ) z)
          * y1 z) z)
    (A B : Polynomial ℚ) (C : Fin 6 → Polynomial ℚ)
    (hrel : ∀ z ∈ Metric.ball (((Work.C17.xs a b : ℝ) : ℂ)) δ,
      (A.eval₂ (algebraMap ℚ ℂ) z) * y1 z + (B.eval₂ (algebraMap ℚ ℂ) z) * deriv y1 z
        + ∑ i : Fin 6, ((C i).eval₂ (algebraMap ℚ ℂ) z) * J i z = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hy1ne' : ∃ z ∈ Metric.ball (((Work.C17.xs a b : ℝ) : ℂ)) δ, y1 z ≠ 0 :=
    ⟨_, Metric.mem_ball_self hδ, hy1ne⟩
  have hode' : ∀ z ∈ Metric.ball (((Work.C17.xs a b : ℝ) : ℂ)) δ,
      (P2C a b).eval z * deriv (deriv y1) z + (P1C a b).eval z * deriv y1 z
        + (P0C a b).eval z * y1 z = 0 := by
    intro z hz
    simpa only [P2C, P1C, P0C, Polynomial.eval_map] using hode z hz
  have hJderiv' : ∀ i : Fin 6, ∀ z ∈ Metric.ball (((Work.C17.xs a b : ℝ) : ℂ)) δ,
      HasDerivAt (J i) ((rnC i).eval z / (rdC i).eval z * y1 z) z := by
    intro i z hz
    simpa only [rnC, rdC, Polynomial.eval_map] using hJderiv i z hz
  obtain ⟨hA0, hB0, hC0⟩ :=
    Work.C17y.periods_indep_gen (P2C a b) (P1C a b) (P0C a b) (P2C_ne_zero a b) rnC rdC
      (fun i => rdC_ne_zero i) hric hadj (((xs a b : ℝ) : ℂ)) hδ y1 hy1d hy1ne' hode' J hJd
      hJderiv' (A.map (algebraMap ℚ ℂ)) (B.map (algebraMap ℚ ℂ))
      (fun i => (C i).map (algebraMap ℚ ℂ)) (by
        intro z hz
        simpa only [Polynomial.eval_map] using hrel z hz)
  refine ⟨?_, ?_, ?_⟩
  · exact (Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective).mp hA0
  · exact (Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective).mp hB0
  · funext i
    exact (Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective).mp (congrFun hC0 i)

end Work.C17
