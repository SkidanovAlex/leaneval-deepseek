import Mathlib
import Submission.Work.ALift.ode_A
import Submission.Work.ALift.coef_bound_A
import Submission.Work.ALift.hasDerivAt_tsum_pow_rate

/-!
# Area ALift — `U₀` and `U₁` are analytic, with derivatives `U₁` and `U₂`

The coefficient bound `‖hcoef a b c k‖ ≤ C·(11/10)^k` (`coef_bound_A`) has rate `11/10 > 10/9`, so
the functions `U₀ = Σ_k h_k q^k`, `U₁ = Σ_k (k+1)h_{k+1}q^k`, `U₂ = Σ_k (k+1)(k+2)h_{k+2}q^k` are
analytic on the disc `‖q‖ < 10/11`, and term-by-term differentiation
(`hasDerivAt_tsum_pow_rate`) gives `U₀' = U₁` and `U₁' = U₂` there.
-/

open PowerSeries

namespace Work.ALift

open Submission.CDTPlan

noncomputable section

theorem hasDerivAt_HU (a b c : ℤ) (hRel : ARel a b c) (q : ℂ) (hq : ‖q‖ ≤ 9 / 10) :
    HasDerivAt (HU0 a b c) (HU1 a b c q) q ∧ HasDerivAt (HU1 a b c) (HU2 a b c q) q := by
  obtain ⟨C, hC0, hC⟩ := coef_bound_A a b c hRel
  have hq' : ‖q‖ < 1 / (11 / 10 : ℝ) := by
    rw [show (1 : ℝ) / (11 / 10) = 10 / 11 by norm_num]
    linarith
  constructor
  · have h := hasDerivAt_tsum_pow_rate (hcoef a b c) C (11 / 10) hC0 (by norm_num) 0
      (fun k => by simpa using hC k) hq'
    have hfun : (fun z : ℂ => ∑' k : ℕ, hcoef a b c k * z ^ k) = HU0 a b c := by
      funext z; rw [HU0]
    rw [hfun] at h
    refine h.congr_deriv ?_
    rw [HU1]
  · have hnorm : ∀ k : ℕ, ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := Work.CLift.norm_add_one
    have hb : ∀ k : ℕ, ‖((k : ℂ) + 1) * hcoef a b c (k + 1)‖
        ≤ (C * (11 / 10)) * ((k : ℝ) + 1) ^ 1 * (11 / 10) ^ k := by
      intro k
      rw [norm_mul, hnorm k]
      calc ((k : ℝ) + 1) * ‖hcoef a b c (k + 1)‖
          ≤ ((k : ℝ) + 1) * (C * (11 / 10) ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left (hC (k + 1)) (by positivity)
        _ = (C * (11 / 10)) * ((k : ℝ) + 1) ^ 1 * (11 / 10) ^ k := by
            rw [pow_succ]; ring
    have h := hasDerivAt_tsum_pow_rate (fun k : ℕ => ((k : ℂ) + 1) * hcoef a b c (k + 1))
      (C * (11 / 10)) (11 / 10) (by positivity) (by norm_num) 1 hb hq'
    have hfun : (fun z : ℂ => ∑' k : ℕ, ((k : ℂ) + 1) * hcoef a b c (k + 1) * z ^ k)
        = HU1 a b c := by
      funext z
      rw [HU1]
    rw [hfun] at h
    refine h.congr_deriv ?_
    rw [HU2]
    apply tsum_congr
    intro k
    have hk : (k + 1) + 1 = k + 2 := by omega
    rw [hk]
    push_cast
    ring

end

end Work.ALift
