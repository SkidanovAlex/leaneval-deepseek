import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Solutions.rat_bound
import Submission.Work.TMC7Core.Solutions.lyap_periodic
import Submission.Work.TMC7Core.Scale.floquet_trace_bound_phase
import Submission.Work.TMC7Core.Scale.trace_oscillation_pair

/-!
# The rational Lyapunov bound at an arbitrary phase

This is **S5** of the lead's C7 design (`Submission/Work/TMC7Core/Scale/S5_GUIDE.md`).

For `α = p/q` in lowest terms, every energy in the spectrum of the almost Mathieu operator
satisfies `L(E) ≤ max 0 (log|λ|) + log 6 / q`.  The phase `θ` does not appear on either side,
but the proof does use the phase:

* `floquet_trace_bound_phase` bounds the Floquet trace at the phase of the operator,
  `‖tr A_q(θ)‖ ≤ 2`, for `E` in the spectrum at that phase (this is where `P_Schnol` and the
  phase-general Floquet step are consumed);
* `trace_oscillation_pair` (Chambers) turns this into `|tr A_q(x)| ≤ 2 + 4|λ|^q` for every
  `x`, uniformly in `θ`;
* `log_rhoSL_le_of_abs_le` converts that pointwise bound into the `q·log⁺|λ| + log 6` bound on
  `log ρ(A_q(x))`;
* `lyap_periodic` identifies `lyap α λ E` with the average of `log ρ(A_q(x))` over one period,
  which averages over the phase `x` and therefore does not see `θ`.
-/

namespace Work.TMC7Core.Scale

open Work.TMC7Core

noncomputable section

/-- The arithmetic core of the rational Lyapunov bound: `|τ| ≤ 2 + 4|λ|^q` forces
`log ρ(τ) ≤ q·max 0 (log|λ|) + log 6`, where `ρ` is the spectral radius of an `SL(2,ℝ)`
matrix with trace `τ`. -/
lemma log_rhoSL_le_of_abs_le (q : ℕ) (lam τ : ℝ) (hτ : |τ| ≤ 2 + 4 * |lam| ^ q) :
    Real.log (rhoSL τ) ≤ (q : ℝ) * max 0 (Real.log |lam|) + Real.log 6 := by
  have hρ : rhoSL τ ≤ 2 + 4 * |lam| ^ q :=
    le_trans (rhoSL_le τ) (max_le (by have h := pow_nonneg (abs_nonneg lam) q; linarith) hτ)
  have hlog : Real.log (rhoSL τ) ≤ Real.log (2 + 4 * |lam| ^ q) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (rhoSL_one_le τ)) hρ
  refine le_trans hlog ?_
  rcases lt_or_ge (1 : ℝ) |lam| with ha | ha
  · have ha1 : 1 ≤ |lam| := le_of_lt ha
    have haq1 : 1 ≤ |lam| ^ q := one_le_pow₀ ha1
    have h6 : 2 + 4 * |lam| ^ q ≤ 6 * |lam| ^ q := by linarith
    have h1' := Real.log_le_log
      (by have h := pow_nonneg (abs_nonneg lam) q; linarith : (0 : ℝ) < 2 + 4 * |lam| ^ q) h6
    have hmul : Real.log (6 * |lam| ^ q) = Real.log 6 + (q : ℝ) * Real.log |lam| := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rw [hmul] at h1'
    rw [max_eq_right (Real.log_nonneg ha1)]
    linarith
  · have haq : |lam| ^ q ≤ 1 := pow_le_one₀ (abs_nonneg lam) ha
    have h6 : 2 + 4 * |lam| ^ q ≤ 6 := by linarith
    have h1' := Real.log_le_log
      (by have h := pow_nonneg (abs_nonneg lam) q; linarith : (0 : ℝ) < 2 + 4 * |lam| ^ q) h6
    rw [max_eq_left (Real.log_nonpos (abs_nonneg lam) ha), mul_zero, zero_add]
    linarith

/-- **S5** of the lead's C7 design (see `Submission/Work/TMC7Core/Scale/S5_GUIDE.md`):
the rational bound at an arbitrary phase.  (Hypotheses `P_OpBasics`, `P_Schnol` and coprimality
added, as the reviewer of this path pointed out: they are what `Solutions.rat_bound` actually
consumes and what the Floquet step needs; the call sites in S3/S2 supply them.) -/
theorem rat_bound_phase (h1 : Work.TMC7Core.P_OpBasics) (h15 : Work.TMC7Core.P_Schnol)
    (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs p) q)
    (lam θ E : ℝ)
    (H : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo)
    (hH : LeanEval.Analysis.TenMartini.IsAlmostMathieuOperator ((p : ℝ) / (q : ℝ)) lam θ H)
    (hE : (E : ℂ) ∈ spectrum ℂ H) :
    Work.TMC7Core.lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
      ≤ max 0 (Real.log |lam|) + Real.log 6 / (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Solutions.lyap_periodic p q hq lam E]
  have hcont := Solutions.continuous_log_rhoSL_trace p q lam E
  have hfl := floquet_trace_bound_phase h1 h15 p q hq lam θ E H hH hE
  -- pointwise bound on `log ρ(A_q(x))` at every phase `x`
  have hpt : ∀ x : ℝ,
      Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace.re))
        ≤ (q : ℝ) * max 0 (Real.log |lam|) + Real.log 6 := by
    intro x
    refine log_rhoSL_le_of_abs_le q lam _ ?_
    have himx := Solutions.trace_iterC_im_zero ((p : ℝ) / (q : ℝ)) lam E q x
    have heqx := Solutions.trace_eq_ofReal_re himx
    have hnorm : ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace‖
        = |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re| := by
      conv_lhs => rw [heqx]
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hosc := trace_oscillation_pair p q hq hcop lam E x θ
    have htri : ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace‖
        ≤ ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).trace‖
          + ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace
            - (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).trace‖ := by
      have h := norm_add_le ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).trace)
        ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace
          - (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).trace)
      have h2 : (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).trace
          + ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace
            - (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).trace)
          = (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace := by ring
      rwa [h2] at h
    calc |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re|
        = ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace‖ := hnorm.symm
      _ ≤ 2 + 4 * |lam| ^ q := le_trans htri (add_le_add hfl hosc)
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (show (0 : ℝ) ≤ 1 by norm_num) (hcont.intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1) (fun x _ => hpt x)
  have hg : (∫ x in (0 : ℝ)..1, ((q : ℝ) * max 0 (Real.log |lam|) + Real.log 6))
      = (q : ℝ) * max 0 (Real.log |lam|) + Real.log 6 := by
    rw [intervalIntegral.integral_const]
    simp
  rw [hg] at hint
  calc (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1,
        Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace.re)))
      ≤ (1 / (q : ℝ)) * ((q : ℝ) * max 0 (Real.log |lam|) + Real.log 6) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = max 0 (Real.log |lam|) + Real.log 6 / (q : ℝ) := by
        have h1 : (1 : ℝ) / (q : ℝ) * ((q : ℝ) * max 0 (Real.log |lam|))
            = max 0 (Real.log |lam|) := by
          rw [← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hq0), one_mul]
        have h2 : (1 : ℝ) / (q : ℝ) * Real.log 6 = Real.log 6 / (q : ℝ) := by
          rw [one_div, inv_mul_eq_div]
        rw [mul_add, h1, h2]

end

end Work.TMC7Core.Scale
