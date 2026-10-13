import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.abs_sub_le_exp_sqrt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_mul_of_sq_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integral_mul_le_sqrt_mul_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

/-- The `L²`-commutator estimate for a weight `Q` that is comparable to its translates:
if `0 ≤ Q` and `Q (y + p) ≤ e^{Cw(|p₁|+|p₂|)} Q y` together with the reverse inequality
(so that `Q` is "log-Lipschitz" with constant `Cw` in both directions), then for any
`G₁, G₂` with `Q · Gᵢ²` integrable,

`|∫ (Q y − Q (y − p)) G₁ (y − p) G₂ y| ≤ (e^{Cw(|p₁|+|p₂|)} − 1) ‖G₁‖_{L²(Q)} ‖G₂‖_{L²(Q)}`.

The mechanism: pointwise `|Q y − Q (y − p)| ≤ (E−1)·min (Q y) (Q (y − p)) ≤ (E−1)·√(Q y Q (y − p))`
with `E = e^{Cw(|p₁|+|p₂|)}`, then Cauchy–Schwarz against
`√(Q y)|G₂ y|` and `√(Q (y − p))|G₁ (y − p)|`, using translation invariance,
`∫ Q (y − p) G₁ (y − p)² = ∫ Q G₁²`, to remove the shift. -/
theorem dabsIntLe {Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) (p : ℝ × ℝ) :
    |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by
  set E : ℝ := Real.exp (Cw * (|p.1| + |p.2|)) with hEdef
  have hE1 : 1 ≤ E := by
    rw [hEdef]
    exact Real.one_le_exp (mul_nonneg hCw (add_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hE0 : 0 ≤ E - 1 := by linarith
  -- Pointwise: `|Q y - Q (y - p)| ≤ (E - 1) √(Q y) √(Q (y - p))`.
  have hA : ∀ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (E - 1) * ((Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|)) := by
    intro y
    have hb : Q (y - p) ≤ E * Q y := by
      rw [hEdef]
      simpa [sub_add_cancel] using hQsh' (y - p) p
    have ha : Q y ≤ E * Q (y - p) := by
      rw [hEdef]
      simpa [sub_add_cancel] using hQsh (y - p) p
    have hmin := abs_sub_le_exp_sqrt hE1 (hQ0 y) (hQ0 (y - p)) ha hb
    calc |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
        = |Q y - Q (y - p)| * |G₁ (y - p)| * |G₂ y| := by rw [abs_mul, abs_mul]
      _ ≤ ((E - 1) * Real.sqrt (Q y * Q (y - p))) * |G₁ (y - p)| * |G₂ y| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hmin (abs_nonneg _)) (abs_nonneg _)
      _ = (E - 1) * ((Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|)) := by
            rw [Real.sqrt_mul (hQ0 y)]
            ring
  -- Square integrability of the two C-S factors.
  have hu2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => (Real.sqrt (Q y) * |G₂ y|) ^ 2) := by
    refine hI2.congr (Filter.Eventually.of_forall fun y => ?_)
    show Q y * G₂ y ^ 2 = (Real.sqrt (Q y) * |G₂ y|) ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 y), sq_abs]
  have hv2 : MeasureTheory.Integrable
      (fun y : ℝ × ℝ => (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) ^ 2) := by
    refine (hI1.comp_sub_right p).congr (Filter.Eventually.of_forall fun y => ?_)
    show Q (y - p) * G₁ (y - p) ^ 2 = (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 (y - p)), sq_abs]
  have hmu : Measurable (fun y : ℝ × ℝ => Real.sqrt (Q y) * |G₂ y|) := hQm.sqrt.mul hG2m.abs
  have hmv : Measurable (fun y : ℝ × ℝ => Real.sqrt (Q (y - p)) * |G₁ (y - p)|) :=
    (hQm.comp (measurable_id.sub measurable_const)).sqrt.mul
      (hG1m.comp (measurable_id.sub measurable_const)).abs
  have hprod : MeasureTheory.Integrable (fun y : ℝ × ℝ =>
      (Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|)) :=
    integrable_mul_of_sq_integrable hmu hmv hu2 hv2
  -- Step 1: take absolute values pointwise.
  have hstep1 : ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (E - 1) * ∫ y : ℝ × ℝ,
          (Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => abs_nonneg _) ?_ ?_
    · exact hprod.const_mul (E - 1)
    · exact Filter.Eventually.of_forall fun y => hA y
  -- Step 2: Cauchy–Schwarz, with all the shifts removed by translation invariance.
  have hCS := integral_mul_le_sqrt_mul_sqrt (μ := MeasureTheory.volume)
      (f := fun y : ℝ × ℝ => Real.sqrt (Q y) * |G₂ y|)
      (g := fun y : ℝ × ℝ => Real.sqrt (Q (y - p)) * |G₁ (y - p)|)
      (fun y => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (fun y => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hmu hmv hu2 hv2
  have hIntU : ∫ y : ℝ × ℝ, (Real.sqrt (Q y) * |G₂ y|) ^ 2 = ∫ y : ℝ × ℝ, Q y * G₂ y ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (Real.sqrt (Q y) * |G₂ y|) ^ 2 = Q y * G₂ y ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 y), sq_abs]
  have hIntV : ∫ y : ℝ × ℝ, (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) ^ 2
      = ∫ y : ℝ × ℝ, Q y * G₁ y ^ 2 := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => (by
      show (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) ^ 2 = Q (y - p) * G₁ (y - p) ^ 2
      rw [mul_pow, Real.sq_sqrt (hQ0 (y - p)), sq_abs]))]
    exact MeasureTheory.integral_sub_right_eq_self (fun x => Q x * G₁ x ^ 2) p
  have hstep2 : ∫ y : ℝ × ℝ, (Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|)
      ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2) := by
    rw [← hIntU, ← hIntV]
    exact hCS
  calc |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      = ‖∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ × ℝ, ‖(Q y - Q (y - p)) * G₁ (y - p) * G₂ y‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y| := by
          simp only [Real.norm_eq_abs]
    _ ≤ (E - 1) * ∫ y : ℝ × ℝ,
            (Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) := hstep1
    _ ≤ (E - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) *
            Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep2 hE0
    _ = (E - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
