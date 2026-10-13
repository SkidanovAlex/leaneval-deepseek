import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le
import Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/StrongEps/HkSqAux/slot_sq_bound.lean`

The single-slot `L²`-bound behind the `E1` weighted estimates.  If the difference quotient `D`
commutes with the mollifier `J_ε` in the form

  `D (Jeps ρ ε f) z θ = ∫ p, Jker ρ ε p * D f (zShift z p.1) (thShift θ p.2)`

and the weight `W` is almost invariant under the two shifts,
`W z θ ≤ e^{cε} · W (zShift z p.1) (thShift θ p.2)` for every `p`, then

  `(W z θ * D (Jeps ρ ε f) z θ)^2 ≤ e^{2cε} ∫ p, Jker ρ ε p * (W (zShift z p.1) (thShift θ p.2)
      * D f (zShift z p.1) (thShift θ p.2))^2`.

Since `Jker ρ ε` is, by `IsMollKernel`, a *probability* density (nonnegative, total mass `1`,
supported in the ball of radius `ε`), this is Jensen's inequality for the average of the shifted
slot, with the weight ratio `e^{cε}` taken out of the integral.

The proof splits into the two halves of the statement.

* **`abs_slot_le` (the absolute-value bound).**  The shift inequality gives, pointwise,
  `W z θ * |D f (shift p)| ≤ e^{cε} * |W (shift p) * D f (shift p)|` (the shifted weight is
  nonnegative, being `≥ e^{-cε} W z θ ≥ 0`).  Integrating against the nonnegative kernel and
  pulling out the constant `e^{cε}` bounds `|W z θ * D (Jeps ρ ε f) z θ|`.
* **Cauchy–Schwarz.**  `sq_integral_Jker_mul_le` applied to the test function
  `|W (shift ·) * D f (shift ·)|`, whose square is the weight times the square of the slot.

Both integrals are genuine because `Jker ρ ε` is supported in the compact ball of radius `ε`, on
which the relevant test functions are continuous (`hg`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

/-- **The absolute-value half of the slot bound.**  Under the shift inequality for the weight `W`,
the weighted average `W z θ * D (Jeps ρ ε f) z θ` is dominated in absolute value by `e^{cε}` times
the average of `|W (shift p) * D f (shift p)|` against the (probability) kernel.

The proof is monotonicity of the integral for the pointwise inequality
`W z θ * |D f (shift p)| ≤ e^{cε} * |W (shift p) * D f (shift p)|`, together with
`|∫ p, k p * A p| ≤ ∫ p, k p * |A p|` for `k = Jker ρ ε ≥ 0`. -/
theorem abs_slot_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε c : ℝ} (hε : 0 < ε)
    (D : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ) (W f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hcomm : D (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (hWnn : 0 ≤ W z θ)
    (hW : ∀ p : ℝ × ℝ, W z θ ≤ Real.exp (c * ε)
        * W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (hg : ContinuousOn (fun p : ℝ × ℝ =>
        W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    |W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ|
      ≤ Real.exp (c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| := by
  -- the shifted weight is nonnegative, since `0 ≤ W z θ ≤ e^{cε} * W (shift p)`
  have hWsh : ∀ p : ℝ × ℝ,
      0 ≤ W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => nonneg_of_mul_nonneg_right (le_trans hWnn (hW p)) (Real.exp_pos _)
  -- pull the constant `W z θ` inside the integral
  have hX : W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W z θ * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
    rw [hcomm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => by ring)
  -- the pointwise comparison of the two slots
  have hpt : ∀ p : ℝ × ℝ,
      W z θ * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        ≤ Real.exp (c * ε) * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| := by
    intro p
    have h3 : Real.exp (c * ε) * |W (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        = Real.exp (c * ε) * (W (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
            * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) := by
      rw [abs_mul, abs_of_nonneg (hWsh p)]
    rw [h3]
    calc W z θ * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        ≤ (Real.exp (c * ε) * W (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2))
            * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| :=
          mul_le_mul_of_nonneg_right (hW p) (abs_nonneg _)
      _ = Real.exp (c * ε) * (W (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
            * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) := by
          ring
  rw [hX]
  calc |∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W z θ * D f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2))|
      ≤ ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p
          * (W z θ * D f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2))| := by
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm
            (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
              * (W z θ * D f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)))
    _ = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W z θ * |D f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)|) := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only
        rw [abs_mul, abs_mul, abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p),
          abs_of_nonneg hWnn]
    _ ≤ ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (Real.exp (c * ε) * |W (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) := by
        refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun p => ?_) ?_
          (Eventually.of_forall fun p => ?_)
        · simp only
          exact mul_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p)
            (mul_nonneg hWnn (abs_nonneg _))
        · exact Work.FTS.StrongEps.HkSqAux.integrable_Jker_mul ρ hρ hε (hg.abs.const_mul _)
        · simp only
          exact mul_le_mul_of_nonneg_left (hpt p)
            (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p)
    _ = Real.exp (c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => by ring)

theorem slot_sq_bound (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε c : ℝ} (hε : 0 < ε)
    (D : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ) (W f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hcomm : D (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (hWnn : 0 ≤ W z θ)
    (hW : ∀ p : ℝ × ℝ, W z θ ≤ Real.exp (c * ε)
        * W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (hg : ContinuousOn (fun p : ℝ × ℝ =>
        W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    (W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ) ^ 2
      ≤ Real.exp (2 * c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
  have hbound := abs_slot_le ρ hρ hε D W f hcomm hWnn hW hg
  -- Cauchy–Schwarz for the probability density `Jker ρ ε`
  have hCS := Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le ρ hρ hε
    (fun p : ℝ × ℝ => |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
        * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) hg.abs
  have hCSeq : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) ^ 2
      ≤ ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * (W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
    simpa only [sq_abs] using hCS
  have hexp : Real.exp (c * ε) ^ 2 = Real.exp (2 * c * ε) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  calc (W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ) ^ 2
      = |W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ| ^ 2 := by rw [sq_abs]
    _ ≤ (Real.exp (c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hbound 2
    _ = Real.exp (c * ε) ^ 2 * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) ^ 2 := by
        rw [mul_pow]
    _ ≤ Real.exp (c * ε) ^ 2 * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hCSeq (sq_nonneg _)
    _ = Real.exp (2 * c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
        rw [hexp]

end Work.FTS.StrongEps.HkSqAux
