import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.pd_aux.proj_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_aux.proj_int` — `L¹` for the window-derivative integrand

`kinIntD ℓ d u x = Σ_k (∂_k χ_{B(u)}(x))²` is the derivative of the sliding window alone.
Its `u`-dependence is confined to a ball: the Leibniz form `chiBLb` of `∂_kχ_{B(u)}` is
supported where the sliding factor `chiScale (ℓ*d)(x 0 - (ℓ*d)•u)` or its derivative does not
vanish, and both of those force `‖x 0 - (ℓ*d)•u‖ ≤ ℓ*d/2`, while the factor `chiScale ℓ` (or its
derivative) forces `‖x 0‖ ≤ ℓ/2`.  Hence `kinIntD` is dominated by a constant times a ball
indicator in `u`, which is `Integrable` for `pdMu ℓ` (the `x`-measure is finite on the box).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- A uniform bound on the directional derivative of `chiScale s`. -/
lemma fderiv_chiScale_bound (s : ℝ) (hs : 0 < s) (k : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ³, |fderiv ℝ (chiScale s) z (kcStdBasis k)| ≤ M := by
  have hcont : Continuous (fun z : ℝ³ => fderiv ℝ (chiScale s) z (kcStdBasis k)) :=
    (chiScale_contDiff (ne_of_gt hs)).continuous_fderiv (by simp) |>.clm_apply continuous_const
  obtain ⟨M, hM⟩ := ((chiScale_hasCompactSupport (ne_of_gt hs)).fderiv_apply ℝ
      (kcStdBasis k)).exists_bound_of_continuous hcont
  exact ⟨M, le_trans (norm_nonneg _) (hM 0), fun z => by rw [← Real.norm_eq_abs]; exact hM z⟩

/-- **`kinIntD` is dominated by a constant times the indicator of a ball in `u`.** -/
theorem kinIntD_le_ball {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∃ R C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ³) (x : X1),
      kinIntD ℓ d u x
        ≤ C * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) u := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  choose MD1 hMD1 using fun k : Fin 3 => fderiv_chiScale_bound ℓ hℓ k
  choose MD2 hMD2 using fun k : Fin 3 => fderiv_chiScale_bound (ℓ * d) hld k
  refine ⟨(ℓ / 2 + ℓ * d / 2) / (ℓ * d),
    ∑ k : Fin 3, (MD1 k * chiSup + chiSup * MD2 k) ^ 2, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  · intro u x
    have hR : ℓ * d * ((ℓ / 2 + ℓ * d / 2) / (ℓ * d)) = ℓ / 2 + ℓ * d / 2 :=
      mul_div_cancel₀ _ (ne_of_gt hld)
    rw [kinIntD_eq hℓ hd u x]
    by_cases hu : u ∈ Metric.closedBall (0 : ℝ³) ((ℓ / 2 + ℓ * d / 2) / (ℓ * d))
    · rw [Set.indicator_of_mem hu, mul_one]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hK0 : 0 ≤ MD1 k * chiSup + chiSup * MD2 k :=
        add_nonneg (mul_nonneg (hMD1 k).1 chiSup_pos.le)
          (mul_nonneg chiSup_pos.le (hMD2 k).1)
      have hb : |chiBLb ℓ d k (u, x)| ≤ MD1 k * chiSup + chiSup * MD2 k := by
        have hA : |fderiv ℝ (chiScale ℓ) (x 0) (kcStdBasis k)| ≤ MD1 k := (hMD1 k).2 (x 0)
        have hB : |chiScale (ℓ * d) (x 0 - (ℓ * d) • u)| ≤ chiSup := abs_chiScale_le_chiSup _ _
        have hC : |chiScale ℓ (x 0)| ≤ chiSup := abs_chiScale_le_chiSup _ _
        have hD : |fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k)| ≤ MD2 k :=
          (hMD2 k).2 _
        rw [chiBLb]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hA hB (abs_nonneg _) (hMD1 k).1)
          (mul_le_mul hC hD (abs_nonneg _) chiSup_pos.le)
      rw [sq_le_sq, abs_of_nonneg hK0]
      exact hb
    · rw [Set.indicator_of_notMem hu, mul_zero]
      have hzero : ∀ k : Fin 3, chiBLb ℓ d k (u, x) = 0 := by
        intro k
        by_contra hk
        have hru : (ℓ / 2 + ℓ * d / 2) / (ℓ * d) < ‖u‖ := by
          rw [mem_closedBall, dist_eq_norm, sub_zero] at hu
          exact lt_of_not_ge hu
        rw [chiBLb] at hk
        set A : ℝ := fderiv ℝ (chiScale ℓ) (x 0) (kcStdBasis k) with hA
        set B : ℝ := chiScale (ℓ * d) (x 0 - (ℓ * d) • u) with hB
        set C : ℝ := chiScale ℓ (x 0) with hC
        set D : ℝ := fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k) with hD
        have hor : A * B ≠ 0 ∨ C * D ≠ 0 := by
          by_contra h
          push_neg at h
          exact hk (by rw [h.1, h.2, add_zero])
        have hx1 : ‖x 0‖ ≤ ℓ / 2 := by
          rcases hor with h | h
          · exact le_of_not_gt fun hlt =>
              (mul_ne_zero_iff.mp h).1 (fderiv_chiScale_eq_zero_of_norm_gt hℓ hlt)
          · exact le_of_not_gt fun hlt =>
              (mul_ne_zero_iff.mp h).1 (chiScale_eq_zero_of_norm_gt hℓ hlt)
        have hx2 : ‖x 0 - (ℓ * d) • u‖ ≤ ℓ * d / 2 := by
          rcases hor with h | h
          · exact le_of_not_gt fun hlt =>
              (mul_ne_zero_iff.mp h).2 (chiScale_eq_zero_of_norm_gt hld hlt)
          · exact le_of_not_gt fun hlt =>
              (mul_ne_zero_iff.mp h).2 (fderiv_chiScale_eq_zero_of_norm_gt hld hlt)
        have hnorm : ℓ * d * ‖u‖ ≤ ℓ / 2 + ℓ * d / 2 := by
          have h1 : ‖(ℓ * d) • u‖ = ℓ * d * ‖u‖ := by
            rw [norm_smul, Real.norm_of_nonneg hld.le]
          have h2 : ‖(ℓ * d) • u‖ ≤ ‖(ℓ * d) • u - x 0‖ + ‖x 0‖ := by
            have := norm_add_le ((ℓ * d) • u - x 0) (x 0)
            simpa using this
          rw [h1] at h2
          have h3 : ‖(ℓ * d) • u - x 0‖ = ‖x 0 - (ℓ * d) • u‖ := norm_sub_rev _ _
          rw [h3] at h2
          linarith
        have : ‖u‖ ≤ (ℓ / 2 + ℓ * d / 2) / (ℓ * d) := by
          rw [le_div_iff₀ hld]
          rw [mul_comm] at hnorm
          exact hnorm
        linarith
      rw [Finset.sum_eq_zero (fun k _ => by rw [hzero k]; ring)]

/-- A constant times the indicator of a ball in the first variable is `L¹` for `pdMu ℓ`. -/
theorem integrable_indicator_fst_pdMu_aux {ℓ : ℝ} (hℓ : 0 < ℓ) (R C : ℝ) :
    Integrable (fun p : ℝ³ × X1 =>
        C * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) p.1)
      (pdMu ℓ) := by
  classical
  haveI hfin : IsFiniteMeasure ((volume : Measure X1).restrict (abox 1 ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, abox_volume 1 ℓ hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
  have hind : Integrable
      (fun u : ℝ³ => (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) u)
      (volume : Measure ℝ³) := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact integrableOn_const (MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ³)) (r := R)).ne
  have h := (hind.const_mul C).comp_fst ((volume : Measure X1).restrict (abox 1 ℓ))
  rw [pdMu]
  exact h

/-- **The window-derivative integrand is `L¹` for `pdMu ℓ`.** -/
theorem integrable_kinIntD_aux {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    Integrable (fun p : ℝ³ × X1 => kinIntD ℓ d p.1 p.2) (pdMu ℓ) := by
  obtain ⟨R, C, hC0, hRC⟩ := kinIntD_le_ball hℓ hd
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ × X1 => kinIntD ℓ d p.1 p.2) (pdMu ℓ) := by
    have hcont : Continuous (fun p : ℝ³ × X1 => kinIntD ℓ d p.1 p.2) := by
      have hfun : (fun p : ℝ³ × X1 => kinIntD ℓ d p.1 p.2)
          = fun p : ℝ³ × X1 => ∑ k : Fin 3, (chiBLb ℓ d k p) ^ 2 := by
        funext p
        rw [kinIntD_eq hℓ hd p.1 p.2]
      rw [hfun]
      exact continuous_finsetSum _ (fun k _ => (continuous_chiBLb hℓ hd k).pow 2)
    exact hcont.aestronglyMeasurable
  refine (integrable_indicator_fst_pdMu_aux hℓ R C).mono' hmeas ?_
  filter_upwards with p
  have hnn : 0 ≤ kinIntD ℓ d p.1 p.2 := by
    rw [kinIntD_eq hℓ hd p.1 p.2]
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hRC p.1 p.2

end Work.UBBInputs9.B.pd_aux
