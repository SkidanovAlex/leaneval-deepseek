import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_upper
import Submission.Work.BMF.VK.zeta_norm_two_sided
import Submission.Work.BMF.znl.hasDerivAt_log_norm
import Submission.Work.BMF.znl.zeta_bdd_box

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.znl

open Complex Metric Set Filter
open scoped Real Topology

noncomputable section

/-! ## Integrating the log-derivative bound -/

lemma log_zeta_le_of_logDeriv_bound {C₀ H : ℝ} (hH2 : 2 ≤ H)
    (hbd : ∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤
          C₀ * (Real.log (|t| + 3) + 1))
    {x y t : ℝ} (ht : H ≤ |t|) (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) :
    Real.log ‖riemannZeta (((x : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      Real.log ‖riemannZeta (((y : ℂ) + (t : ℂ) * Complex.I))‖ +
        C₀ * (Real.log (|t| + 3) + 1) * (y - x) := by
  have ht2 : (2 : ℝ) ≤ |t| := le_trans hH2 ht
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht2
    norm_num at ht2
  have hlogt : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith [abs_nonneg t])
  set c : ℝ := C₀ * (Real.log (|t| + 3) + 1) with hc
  have hmono : MonotoneOn
      (fun w : ℝ => Real.log ‖riemannZeta (((w : ℂ) + (t : ℂ) * Complex.I))‖ + c * w)
      (Set.Icc 1 2) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 1 2) ?_ ?_ ?_
    · intro w hw
      have hw1 : (1 : ℝ) ≤ w := hw.1
      have hne1 : ((w : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
        intro h
        have him : (((w : ℂ) + (t : ℂ) * Complex.I)).im = 0 := by rw [h]; simp
        simp at him
        exact ht0 him
      have hz : riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by simpa using hw1)
      have hcurve : ContinuousAt (fun w : ℝ => ((w : ℂ) + (t : ℂ) * Complex.I)) w := by
        fun_prop
      have hcontζ : ContinuousAt
          (fun w : ℝ => riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I)) w :=
        ((differentiableAt_riemannZeta hne1).continuousAt).tendsto.comp hcurve.tendsto
      have h1 : ContinuousAt
          (fun w : ℝ => Real.log ‖riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I)‖) w :=
        (Real.continuousAt_log (norm_ne_zero_iff.mpr hz)).tendsto.comp hcontζ.norm.tendsto
      have h2 : ContinuousAt (fun w : ℝ => c * w) w := continuousAt_const.mul continuousAt_id
      exact (h1.add h2).continuousWithinAt
    · rw [interior_Icc]
      intro w hw
      have hw1 : (1 : ℝ) < w := hw.1
      have hne1 : ((w : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hz : riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by simpa using hw1.le)
      have hlin : HasDerivAt (fun y : ℝ => ((y : ℂ) + (t : ℂ) * Complex.I)) 1 w := by
        have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) w := (hasDerivAt_id w).ofReal_comp
        simpa using h1.add_const ((t : ℂ) * Complex.I)
      have hg : HasDerivAt (fun y : ℝ => riemannZeta ((y : ℂ) + (t : ℂ) * Complex.I))
          (deriv riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I) * 1) w :=
        HasDerivAt.comp w ((differentiableAt_riemannZeta hne1).hasDerivAt) hlin
      exact ((hasDerivAt_log_norm hg hz).add
        ((hasDerivAt_id w).const_mul c)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro w hw
      have hw1 : (1 : ℝ) < w := hw.1
      have hw2 : w ≤ 2 := hw.2.le
      have hne1 : ((w : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hz : riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by simpa using hw1.le)
      have hlin : HasDerivAt (fun y : ℝ => ((y : ℂ) + (t : ℂ) * Complex.I)) 1 w := by
        have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) w := (hasDerivAt_id w).ofReal_comp
        simpa using h1.add_const ((t : ℂ) * Complex.I)
      have hg : HasDerivAt (fun y : ℝ => riemannZeta ((y : ℂ) + (t : ℂ) * Complex.I))
          (deriv riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I) * 1) w :=
        HasDerivAt.comp w ((differentiableAt_riemannZeta hne1).hasDerivAt) hlin
      have htot : HasDerivAt
          (fun y : ℝ => Real.log ‖riemannZeta ((y : ℂ) + (t : ℂ) * Complex.I)‖ + c * y)
          (((deriv riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I) * 1) /
            riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I)).re + c * 1) w :=
        (hasDerivAt_log_norm hg hz).add ((hasDerivAt_id w).const_mul c)
      have hderiv : deriv (fun y : ℝ =>
          Real.log ‖riemannZeta ((y : ℂ) + (t : ℂ) * Complex.I)‖ + c * y) w
          = (deriv riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I) /
              riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I)).re + c := by
        rw [htot.deriv]
        simp
      rw [hderiv]
      have hb := hbd t ht w hw1 hw2
      have hneg : ((-deriv riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I)) /
            riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I)).re
          = -(deriv riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I) /
              riemannZeta ((w : ℂ) + (t : ℂ) * Complex.I)).re := by
        rw [neg_div, Complex.neg_re]
      rw [hneg] at hb
      rw [hc]
      linarith
  have hx' : x ∈ Set.Icc (1 : ℝ) 2 := ⟨hx, le_trans hxy hy⟩
  have hy' : y ∈ Set.Icc (1 : ℝ) 2 := ⟨le_trans hx hxy, hy⟩
  have h := hmono hx' hy' hxy
  rw [hc] at h
  linarith

/-- **Upper bound for `ζ` in the strip `1 ≤ Re s ≤ 2`.** There is `C > 0` with
`‖ζ(σ + i t)‖ ≤ C · log(|t| + 3)` for all `1 ≤ σ ≤ 2` and `2 ≤ |t|`.

Proof sketch (the elementary "`ζ(s) = O(log t)` on `Re s ≥ 1`", Titchmarsh Theorem 3.5).
Import `Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_upper`, which gives `C₀ > 0`,
`H ≥ 2` with `Re(ζ'/ζ)(σ+it) ≤ C₀(log(|t|+3)+1)` for `1 < σ ≤ 2`, `H ≤ |t|`.  Let `L = log(|t|+3)`.
* For `σ ≥ 1 + 1/L`: from the Dirichlet series, `‖ζ(σ+it)‖ ≤ ζ(σ) ≤ 1 + 1/(σ-1) ≤ 1 + L`
  (`Mathlib`: `zeta_eq_tsum_one_div_nat_add_one_cpow` + `norm_tsum_le_tsum_norm` + the real
  `ζ(σ) ≤ 1 + 1/(σ-1)`, available in the workspace e.g. as
  `Submission.Work.BMF.zeta_tsum_rpow_le` / `Submission.Work.BMF.riemannZeta_re_le_one_add_inv`).
* For `1 ≤ σ ≤ 1 + 1/L`: writing `f(x) = log‖ζ(x+it)‖` on `(1,2]`, one has
  `f' = Re(ζ'/ζ)(·+it) ≤ C₀(L+1)` and `f(1+1/L) = log‖ζ(1+1/L+it)‖ ≤ log(1+L)`, so integrating
  down from `1+1/L` gives `‖ζ(σ+it)‖ ≤ (1+L)e^{2C₀}`.
* For the bounded range `2 ≤ |t| ≤ H`: `ζ` is continuous on the compact set
  `{1 ≤ σ ≤ 2, 2 ≤ |t| ≤ H}` (the pole `s = 1` has `t = 0`), so `‖ζ‖ ≤ C₁` there.
Take `C := 2·max(e^{2C₀}, C₁/log 5)` (so that `1 + L ≤ 2L` for `t ≥ 2` and the bounded range is
covered by `C log(|t|+3) ≥ C log 5`). -/

theorem zeta_norm_upper_log : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
    ‖riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * Real.log (|t| + 3) := by
  rcases Commons.NumberTheory.Zeta.zeta_logDeriv_re_upper with ⟨C₀, hC₀, H, hH2, hbd⟩
  obtain ⟨A, hA, hbox⟩ := zeta_bdd_box H
  refine ⟨max (2 * Real.exp (2 * C₀)) (A / Real.log 5), ?_, ?_⟩
  · exact lt_max_iff.mpr (Or.inl (by positivity))
  · intro σ t hσ1 hσ2 ht
    have hlog5pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have ht5 : (5 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
    have hLlog5 : Real.log 5 ≤ Real.log (|t| + 3) := Real.log_le_log (by norm_num) ht5
    have hlog5_1 : (1 : ℝ) ≤ Real.log 5 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    have hL1 : (1 : ℝ) ≤ Real.log (|t| + 3) := le_trans hlog5_1 hLlog5
    have hLpos : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith [abs_nonneg t])
    have hLnonneg : 0 ≤ Real.log (|t| + 3) := le_trans zero_le_one hL1
    have h2Cmax : (2 : ℝ) ≤ max (2 * Real.exp (2 * C₀)) (A / Real.log 5) := by
      have h1 : (2 : ℝ) ≤ 2 * Real.exp (2 * C₀) := by
        nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * C₀)]
      exact le_trans h1 (le_max_left (2 * Real.exp (2 * C₀)) (A / Real.log 5))
    by_cases hH : H ≤ |t|
    · -- the log-derivative bound applies
      by_cases hcase : 1 + 1 / Real.log (|t| + 3) ≤ σ
      · -- `σ` is far enough to the right: the Dirichlet series bound suffices
        have hσgt : (1 : ℝ) < σ := by
          have : 0 < 1 / Real.log (|t| + 3) := div_pos one_pos hLpos
          linarith
        have hinv : 1 / (σ - 1) ≤ Real.log (|t| + 3) := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < σ - 1)]
          have hle : 1 / Real.log (|t| + 3) ≤ σ - 1 := by linarith
          calc (1 : ℝ) = Real.log (|t| + 3) * (1 / Real.log (|t| + 3)) := by
                field_simp
            _ ≤ Real.log (|t| + 3) * (σ - 1) := mul_le_mul_of_nonneg_left hle hLpos.le
        have hzb := (Work.BMF.VK.zeta_norm_two_sided
          (s := ((σ : ℂ) + (t : ℂ) * Complex.I)) (by simpa using hσgt)).1
        have hsre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
        rw [hsre] at hzb
        calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 + 1 / (σ - 1) := hzb
          _ ≤ 1 + Real.log (|t| + 3) := by linarith
          _ ≤ 2 * Real.log (|t| + 3) := by linarith
          _ ≤ max (2 * Real.exp (2 * C₀)) (A / Real.log 5) * Real.log (|t| + 3) :=
              mul_le_mul_of_nonneg_right h2Cmax hLnonneg
      · -- `σ` is close to `1`: integrate the log-derivative bound
        have hσle : σ ≤ 1 + 1 / Real.log (|t| + 3) := le_of_lt (lt_of_not_ge hcase)
        have hy2 : 1 + 1 / Real.log (|t| + 3) ≤ 2 := by
          have : 1 / Real.log (|t| + 3) ≤ 1 := by
            rw [div_le_one hLpos]
            exact hL1
          linarith
        have hygt : (1 : ℝ) < 1 + 1 / Real.log (|t| + 3) := by
          have : 0 < 1 / Real.log (|t| + 3) := div_pos one_pos hLpos
          linarith
        have hmain := log_zeta_le_of_logDeriv_bound (C₀ := C₀) (H := H) hH2 hbd
          (x := σ) (y := 1 + 1 / Real.log (|t| + 3)) hH hσ1 hσle hy2
        have hzy : ‖riemannZeta (((1 + 1 / Real.log (|t| + 3) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I)‖ ≤ 1 + Real.log (|t| + 3) := by
          have hs1 : (1 : ℝ) < (((1 + 1 / Real.log (|t| + 3) : ℝ) : ℂ) +
              (t : ℂ) * Complex.I).re := by
            simpa using hygt
          have h := (Work.BMF.VK.zeta_norm_two_sided
            (s := (((1 + 1 / Real.log (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) hs1).1
          have hre : ((((1 + 1 / Real.log (|t| + 3) : ℝ) : ℂ) +
              (t : ℂ) * Complex.I).re - 1) = 1 / Real.log (|t| + 3) := by simp
          rw [hre, one_div_one_div] at h
          exact h
        have hlogle : Real.log ‖riemannZeta (((1 + 1 / Real.log (|t| + 3) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I)‖ ≤ Real.log (1 + Real.log (|t| + 3)) := by
          apply Real.log_le_log
          · exact norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hygt))
          · exact hzy
        have hstep : C₀ * (Real.log (|t| + 3) + 1) * (1 + 1 / Real.log (|t| + 3) - σ) ≤ 2 * C₀ := by
          have hyx : 1 + 1 / Real.log (|t| + 3) - σ ≤ 1 / Real.log (|t| + 3) := by linarith
          have h2 : (Real.log (|t| + 3) + 1) * (1 / Real.log (|t| + 3)) ≤ 2 := by
            rw [mul_one_div, div_le_iff₀ hLpos]
            linarith
          calc C₀ * (Real.log (|t| + 3) + 1) * (1 + 1 / Real.log (|t| + 3) - σ)
              ≤ C₀ * (Real.log (|t| + 3) + 1) * (1 / Real.log (|t| + 3)) := by
                apply mul_le_mul_of_nonneg_left hyx
                positivity
            _ = C₀ * ((Real.log (|t| + 3) + 1) * (1 / Real.log (|t| + 3))) := by ring
            _ ≤ C₀ * 2 := mul_le_mul_of_nonneg_left h2 hC₀.le
            _ = 2 * C₀ := by ring
        have hkey : Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            Real.log (1 + Real.log (|t| + 3)) + 2 * C₀ := by linarith
        have hpos : 0 < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
          norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simpa using hσ1))
        calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            = Real.exp (Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) :=
              (Real.exp_log hpos).symm
          _ ≤ Real.exp (Real.log (1 + Real.log (|t| + 3)) + 2 * C₀) := Real.exp_le_exp.mpr hkey
          _ = (1 + Real.log (|t| + 3)) * Real.exp (2 * C₀) := by
              rw [Real.exp_add, Real.exp_log (by linarith)]
          _ ≤ (2 * Real.log (|t| + 3)) * Real.exp (2 * C₀) := by
              exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
          _ = (2 * Real.exp (2 * C₀)) * Real.log (|t| + 3) := by ring
          _ ≤ max (2 * Real.exp (2 * C₀)) (A / Real.log 5) * Real.log (|t| + 3) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hLnonneg
    · -- the bounded range `2 ≤ |t| ≤ H`
      have htle : |t| ≤ H := le_of_lt (lt_of_not_ge hH)
      have h1 := hbox σ t hσ1 hσ2 ht htle
      have hAle : A ≤ (A / Real.log 5) * Real.log (|t| + 3) := by
        calc A = (A / Real.log 5) * Real.log 5 := (div_mul_cancel₀ A (ne_of_gt hlog5pos)).symm
          _ ≤ (A / Real.log 5) * Real.log (|t| + 3) :=
              mul_le_mul_of_nonneg_left hLlog5 (div_nonneg hA.le hlog5pos.le)
      calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A := h1
        _ ≤ (A / Real.log 5) * Real.log (|t| + 3) := hAle
        _ ≤ max (2 * Real.exp (2 * C₀)) (A / Real.log 5) * Real.log (|t| + 3) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hLnonneg

end

end Work.BMF.znl
