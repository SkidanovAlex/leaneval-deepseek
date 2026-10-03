import Mathlib
import Submission.Work.Horn.FatouQ.Xfun_basic

namespace Work.Horn.FatouQ

open Work.Horn.Flower

noncomputable section

/-- The logarithmic part of the approximate Fatou coordinate grows at most like
`‖w‖ ^ (1/2)`.  Indeed, if `w = chartQ q a (zBranch q a j w)` then `z ^ q = cc q a / w`, hence
`z ^ q / cc q a = w⁻¹` and `Lbranch q a z = (log w⁻¹ + log (cc q a)) / q`; the fundamental
estimate `‖log u‖ ≤ |log ‖u‖| + π` together with `|log r| ≤ 2 r ^ (1/2) + |log M|` on `r ≥ M`
then bounds the logarithm by a constant times `‖w‖ ^ (1/2)` plus a constant. -/
theorem Xfun_log_bound {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hchart : ∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w) :
    ∃ C0 C1 θ : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ w : ℂ, M < w.re →
      ‖(Work.Horn.FatouQ.gcoef f q a q + ((q : ℂ) + 1) / 2) *
          Work.Horn.FatouQ.Lbranch q a (Work.Horn.FatouQ.zBranch q a j w)‖ ≤ C0 * ‖w‖ ^ θ + C1 := by
  have hcc : cc q a ≠ 0 := hd.hgeo.cc_ne_zero
  have hq : 0 < q := j.pos
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  set A : ℝ := ‖gcoef f q a q + ((q : ℂ) + 1) / 2‖ with hAdef
  have hA0 : 0 ≤ A := norm_nonneg _
  set Kc : ℝ := ‖Complex.log (cc q a)‖ with hKcdef
  have hKc0 : 0 ≤ Kc := norm_nonneg _
  set B : ℝ := |Real.log M| + Real.pi + Kc with hBdef
  refine ⟨2 * A / (q:ℝ), A * B / (q:ℝ), 1/2, ?_, ?_, by norm_num, by norm_num, ?_⟩
  · positivity
  · positivity
  · intro w hw
    have hw0 : 0 < ‖w‖ := lt_of_lt_of_le (lt_trans hd.hM hw) (Complex.re_le_norm w)
    have hMle : M ≤ ‖w‖ := le_trans (le_of_lt hw) (Complex.re_le_norm w)
    have hzq : (zBranch q a j w)^q = cc q a / w := zBranch_pow_of_chart j hd.hM hw (hchart w hw)
    have hL : Lbranch q a (zBranch q a j w) =
        (Complex.log w⁻¹ + Complex.log (cc q a)) / (q:ℂ) := by
      rw [Lbranch, hzq]
      congr 2
      rw [div_div, mul_comm w (cc q a), ← div_div, div_self hcc, one_div]
    have h1 : ‖Complex.log w⁻¹ + Complex.log (cc q a)‖ ≤ |Real.log ‖w‖| + Real.pi + Kc := by
      have h1a : ‖Complex.log w⁻¹‖ ≤ |Real.log ‖w‖| + Real.pi := by
        have := norm_log_le w⁻¹
        rwa [norm_inv, Real.log_inv, abs_neg] at this
      calc ‖Complex.log w⁻¹ + Complex.log (cc q a)‖
          ≤ ‖Complex.log w⁻¹‖ + ‖Complex.log (cc q a)‖ := norm_add_le _ _
        _ ≤ (|Real.log ‖w‖| + Real.pi) + Kc := add_le_add h1a (le_of_eq hKcdef)
        _ = |Real.log ‖w‖| + Real.pi + Kc := by ring
    have h2 : ‖Lbranch q a (zBranch q a j w)‖ ≤ (2 * ‖w‖ ^ ((1:ℝ)/2) + B) / (q:ℝ) := by
      rw [hL, norm_div, Complex.norm_natCast]
      have h3 : |Real.log ‖w‖| ≤ 2 * ‖w‖ ^ ((1:ℝ)/2) + |Real.log M| :=
        abs_log_le_rpow hd.hM hMle
      have h3' : |Real.log ‖w‖| + Real.pi + Kc ≤ 2 * ‖w‖ ^ ((1:ℝ)/2) + B := by
        rw [hBdef]; linarith
      have hdiv := div_le_div_of_nonneg_right h1 hqR.le
      calc (‖Complex.log w⁻¹ + Complex.log (cc q a)‖) / (q:ℝ)
          ≤ (|Real.log ‖w‖| + Real.pi + Kc) / (q:ℝ) := hdiv
        _ ≤ (2 * ‖w‖ ^ ((1:ℝ)/2) + B) / (q:ℝ) :=
              div_le_div_of_nonneg_right h3' hqR.le
    calc ‖(gcoef f q a q + ((q : ℂ) + 1) / 2) * Lbranch q a (zBranch q a j w)‖
        = A * ‖Lbranch q a (zBranch q a j w)‖ := by rw [norm_mul, ← hAdef]
      _ ≤ A * ((2 * ‖w‖ ^ ((1:ℝ)/2) + B) / (q:ℝ)) := mul_le_mul_of_nonneg_left h2 hA0
      _ = 2 * A / (q:ℝ) * ‖w‖ ^ ((1:ℝ)/2) + A * B / (q:ℝ) := by ring

end

end Work.Horn.FatouQ
