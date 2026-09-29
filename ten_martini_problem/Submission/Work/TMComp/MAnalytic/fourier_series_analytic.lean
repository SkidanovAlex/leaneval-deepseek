import Mathlib

namespace Work.TMComp.MAnalytic

/-- Summability over `ℤ` of `k ↦ exp (-(a * |k|))` for `a > 0`. -/
lemma summable_int_exp_neg_abs_mul {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℤ => Real.exp (-(a * |(k : ℝ)|))) := by
  have hbase : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hgeo : Summable (fun k : ℤ => (Real.exp (-a)) ^ k.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · refine (summable_geometric_of_lt_one (Real.exp_pos (-a)).le hbase).congr (fun n => ?_)
      simp [Int.natAbs_natCast]
    · refine (summable_geometric_of_lt_one (Real.exp_pos (-a)).le hbase).congr (fun n => ?_)
      simp [Int.natAbs_neg, Int.natAbs_natCast]
  refine hgeo.congr (fun k => ?_)
  rw [show -(a * |(k : ℝ)|) = (k.natAbs : ℝ) * (-a) by
        rw [← Int.cast_abs, ← Int.natCast_natAbs k, Int.cast_natCast]; ring,
      Real.exp_nat_mul]

theorem fourier_series_analytic {c : ℤ → ℂ} {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hdec : ∀ k : ℤ, ‖c k‖ ≤ B * Real.exp (-(2 * Real.pi * |(k : ℝ)| * ρ))) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∑' k : ℤ, c k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * z))
      {z : ℂ | |z.im| < ρ} := by
  intro z hz
  have hz' : |z.im| < ρ := hz
  -- pick an intermediate width `ρ'` with `|z.im| < ρ' < ρ`
  obtain ⟨ρ', hzρ', hρ'ρ, hρ'pos⟩ : ∃ ρ', |z.im| < ρ' ∧ ρ' < ρ ∧ 0 < ρ' :=
    ⟨(|z.im| + ρ) / 2, by linarith [abs_nonneg z.im],
      by linarith, by linarith [abs_nonneg z.im]⟩
  have hU : IsOpen {w : ℂ | |w.im| < ρ'} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  -- each term is entire
  have hterm : ∀ k : ℤ, DifferentiableOn ℂ
      (fun w : ℂ => c k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w))
      {w : ℂ | |w.im| < ρ'} := by
    intro k
    exact ((differentiable_const (c k)).mul
      (Complex.differentiable_exp.comp (by fun_prop))).differentiableOn
  -- uniform bound on the closed sub-strip
  have hbound : ∀ k : ℤ, ∀ w ∈ {w : ℂ | |w.im| < ρ'},
      ‖c k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)‖
        ≤ B * Real.exp (-(2 * Real.pi * (ρ - ρ') * |(k : ℝ)|)) := by
    intro k w hw
    have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)‖
        = Real.exp (-(2 * Real.pi * (k : ℝ) * w.im)) := by
      have h1 : 2 * Real.pi * Complex.I * (k : ℂ) * w
          = (((2 * Real.pi * (k : ℝ) : ℝ)) : ℂ) * (Complex.I * w) := by
        push_cast; ring
      have h2 : ((((2 * Real.pi * (k : ℝ) : ℝ)) : ℂ) * (Complex.I * w)).re
          = -(2 * Real.pi * (k : ℝ) * w.im) := by
        rw [Complex.re_ofReal_mul, mul_comm Complex.I w, Complex.mul_I_re]
        ring
      rw [Complex.norm_exp, h1, h2]
    have hle : Real.exp (-(2 * Real.pi * (k : ℝ) * w.im))
        ≤ Real.exp (2 * Real.pi * |(k : ℝ)| * ρ') := by
      apply Real.exp_le_exp.mpr
      calc -(2 * Real.pi * (k : ℝ) * w.im) ≤ |2 * Real.pi * (k : ℝ) * w.im| := neg_le_abs _
        _ = 2 * Real.pi * |(k : ℝ)| * |w.im| := by
              rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        _ ≤ 2 * Real.pi * |(k : ℝ)| * ρ' :=
              mul_le_mul_of_nonneg_left hw.le (by positivity)
    calc ‖c k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)‖
        = ‖c k‖ * Real.exp (-(2 * Real.pi * (k : ℝ) * w.im)) := by rw [norm_mul, hexp]
      _ ≤ (B * Real.exp (-(2 * Real.pi * |(k : ℝ)| * ρ))) * Real.exp (2 * Real.pi * |(k : ℝ)| * ρ') :=
            mul_le_mul (hdec k) hle (Real.exp_pos _).le (mul_nonneg hB (Real.exp_pos _).le)
      _ = B * Real.exp (-(2 * Real.pi * (ρ - ρ') * |(k : ℝ)|)) := by
            rw [mul_assoc, ← Real.exp_add,
              show -(2 * Real.pi * |(k : ℝ)| * ρ) + 2 * Real.pi * |(k : ℝ)| * ρ'
                = -(2 * Real.pi * (ρ - ρ') * |(k : ℝ)|) by ring]
  have hu : Summable (fun k : ℤ => B * Real.exp (-(2 * Real.pi * (ρ - ρ') * |(k : ℝ)|))) :=
    Summable.mul_left B (summable_int_exp_neg_abs_mul (a := 2 * Real.pi * (ρ - ρ'))
      (mul_pos (by linarith [Real.pi_pos]) (by linarith)))
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => ∑' k : ℤ, c k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w))
      {w : ℂ | |w.im| < ρ'} :=
    Complex.differentiableOn_tsum_of_summable_norm hu hterm hU hbound
  exact hdiff.analyticAt (hU.mem_nhds (by simpa using hzρ'))

end Work.TMComp.MAnalytic
