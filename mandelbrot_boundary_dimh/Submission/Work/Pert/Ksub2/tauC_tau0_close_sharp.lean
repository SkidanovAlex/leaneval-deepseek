import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Ksub2.norm_exp_sub_one_sub_id_le_two
import Submission.Work.Pert.Ksub2.tauC_tau0_ratio_identity

namespace Work.Pert.Ksub2

set_option linter.unusedVariables false

/-!
# Sharp `τ_f ∘ τ₀` closeness (quantitative first-order form)

`τ_f = Work.Pert.tauC σ α` is the perturbed chart `w ↦ σ/(1 - e^{-2πiαw})` and `τ₀ y = -1/y`
(`MandelDim.tau0`).  Under the normalisation `1 - σ u(0) = e^{2πiα}` of (A.1.5), the composition
`τ_f ∘ τ₀` inverts `τ₀` to *first order*, and here we make the two first-order terms explicit:
the deviation of `u(0)` from `1`, and `α` itself.

Writing `w = 2πiα`, `z = w/y = 2πiα/y`, `u₀ = u 0`, the two basic facts are

* `σ = (1 - e^w)/u₀`, hence `τ_f(τ₀ y) = σ/(1 - e^z)`, and the exact identity
  `σ/(1 - e^z) = y·A/(u₀ B)` with `A = (e^w-1)/w`, `B = (e^z-1)/z`
  (`Work.Pert.Ksub2.tauC_tau0_ratio_identity`);
* on `‖z‖ ≤ 1/2` the quadratic Taylor remainders bound `‖A - 1‖ ≤ (3/2)‖w‖`,
  `‖B - 1‖ ≤ ‖z‖`, so that `‖B‖ ≥ 1/2`.

The hypothesis of the sharp form is exactly the *regime* hypothesis `‖z‖ ≤ 1/2` (the gate
`‖α/y‖ ≲ 1`), in which no lattice separation hypothesis on `α/y` is needed. -/

theorem tauC_tau0_close_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : ℂ → ℂ} {σ α y : ℂ},
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      α ≠ 0 → ‖u 0 - 1‖ ≤ 1 / 4 → ‖α‖ ≤ 1 / 4 →
      ‖2 * Real.pi * Complex.I * α / y‖ ≤ 1 / 2 →
      ‖Work.Pert.tauC σ α (MandelDim.tau0 y) - y‖
        ≤ C * (‖y‖ * ‖u 0 - 1‖ + ‖α‖ * (1 + ‖y‖)) := by
  refine ⟨32, by norm_num, ?_⟩
  intro u σ α y hnorm hα0 hu0 hα hzle
  by_cases hy : y = 0
  · subst hy
    have h1 : MandelDim.tau0 (0 : ℂ) = 0 := by simp [MandelDim.tau0]
    have h2 : Work.Pert.tauC σ α 0 = 0 := by simp [Work.Pert.tauC]
    rw [h1, h2, sub_zero, norm_zero]
    positivity
  · -- `y ≠ 0`: the first-order regime
    set w : ℂ := 2 * Real.pi * Complex.I * α with hwdef
    set z : ℂ := 2 * Real.pi * Complex.I * α / y with hzdef
    set u0 : ℂ := u 0 with hu0def
    have hzn : ‖z‖ = ‖w‖ / ‖y‖ := by rw [hzdef, norm_div, ← hwdef]
    have hwn : ‖w‖ = 2 * Real.pi * ‖α‖ := by
      rw [hwdef, norm_mul, norm_mul, norm_mul]
      norm_num
    have hwle : ‖w‖ ≤ Real.pi / 2 := by rw [hwn]; nlinarith [Real.pi_pos, hα]
    have hw2 : ‖w‖ ≤ 2 := by linarith [Real.pi_lt_four]
    have hw0 : w ≠ 0 := by
      rw [hwdef]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hα0
    have hz0 : z ≠ 0 := by rw [hzdef]; exact div_ne_zero hw0 hy
    have hu0le : ‖u0 - 1‖ ≤ 1 / 4 := hu0
    have hu0ge : (3 / 4 : ℝ) ≤ ‖u0‖ := by
      have h := norm_sub_norm_le (1 : ℂ) u0
      simp only [norm_one] at h
      linarith [h, hu0le, norm_sub_rev (1 : ℂ) u0]
    have hu0ne : u0 ≠ 0 := by
      intro h; rw [h, norm_zero] at hu0ge; norm_num at hu0ge
    have hσu : σ * u0 = 1 - Complex.exp w := by
      rw [hu0def, hwdef]
      linear_combination -hnorm
    have hσeq : σ = (1 - Complex.exp w) / u0 := (eq_div_iff hu0ne).mpr hσu
    have hzle' : ‖z‖ ≤ 1 / 2 := by rw [hzdef]; exact hzle
    -- the two `φ`-ratios `A = (e^w - 1)/w`, `B = (e^z - 1)/z`
    set A : ℂ := (Complex.exp w - 1) / w with hAdef
    set B : ℂ := (Complex.exp z - 1) / z with hBdef
    have hA1 : ‖A - 1‖ ≤ 3 / 2 * ‖w‖ := by
      have hq : ‖Complex.exp w - 1 - w‖ ≤ 3 / 2 * ‖w‖ ^ 2 :=
        norm_exp_sub_one_sub_id_le_two hw2
      rw [hAdef, div_sub_one hw0, norm_div, div_le_iff₀ (norm_pos_iff.mpr hw0)]
      nlinarith [hq, norm_nonneg w]
    have hB1 : ‖B - 1‖ ≤ ‖z‖ := by
      have hq : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 :=
        Complex.norm_exp_sub_one_sub_id_le (by linarith [hzle'])
      rw [hBdef, div_sub_one hz0, norm_div, div_le_iff₀ (norm_pos_iff.mpr hz0)]
      nlinarith [hq, norm_nonneg z]
    have hBge : (1 / 2 : ℝ) ≤ ‖B‖ := by
      have h := norm_sub_norm_le (1 : ℂ) B
      simp only [norm_one] at h
      have h2 : ‖(1 : ℂ) - B‖ ≤ 1 / 2 := by
        rw [norm_sub_rev]; linarith [hB1, hzle']
      linarith
    have hBne : B ≠ 0 := by
      intro h; rw [h, norm_zero] at hBge; norm_num at hBge
    have he : Complex.exp z ≠ 1 := by
      intro h
      have hzB : (1 : ℂ) - Complex.exp z = -(z * B) := by rw [hBdef]; field_simp; ring
      rw [h, sub_self] at hzB
      exact (by simp [mul_ne_zero hz0 hBne] : -(z * B) ≠ 0) hzB.symm
    -- the exact chart identity
    have hkey : σ / (1 - Complex.exp z) - y = y * (A / (u0 * B) - 1) :=
      tauC_tau0_ratio_identity (u0 := u0) (σ := σ) (α := α) (y := y) hσeq hα0 hy hu0ne he
    -- the three elementary bounds
    have hAB : ‖A - B‖ ≤ 3 / 2 * ‖w‖ + ‖z‖ := by
      have hsplit : A - B = (A - 1) - (B - 1) := by ring
      rw [hsplit]
      linarith [norm_sub_le (A - 1) (B - 1), hA1, hB1]
    have hdenge : (3 / 8 : ℝ) ≤ ‖u0 * B‖ := by
      rw [norm_mul]; nlinarith [hu0ge, hBge]
    have hratio : ‖A / (u0 * B) - 1‖ ≤ 8 / 3 * (3 / 2 * ‖w‖ + ‖z‖) + 4 / 3 * ‖u0 - 1‖ := by
      have hsplit : A / (u0 * B) - 1 = (A - B) / (u0 * B) - (u0 - 1) / u0 := by
        field_simp
        ring
      rw [hsplit]
      have h1 : ‖(A - B) / (u0 * B)‖ ≤ (3 / 2 * ‖w‖ + ‖z‖) / (3 / 8) := by
        rw [norm_div]
        exact div_le_div₀ (by positivity) hAB (by norm_num) hdenge
      have h2 : ‖(u0 - 1) / u0‖ ≤ 4 / 3 * ‖u0 - 1‖ := by
        rw [norm_div, div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg (u0 - 1)]
      have h3 := norm_sub_le ((A - B) / (u0 * B)) ((u0 - 1) / u0)
      have h4 : (3 / 2 * ‖w‖ + ‖z‖) / (3 / 8) = 8 / 3 * (3 / 2 * ‖w‖ + ‖z‖) := by ring
      linarith [h3, h1, h2, h4]
    -- unfold the chart
    have htauC : Work.Pert.tauC σ α (MandelDim.tau0 y) = σ / (1 - Complex.exp z) := by
      rw [hzdef]
      rw [Work.Pert.tauC, MandelDim.tau0]
      congr 2
      field_simp
    rw [htauC, hkey]
    calc ‖y * (A / (u0 * B) - 1)‖ = ‖y‖ * ‖A / (u0 * B) - 1‖ := norm_mul _ _
      _ ≤ ‖y‖ * (8 / 3 * (3 / 2 * ‖w‖ + ‖z‖) + 4 / 3 * ‖u0 - 1‖) :=
          mul_le_mul_of_nonneg_left hratio (norm_nonneg y)
      _ = 4 * ‖w‖ * ‖y‖ + 8 / 3 * ‖w‖ + 4 / 3 * ‖y‖ * ‖u0 - 1‖ := by
          rw [hzn]
          field_simp
          ring
      _ ≤ 32 * (‖y‖ * ‖u0 - 1‖ + ‖α‖ * (1 + ‖y‖)) := by
          rw [hwn]
          have hab : 0 ≤ ‖α‖ * ‖y‖ := mul_nonneg (norm_nonneg α) (norm_nonneg y)
          nlinarith [Real.pi_lt_four, Real.pi_pos, norm_nonneg α, norm_nonneg y,
            norm_nonneg (u0 - 1), hab]

end Work.Pert.Ksub2
