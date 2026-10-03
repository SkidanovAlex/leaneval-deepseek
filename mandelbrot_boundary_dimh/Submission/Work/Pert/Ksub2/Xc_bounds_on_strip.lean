import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Parab.inversion.exists_mul_log_lt

/-!
# `Work.Pert.Ksub2.Xc_bounds_on_strip`

The datum's curve `u ↦ Xc d u = τ₀ (φ₀ u)` is close to the identity on the deep strip
`Dstrip M T = {-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}` at the *linear* scale: for `M` large enough
(depending only on the datum), and for every `T ≤ M/160`,

* `‖Xc d (-M) + M‖ ≤ M/320`, and
* `‖Xc d u - u‖ ≤ M/160` for every `u` in the strip.

The only input is the two-term asymptotic of the Fatou coordinate (`d.φ_asymp`),
`τ₀ (φ₀ w) = w + a log(-w) + b + o(1)` on the repelling sector `QLeft ξ₀`: on the strip the
logarithmic term is `O(log M)`, and `log M ≤ M / (640(‖a‖+1))` for `M` beyond a threshold
(`Work.Parab.inversion.exists_mul_log_lt_aux`, the elementary `log = o(id)` estimate).  All strip
points have `M ≤ ‖u‖ ≤ 2M` and lie in `QLeft ξ₀` (`Dstrip_sub_QLeft`), so the asymptotic with
`ε = 1` applies, and the strip's *diameter* is `T + 1 ≤ M/160 + 1 ≪ M` — the whole estimate is
linear in the depth `M`, which is exactly what the perturbation argument needs.
-/

namespace Work.Pert.Ksub2

open Complex Metric

theorem Xc_bounds_on_strip {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ T : ℝ, T ≤ M / 160 →
      ‖Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ)‖ ≤ M / 320 ∧
      (∀ u ∈ Dstrip M T, ‖Work.Pert.Xc d u - u‖ ≤ M / 160) := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨R_A, hR_A⟩ := hasym 1 one_pos
  -- the `log = o(id)` threshold, in the precise form needed here
  obtain ⟨R₁, -, hR₁⟩ :=
    Work.Parab.inversion.exists_mul_log_lt_aux (a := ‖a‖) (b := 1 + ‖a‖ * Real.pi + ‖b‖)
      (c := 1 / 320) (by norm_num)
  have hev : ∀ᶠ M : ℝ in Filter.atTop,
      2 ≤ M ∧ R_A + 1 ≤ M ∧ d.ξ₀ + 1 ≤ M ∧ R₁ ≤ M := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), Filter.eventually_ge_atTop (R_A + 1),
      Filter.eventually_ge_atTop (d.ξ₀ + 1), Filter.eventually_ge_atTop R₁] with M h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max M₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro M hM T hT
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) hM
  obtain ⟨hM2, hMRA, hMξ, hMR1⟩ := hM₁ M hM1
  have hMpos : 0 < M := by linarith
  -- the uniform estimate on any sector point of size between `M` and `2M`
  have hgen : ∀ u : ℂ, u ∈ MandelDim.QLeft d.ξ₀ → M ≤ ‖u‖ → ‖u‖ ≤ 2 * M →
      ‖Work.Pert.Xc d u - u‖ ≤ M / 320 := by
    intro u huQ hMle hule
    have hMnorm : R_A < ‖u‖ := by linarith
    have hasy := hR_A u huQ hMnorm
    have hlog : Real.log ‖u‖ ≤ Real.log (2 * M) := by
      apply Real.log_le_log
      · linarith
      · exact hule
    have hclog : ‖Complex.log (-u)‖ ≤ Real.log ‖u‖ + Real.pi := by
      have h := Work.Pert.norm_clog_le (-u)
      rw [norm_neg, abs_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ ‖u‖))] at h
      exact h
    have hAb : ‖a * Complex.log (-u) + b‖ ≤
        ‖a‖ * Real.log ‖u‖ + (‖a‖ * Real.pi + ‖b‖) := by
      calc ‖a * Complex.log (-u) + b‖ ≤ ‖a * Complex.log (-u)‖ + ‖b‖ := norm_add_le _ _
        _ = ‖a‖ * ‖Complex.log (-u)‖ + ‖b‖ := by rw [norm_mul]
        _ ≤ ‖a‖ * (Real.log ‖u‖ + Real.pi) + ‖b‖ := by
              have hmm := mul_le_mul_of_nonneg_left hclog (norm_nonneg a)
              linarith
        _ = ‖a‖ * Real.log ‖u‖ + (‖a‖ * Real.pi + ‖b‖) := by ring
    have hsplit : Work.Pert.Xc d u - u =
        (MandelDim.tau0 (d.φ u) - (u + a * Complex.log (-u) + b)) +
          (a * Complex.log (-u) + b) := by
      simp only [Work.Pert.Xc]; ring
    have htri : ‖Work.Pert.Xc d u - u‖ ≤
        ‖MandelDim.tau0 (d.φ u) - (u + a * Complex.log (-u) + b)‖ +
          ‖a * Complex.log (-u) + b‖ := by
      rw [hsplit]; exact norm_add_le _ _
    have hkey := hR₁ M hMR1
    have hlogmul : ‖a‖ * Real.log ‖u‖ ≤ ‖a‖ * Real.log (2 * M) :=
      mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
    have h320 : (1 / 320 : ℝ) * M = M / 320 := by ring
    rw [h320] at hkey
    linarith [htri, hasy, hAb, hlogmul, hkey]
  constructor
  · -- the sharp bound at the real point `-M`
    have hmem : (((-M : ℝ)) : ℂ) ∈ Work.Pert.Dstrip M 0 := by
      simp only [Work.Pert.Dstrip, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im,
        abs_zero]
      exact ⟨by linarith, by linarith, le_refl 0⟩
    have hQ : (((-M : ℝ)) : ℂ) ∈ MandelDim.QLeft d.ξ₀ :=
      Work.Pert.Dstrip_sub_QLeft hMξ hmem
    have hn : ‖(((-M : ℝ)) : ℂ)‖ = M := by
      simp [abs_of_nonneg (by linarith : (0 : ℝ) ≤ M)]
    exact hgen _ hQ (by rw [hn]) (by rw [hn]; linarith)
  · -- the strip
    intro u hu
    have hQ : u ∈ MandelDim.QLeft d.ξ₀ := Work.Pert.Dstrip_sub_QLeft hMξ hu
    have hle : M ≤ ‖u‖ := by
      have h1 : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
      have h2 : |u.re| = -u.re := abs_of_nonpos (by linarith [hu.2.1])
      linarith [hu.2.1]
    have hule : ‖u‖ ≤ 2 * M := by
      have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      have h2 : |u.re| ≤ M + 1 := by
        apply abs_le.mpr; constructor <;> linarith [hu.1, hu.2.1]
      have h3 : |u.im| ≤ T := hu.2.2
      linarith
    have h := hgen u hQ hle hule
    linarith

end Work.Pert.Ksub2
