import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.psiTail_ge_of_RH

namespace Work.RHContract.Nonvacuity

open Filter

/-- **The analytic core.**  The lower-bound expression `E(x)` produced by
`Work.RHContract.A.psiTail_ge_of_RH` decays like `x^{-1/2}/log x`, hence is eventually
*strictly smaller* than `2 x^{-β}` for every fixed `β < 1/2`.  This is the quantitative
content of "`psiTail` cannot oscillate down to `-2x^{-β}` under RH". -/
private lemma eventually_bound (B β : ℝ) (hβ : β < 1 / 2) :
    ∀ᶠ x in atTop,
      (B * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
          + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x)
        / (Real.sqrt x * Real.log x) < 2 * x ^ (-β) := by
  have hδ : 0 < 1 / 2 - β := by linarith
  have htend : Tendsto (fun x : ℝ => x ^ (1 / 2 - β) * Real.log x) atTop atTop :=
    (tendsto_rpow_atTop hδ).atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hevpow : ∀ᶠ x in atTop, (16 * |B| + Real.log (2 * Real.pi) + 1) / 2
      < x ^ (1 / 2 - β) * Real.log x := htend.eventually_gt_atTop _
  have hev3 : ∀ᶠ x in atTop, (3 : ℝ) ≤ x := eventually_ge_atTop 3
  filter_upwards [hevpow, hev3] with x hpow hx3
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have hlog0 : 0 < Real.log x := lt_of_lt_of_le one_pos hlog1
  have hsqrt1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
  have hsqrt0 : 0 < Real.sqrt x := lt_of_lt_of_le one_pos hsqrt1
  have hden : 0 < Real.sqrt x * Real.log x := mul_pos hsqrt0 hlog0
  have hfact0 : 0 ≤ 5 + 7 / Real.log x + 4 / (Real.log x) ^ 2 := by
    have h1 : 0 ≤ 7 / Real.log x := by positivity
    have h2 : 0 ≤ 4 / (Real.log x) ^ 2 := by positivity
    linarith
  have hfact : 5 + 7 / Real.log x + 4 / (Real.log x) ^ 2 ≤ 16 := by
    have h7 : 7 / Real.log x ≤ 7 := by rw [div_le_iff₀ hlog0]; linarith
    have h4 : 4 / (Real.log x) ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hlog1]
    linarith
  have hBle : B * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2) ≤ |B| * 16 :=
    calc B * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        ≤ |B| * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self B) hfact0
      _ ≤ |B| * 16 := mul_le_mul_of_nonneg_left hfact (abs_nonneg B)
  have hlog2pi0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have ht2 : Real.log (2 * Real.pi) / Real.sqrt x ≤ Real.log (2 * Real.pi) := by
    rw [div_le_iff₀ hsqrt0]; nlinarith [hlog2pi0, hsqrt1]
  have ht3 : 1 / x ≤ 1 := by rw [div_le_one hx0]; linarith
  have hnum : B * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
      + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x
      ≤ 16 * |B| + Real.log (2 * Real.pi) + 1 := by linarith
  have hE : (B * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x)
        / (Real.sqrt x * Real.log x)
      ≤ (16 * |B| + Real.log (2 * Real.pi) + 1) / (Real.sqrt x * Real.log x) :=
    div_le_div_of_nonneg_right hnum hden.le
  have hKlt : 16 * |B| + Real.log (2 * Real.pi) + 1
      < 2 * (x ^ (1 / 2 - β) * Real.log x) := by linarith
  have hdivlt : (16 * |B| + Real.log (2 * Real.pi) + 1) / (Real.sqrt x * Real.log x)
      < 2 * x ^ (-β) := by
    rw [div_lt_iff₀ hden]
    have hpoweq : x ^ (-β) * (Real.sqrt x * Real.log x) = x ^ (1 / 2 - β) * Real.log x := by
      rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hx0]
      ring_nf
    rw [show 2 * x ^ (-β) * (Real.sqrt x * Real.log x)
        = 2 * (x ^ (-β) * (Real.sqrt x * Real.log x)) from by ring, hpoweq]
    exact hKlt
  exact lt_of_le_of_lt hE hdivlt

/-- Under RH the Erdős–Landau `J`-tail does not oscillate down to `-2x^{-β}` for any
`β < 1/2`; equivalently `PsiTailOscillation` fails. -/
theorem psiTail_not_oscillation_of_RH (h : RiemannHypothesis) :
    ¬ Work.RHContract.PsiTailOscillation := by
  intro hosc
  obtain ⟨β, _hβ0, hβ, hfreq⟩ := hosc
  have hev := eventually_bound (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) β hβ
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  obtain ⟨x, hx, hle⟩ := hfreq (max N 1000)
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hx1000 : 1000 ≤ x := le_trans (le_max_right _ _) hx
  have hlb := Work.RHContract.A.psiTail_ge_of_RH h x hx1000
  rw [neg_div] at hlb
  have hub := hN x hxN
  linarith [hlb, hub, hle]

end Work.RHContract.Nonvacuity
