import Mathlib
import Submission.Work.FatouCoord.Flower.PsiData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.FatouCoord.Flower

noncomputable section

/-- `sgauge` is `2`-Lipschitz: `sgauge z ≤ sgauge w + 2 * ‖z - w‖`. -/
private lemma sgauge_sub_le (z w : ℂ) : sgauge z - sgauge w ≤ 2 * ‖z - w‖ := by
  have h1 : z.re - w.re ≤ ‖z - w‖ := by
    simpa using Complex.re_le_norm (z - w)
  have h2 : |z.im| - |w.im| ≤ ‖z - w‖ := by
    calc |z.im| - |w.im| ≤ |z.im - w.im| := abs_sub_abs_le_abs_sub _ _
      _ = |(z - w).im| := by simp
      _ ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  have hsum : sgauge z - sgauge w = (z.re - w.re) + (|z.im| - |w.im|) := by
    simp only [sgauge]; ring
  rw [hsum]; linarith

/-- For any real `D ≥ 0` and `E` there is `T > 0` with `E < t - D * √t` for all `t > T`:
the linear term `t` eventually dominates the `√t` term. -/
private lemma exists_gt_sub_mul_sqrt (D E : ℝ) (hD : 0 ≤ D) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T < t → E < t - D * Real.sqrt t := by
  refine ⟨max (max (4 * D ^ 2) (2 * E)) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · intro t ht
    rw [max_lt_iff] at ht
    obtain ⟨ht1, ht2⟩ := ht
    rw [max_lt_iff] at ht1
    obtain ⟨hD4, h2E⟩ := ht1
    have ht0 : 0 < t := by linarith
    have hDt : D * Real.sqrt t ≤ t / 2 := by
      rcases eq_or_lt_of_le hD with hD0 | hDpos
      · rw [← hD0, zero_mul]; linarith
      · have hsq : (D * Real.sqrt t) ^ 2 ≤ (t / 2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ht0.le]
          nlinarith [hD4, ht0]
        have ha : 0 ≤ D * Real.sqrt t := by positivity
        have hb : 0 ≤ t / 2 := by linarith
        have hle := sq_le_sq.mp hsq
        rwa [abs_of_nonneg ha, abs_of_nonneg hb] at hle
    linarith

theorem rV_window {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    {R : ℝ} (V : ℂ → ℂ)
    (hVdiff : DifferentiableOn ℂ V {w : ℂ | w.re < -R})
    (hVshift : ∀ w : ℂ, w.re < -R → V (w+1) = Work.FatouCoord.wMap f (V w))
    (hVbd : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ (1/2) * ‖w‖)
    (hVref : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1/2)
    {M R₀ : ℝ} (hM : 0 ≤ M) (hR₀ : R + 1 ≤ R₀) :
    ∃ T : ℝ, 0 < T ∧ ∀ w : ℂ, -R₀ - 1 ≤ w.re → w.re < -R₀ + 1 → T < |w.im| →
      Work.FatouCoord.Flower.rV f V R w ≠ 0 ∧ M < Work.FatouCoord.Flower.sgauge (Work.FatouCoord.Flower.rV f V R w) := by
  obtain ⟨T₁, _, hT₁⟩ :=
    exists_gt_sub_mul_sqrt (4 * Real.sqrt 2 * ‖1 - a‖)
      (M + R₀ + 2 + 4 * Real.pi * ‖1 - a‖) (by positivity)
  refine ⟨max T₁ (|R₀| + 2),
    lt_of_lt_of_le (by positivity : (0:ℝ) < |R₀| + 2) (le_max_right _ _), ?_⟩
  intro w hre1 hre2 hIm
  have hT₁' : T₁ < |w.im| := lt_of_le_of_lt (le_max_left _ _) hIm
  have hRp : |R₀| + 2 < |w.im| := lt_of_le_of_lt (le_max_right _ _) hIm
  have hwR : w.re < -R := by linarith
  have hrV : rV f V R w = V w := rV_eq_of_re_lt hVshift hwR
  have habsre : |w.re| ≤ |R₀| + 1 := by
    have hs : |w.re + R₀| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have h1 : |w.re| = |(w.re + R₀) - R₀| := by
      rw [show (w.re + R₀) - R₀ = w.re by ring]
    rw [h1]
    calc |(w.re + R₀) - R₀| ≤ |w.re + R₀| + |R₀| := abs_sub _ _
      _ ≤ |R₀| + 1 := by linarith
  have hnormw : ‖w‖ ≤ 2 * |w.im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im w
    have h2 : |R₀| + 1 ≤ |w.im| := by linarith
    linarith
  have hsqrt : Real.sqrt ‖w‖ ≤ Real.sqrt 2 * Real.sqrt |w.im| := by
    have h := Real.sqrt_le_sqrt hnormw
    rwa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at h
  have hδ := hVref w hwR
  have h2δ : 2 * ‖V w - w‖
      ≤ 4 * Real.sqrt 2 * ‖1 - a‖ * Real.sqrt |w.im| + 4 * Real.pi * ‖1 - a‖ + 1 := by
    have hc : (0:ℝ) ≤ ‖1 - a‖ := norm_nonneg _
    have hstep : 4 * ‖1 - a‖ * Real.sqrt ‖w‖
        ≤ 4 * ‖1 - a‖ * (Real.sqrt 2 * Real.sqrt |w.im|) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    nlinarith [hδ, hstep, hc]
  have hsw : -R₀ - 1 + |w.im| ≤ sgauge w := by
    simp only [sgauge]; linarith
  have hsub : sgauge w - sgauge (V w) ≤ 2 * ‖V w - w‖ := by
    have h := sgauge_sub_le w (V w)
    rwa [norm_sub_rev] at h
  have hkey := hT₁ |w.im| hT₁'
  have hmain : M < sgauge (V w) := by linarith
  constructor
  · rw [hrV]
    intro h0
    rw [h0] at hmain
    simp [sgauge] at hmain
    linarith
  · rw [hrV]; exact hmain

end

end Work.FatouCoord.Flower
