import Mathlib
import Submission.Work.FatouCoord.Flower.PsiData
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Flower.ConjRefined
import Submission.Work.FatouCoord.Flower.logShiftBound
import Submission.Work.FatouCoord.Flower.exists_threshold_log_div

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped NNReal

set_option linter.unusedVariables false

namespace Work.FatouCoord.Flower

open Work.FatouCoord.Petal (Lambda LeftHalfPlane mem_LeftHalfPlane Lambda_apply)

noncomputable section

theorem V_preimage {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    {R : ℝ} (V : ℂ → ℂ)
    (hVdiff : DifferentiableOn ℂ V {w : ℂ | w.re < -R})
    (hZdiff : DifferentiableOn ℂ (fun w => V w - w - (1 - a) * Work.FatouCoord.Petal.Lambda w) {w : ℂ | w.re < -R})
    (hZbd : ∀ w : ℂ, w.re < -R → ‖V w - w - (1 - a) * Work.FatouCoord.Petal.Lambda w‖ ≤ 1/2)
    (hVinj : Set.InjOn V {w : ℂ | w.re < -R}) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ Y : ℂ, R₁ ≤ ‖Y‖ →
      (Y - (1 - a) * Work.FatouCoord.Petal.Lambda Y).re < -R₁ →
        ∃ x : ℂ, x.re < -R ∧ V x = Y ∧ ‖x - (Y - (1 - a) * Work.FatouCoord.Petal.Lambda Y)‖ ≤ 4 := by
  set c : ℂ := 1 - a with hc
  set Z : ℂ → ℂ := fun w => V w - w - c * Lambda w with hZ
  obtain ⟨Tlog, hTlogpos, hTlog⟩ := logShiftBound c
  obtain ⟨Tsm, hTsmpos, hTsm⟩ := exists_threshold_log_div (2 * ‖c‖ ^ 2)
  set R₀ : ℝ := max R 1 with hR₀
  have hR₀pos : 0 < R₀ := by rw [hR₀]; exact lt_of_lt_of_le one_pos (le_max_right R 1)
  have hRR₀ : R ≤ R₀ := by rw [hR₀]; exact le_max_left R 1
  set R₁ : ℝ := Tlog + Tsm + (R₀ + 12) + (4 * ‖c‖ + 8) + 12 + 1 with hR₁
  have hTlogR₁ : Tlog ≤ R₁ := by rw [hR₁]; linarith [hTsmpos, hR₀pos, norm_nonneg c]
  have hTsmR₁ : Tsm ≤ R₁ := by rw [hR₁]; linarith [hTlogpos, hR₀pos, norm_nonneg c]
  have hR₀R₁ : R₀ + 12 ≤ R₁ := by rw [hR₁]; linarith [hTlogpos, hTsmpos, norm_nonneg c]
  have hKR₁ : 4 * ‖c‖ + 8 ≤ R₁ := by rw [hR₁]; linarith [hTlogpos, hTsmpos, hR₀pos]
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le hTlogpos hTlogR₁
  refine ⟨R₁, hR₁pos, ?_⟩
  intro Y hY hYre
  set x₀ : ℂ := Y - c * Lambda Y with hx₀
  have hx₀re : x₀.re < -R₁ := by rw [hx₀]; exact hYre
  have hx₀R₀ : x₀ ∈ LeftHalfPlane R₀ := by
    rw [mem_LeftHalfPlane]; linarith
  -- working half-plane
  set T₂ : ℝ := R₁ - 6 with hT₂
  have hT₂pos : 0 < T₂ := by rw [hT₂]; linarith
  have hR₀T₂ : R₀ < T₂ := by rw [hT₂]; linarith
  have hT₂K : 4 * ‖c‖ ≤ T₂ := by rw [hT₂]; linarith
  have hT₂R₀ : R₀ + 2 ≤ T₂ := by rw [hT₂]; linarith
  set s : Set ℂ := Metric.closedBall x₀ 4 with hs
  have hs_sub : s ⊆ LeftHalfPlane T₂ := by
    intro y hy
    rw [hs, Metric.mem_closedBall, dist_eq_norm] at hy
    rw [mem_LeftHalfPlane]
    have h1 : y.re - x₀.re ≤ ‖y - x₀‖ := by
      have := Complex.re_le_norm (y - x₀); rw [Complex.sub_re] at this; exact this
    have h3 : T₂ = R₁ - 6 := hT₂
    linarith
  -- Lipschitz bounds on the ball
  have hΛ : ∀ y ∈ s, ∀ y' ∈ s, ‖Lambda y - Lambda y'‖ ≤ ‖y - y'‖ / T₂ :=
    fun y hy y' hy' => Rep.norm_Lambda_sub_le_aux hT₂pos (hs_sub hy) (hs_sub hy')
  have hZdiffR₀ : DifferentiableOn ℂ Z (LeftHalfPlane R₀) :=
    hZdiff.mono (fun w hw => by
      rw [mem_LeftHalfPlane] at hw
      exact show w.re < -R from by linarith)
  have hZbdR₀ : ∀ w : ℂ, w ∈ LeftHalfPlane R₀ → ‖Z w‖ ≤ 1 / 2 :=
    fun w hw => hZbd w (by rw [mem_LeftHalfPlane] at hw; linarith)
  have hZL : ∀ y ∈ s, ∀ y' ∈ s, ‖Z y - Z y'‖ ≤ (1 / 2) * ‖y - y'‖ := by
    intro y hy y' hy'
    have h := Rep.norm_Z_sub_le hR₀pos hZdiffR₀ hZbdR₀ hR₀T₂ (hs_sub hy) (hs_sub hy')
    have h2 : (1 / (T₂ - R₀)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) (by linarith : (2:ℝ) ≤ T₂ - R₀)
    calc ‖Z y - Z y'‖ ≤ (1 / (T₂ - R₀)) * ‖y - y'‖ := h
      _ ≤ (1 / 2) * ‖y - y'‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  -- the fixed point map
  set Ψ : ℂ → ℂ := fun y => Y - c * Lambda y - Z y with hΨ
  have hcontr_pt : ∀ y ∈ s, ∀ y' ∈ s, ‖Ψ y - Ψ y'‖ ≤ (3 / 4) * ‖y - y'‖ := by
    intro y hy y' hy'
    have h1 : Ψ y - Ψ y' = -(c * (Lambda y - Lambda y') + (Z y - Z y')) := by rw [hΨ]; ring
    rw [h1, norm_neg]
    have hK : ‖c‖ / T₂ ≤ 1 / 4 := by
      rw [div_le_iff₀ hT₂pos]; linarith
    calc ‖c * (Lambda y - Lambda y') + (Z y - Z y')‖
        ≤ ‖c * (Lambda y - Lambda y')‖ + ‖Z y - Z y'‖ := norm_add_le _ _
      _ = ‖c‖ * ‖Lambda y - Lambda y'‖ + ‖Z y - Z y'‖ := by rw [norm_mul]
      _ ≤ ‖c‖ * (‖y - y'‖ / T₂) + (1 / 2) * ‖y - y'‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (hΛ y hy y' hy') (norm_nonneg c))
              (hZL y hy y' hy')
      _ = (‖c‖ / T₂ + 1 / 2) * ‖y - y'‖ := by ring
      _ ≤ (3 / 4) * ‖y - y'‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hx₀mem : x₀ ∈ s := by
    rw [hs, Metric.mem_closedBall]; simp
  -- displacement at the centre
  have hΨx₀ : ‖Ψ x₀ - x₀‖ ≤ 1 := by
    have h1 : Ψ x₀ - x₀ = c * (Lambda Y - Lambda x₀) - Z x₀ := by rw [hΨ, hx₀]; ring
    rw [h1]
    have hkey : ‖Lambda Y - Lambda x₀‖ ≤ 2 * ‖c‖ * (Real.log ‖Y‖ + 2 * Real.pi) / ‖Y‖ := by
      have hx₀neg : (-x₀).re > 0 := by rw [Complex.neg_re]; linarith
      have harg : -Y + c * (Complex.log (-Y) + (Real.pi : ℂ) * Complex.I) = -x₀ := by
        rw [hx₀, Lambda_apply]; ring
      have hre : (-Y + c * (Complex.log (-Y) + (Real.pi : ℂ) * Complex.I)).re > 0 := by
        rw [harg]; exact hx₀neg
      have hlogb := hTlog (-Y) (by rw [norm_neg]; exact le_trans hTlogR₁ hY) hre
      have heq : Lambda Y - Lambda x₀ = Complex.log (-Y) - Complex.log (-x₀) := by
        rw [Lambda_apply, Lambda_apply]; ring
      rw [heq, norm_sub_rev]
      rw [harg, norm_neg] at hlogb
      exact hlogb
    have hmul : ‖c * (Lambda Y - Lambda x₀)‖ ≤ 1 / 2 := by
      rw [norm_mul]
      calc ‖c‖ * ‖Lambda Y - Lambda x₀‖
          ≤ ‖c‖ * (2 * ‖c‖ * (Real.log ‖Y‖ + 2 * Real.pi) / ‖Y‖) :=
            mul_le_mul_of_nonneg_left hkey (norm_nonneg c)
        _ ≤ 1 / 2 := by
            rw [← mul_div_assoc]
            rw [div_le_iff₀ (lt_of_lt_of_le hR₁pos hY)]
            have h2 := hTsm ‖Y‖ (le_trans hTsmR₁ hY)
            have h3 : ‖c‖ * (2 * ‖c‖ * (Real.log ‖Y‖ + 2 * Real.pi))
                = 2 * ‖c‖ ^ 2 * (Real.log ‖Y‖ + 2 * Real.pi) := by ring
            rw [h3]; linarith
    calc ‖c * (Lambda Y - Lambda x₀) - Z x₀‖
        ≤ ‖c * (Lambda Y - Lambda x₀)‖ + ‖Z x₀‖ := norm_sub_le _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add hmul (hZbdR₀ x₀ hx₀R₀)
      _ = 1 := by norm_num
  have hmaps : Set.MapsTo Ψ s s := by
    intro y hy
    rw [hs, Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    have h1 : Ψ y - x₀ = (Ψ y - Ψ x₀) + (Ψ x₀ - x₀) := by ring
    calc ‖Ψ y - x₀‖ ≤ ‖Ψ y - Ψ x₀‖ + ‖Ψ x₀ - x₀‖ := by rw [h1]; exact norm_add_le _ _
      _ ≤ (3 / 4) * ‖y - x₀‖ + 1 :=
            add_le_add (hcontr_pt y (by rw [hs, Metric.mem_closedBall, dist_eq_norm]; exact hy)
              x₀ (by rw [hs, Metric.mem_closedBall, dist_eq_norm]; simp)) hΨx₀
      _ ≤ (3 / 4) * 4 + 1 := by linarith
      _ ≤ 4 := by norm_num
  have hcontr : ContractingWith (3 / 4 : ℝ≥0) (Set.MapsTo.restrict Ψ s s hmaps) := by
    refine ⟨by norm_num, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro y y'
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hcontr_pt y.1 y.2 y'.1 y'.2
  obtain ⟨y, hys, hyfix, -⟩ := ContractingWith.exists_fixedPoint' (s := s) (f := Ψ)
    (K := (3 / 4 : ℝ≥0)) (Metric.isClosed_closedBall.isComplete) hmaps hcontr (x := x₀)
    (by rw [hs, Metric.mem_closedBall]; simp) (edist_ne_top x₀ (Ψ x₀))
  have hys' : y ∈ s := hys
  have hys'' : y ∈ Metric.closedBall x₀ 4 := by rw [← hs]; exact hys'
  have hyre : y.re < -R := by
    have h1 := hs_sub hys'
    rw [mem_LeftHalfPlane] at h1
    linarith
  have hdist : ‖y - x₀‖ ≤ 4 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hys''
    exact hys''
  have hVy : V y = Y := by
    have h1 : Y - c * Lambda y - Z y = y := by
      have h0 : Ψ y = y := hyfix
      rw [hΨ] at h0
      simpa using h0
    have h2 : Y = y + c * Lambda y + Z y := by linear_combination h1
    rw [h2, hZ]; ring
  exact ⟨y, hyre, hVy, by simpa [hc, hx₀] using hdist⟩

end

end Work.FatouCoord.Flower
