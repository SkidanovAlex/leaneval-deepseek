import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.Analysis.Integral.trig_conv_integral

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open MeasureTheory
noncomputable section

/-- `ζ · γ = θ`: immediate from `γ = θ/ζ` and `ζ ≠ 0`. -/
lemma zetaT_mul_gammaT {θ lam : ℝ} (hζ : zetaT θ lam ≠ 0) :
    zetaT θ lam * gammaT θ lam = θ := by
  rw [gammaT]
  field_simp

/-- On `[-γ,γ]`, `gT` is the trigonometric expression of HB §7. -/
lemma gT_of_abs_le (θ lam t : ℝ) (ht : |t| ≤ gammaT θ lam) :
    gT θ lam t = lam * (1 + Real.tan θ ^ 2) * (Real.cos (zetaT θ lam * t) - Real.cos θ) := by
  rw [gT, if_pos ht]

/-- `gT` vanishes once `γ ≤ |t|` (including the two endpoints `t = ±γ`, where
`cos (ζ(±γ)) = cos θ`). -/
lemma gT_eq_zero_of_gamma_le_abs {θ lam t : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) (ht : gammaT θ lam ≤ |t|) : gT θ lam t = 0 := by
  have hζ := zetaT_pos hθ1 hθ2 hlam
  have hzγ : zetaT θ lam * gammaT θ lam = θ := zetaT_mul_gammaT (ne_of_gt hζ)
  rw [gT]
  rcases lt_or_eq_of_le ht with hlt | heq
  · rw [if_neg (not_le.mpr hlt)]
  · rw [if_pos heq.ge]
    have hc : Real.cos (zetaT θ lam * t) = Real.cos θ := by
      have h1 : |zetaT θ lam * t| = θ := by
        rw [abs_mul, abs_of_pos hζ, ← heq]
        exact hzγ
      rw [← Real.cos_abs, h1]
    rw [hc, sub_self, mul_zero]

theorem testfun_conv (θ lam x : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam)
    (hx : 0 ≤ x) :
    Work.LinnikAreas.Density4.fT θ lam x =
      ∫ t in (-(Work.LinnikAreas.Density4.gammaT θ lam))..(Work.LinnikAreas.Density4.gammaT θ lam),
        Work.LinnikAreas.Density4.gT θ lam t * Work.LinnikAreas.Density4.gT θ lam (x - t) := by
  have hζ : 0 < zetaT θ lam := zetaT_pos hθ1 hθ2 hlam
  have hγ : 0 < gammaT θ lam := gammaT_pos hθ1 hθ2 hlam
  have hzγ : zetaT θ lam * gammaT θ lam = θ := zetaT_mul_gammaT (ne_of_gt hζ)
  by_cases hx2 : x ≤ 2 * gammaT θ lam
  · rw [fT, if_pos ⟨hx, hx2⟩]
    have hmain : ∫ t in (-(gammaT θ lam))..(gammaT θ lam), gT θ lam t * gT θ lam (x - t)
        = lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 *
          ( (2 * gammaT θ lam - x) * (Real.cos (zetaT θ lam * x) / 2 + Real.cos θ ^ 2)
            + Real.sin (2 * θ - zetaT θ lam * x) / (2 * zetaT θ lam)
            - Real.sin (2 * θ) / zetaT θ lam
            + 2 * Real.cos θ * Real.sin (zetaT θ lam * x - θ) / zetaT θ lam ) := by
      have hle : -(gammaT θ lam) ≤ x - gammaT θ lam := by linarith
      have hle2 : x - gammaT θ lam ≤ gammaT θ lam := by linarith
      have hint1 : IntervalIntegrable (fun t : ℝ => gT θ lam t * gT θ lam (x - t)) volume
          (-(gammaT θ lam)) (x - gammaT θ lam) := by
        refine (intervalIntegrable_const (μ := volume) (a := -(gammaT θ lam))
          (b := x - gammaT θ lam) (c := (0:ℝ))).congr ?_
        intro t ht
        show (0:ℝ) = gT θ lam t * gT θ lam (x - t)
        have htle : t ≤ x - gammaT θ lam := by
          rcases Set.mem_uIoc.mp ht with ⟨_, h⟩ | ⟨h1, h2⟩
          · exact h
          · linarith
        have habs : gammaT θ lam ≤ |x - t| := by
          have h1 : 0 ≤ x - t := by linarith
          rw [abs_of_nonneg h1]
          linarith
        rw [gT_eq_zero_of_gamma_le_abs hθ1 hθ2 hlam habs, mul_zero]
      have hint2 : IntervalIntegrable (fun t : ℝ => gT θ lam t * gT θ lam (x - t)) volume
          (x - gammaT θ lam) (gammaT θ lam) := by
        refine ((by fun_prop : Continuous (fun t : ℝ =>
          (lam * (1 + Real.tan θ ^ 2)) * (Real.cos (zetaT θ lam * t) - Real.cos θ) *
            ((lam * (1 + Real.tan θ ^ 2)) * (Real.cos (zetaT θ lam * (x - t)) - Real.cos θ)))).intervalIntegrable _ _).congr ?_
        intro t ht
        show (lam * (1 + Real.tan θ ^ 2)) * (Real.cos (zetaT θ lam * t) - Real.cos θ) *
            ((lam * (1 + Real.tan θ ^ 2)) * (Real.cos (zetaT θ lam * (x - t)) - Real.cos θ))
          = gT θ lam t * gT θ lam (x - t)
        have htlo : x - gammaT θ lam ≤ t := by
          rcases Set.mem_uIoc.mp ht with ⟨h1, _⟩ | ⟨h1, h2⟩
          · linarith
          · linarith
        have hthi : t ≤ gammaT θ lam := by
          rcases Set.mem_uIoc.mp ht with ⟨_, h2⟩ | ⟨h1, h2⟩
          · exact h2
          · linarith
        have ht_abs : |t| ≤ gammaT θ lam := by
          rw [abs_le]; constructor <;> linarith
        have hxt_abs : |x - t| ≤ gammaT θ lam := by
          rw [abs_le]; constructor <;> linarith
        rw [gT_of_abs_le θ lam t ht_abs, gT_of_abs_le θ lam (x - t) hxt_abs]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      have hzero : ∫ t in (-(gammaT θ lam))..(x - gammaT θ lam),
          gT θ lam t * gT θ lam (x - t) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr
        intro t ht
        show gT θ lam t * gT θ lam (x - t) = 0
        have htle : t ≤ x - gammaT θ lam := by
          rcases Set.mem_uIcc.mp ht with ⟨_, h⟩ | ⟨h1, h2⟩
          · exact h
          · linarith
        have habs : gammaT θ lam ≤ |x - t| := by
          have h1 : 0 ≤ x - t := by linarith
          rw [abs_of_nonneg h1]
          linarith
        rw [gT_eq_zero_of_gamma_le_abs hθ1 hθ2 hlam habs, mul_zero]
      have htr : ∫ t in (x - gammaT θ lam)..(gammaT θ lam), gT θ lam t * gT θ lam (x - t)
          = (lam * (1 + Real.tan θ ^ 2)) ^ 2 *
            ( (2 * gammaT θ lam - x) * (Real.cos (zetaT θ lam * x) / 2 + Real.cos θ ^ 2)
              + Real.sin (2 * θ - zetaT θ lam * x) / (2 * zetaT θ lam)
              - Real.sin (2 * θ) / zetaT θ lam
              + 2 * Real.cos θ * Real.sin (zetaT θ lam * x - θ) / zetaT θ lam ) := by
        have step1 : ∫ t in (x - gammaT θ lam)..(gammaT θ lam), gT θ lam t * gT θ lam (x - t)
            = ∫ t in (x - gammaT θ lam)..(gammaT θ lam),
                (lam * (1 + Real.tan θ ^ 2)) ^ 2 *
                  ((Real.cos (zetaT θ lam * t) - Real.cos θ) *
                   (Real.cos (zetaT θ lam * (x - t)) - Real.cos θ)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          show gT θ lam t * gT θ lam (x - t) = (lam * (1 + Real.tan θ ^ 2)) ^ 2 *
                  ((Real.cos (zetaT θ lam * t) - Real.cos θ) *
                   (Real.cos (zetaT θ lam * (x - t)) - Real.cos θ))
          have htlo : x - gammaT θ lam ≤ t := by
            rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact h1
            · linarith
          have hthi : t ≤ gammaT θ lam := by
            rcases Set.mem_uIcc.mp ht with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact h2
            · linarith
          have ht_abs : |t| ≤ gammaT θ lam := by
            rw [abs_le]; constructor <;> linarith
          have hxt_abs : |x - t| ≤ gammaT θ lam := by
            rw [abs_le]; constructor <;> linarith
          rw [gT_of_abs_le θ lam t ht_abs, gT_of_abs_le θ lam (x - t) hxt_abs]
          ring
        rw [step1, intervalIntegral.integral_const_mul,
          Work.Analysis.Integral.trig_conv_integral (zetaT θ lam) (gammaT θ lam) θ x (ne_of_gt hζ) hzγ]
      rw [← hsplit, hzero, htr]
      ring
    exact hmain.symm
  · rw [fT, if_neg (fun h => hx2 h.2)]
    have : ∫ t in (-(gammaT θ lam))..(gammaT θ lam), gT θ lam t * gT θ lam (x - t) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr
      intro t ht
      show gT θ lam t * gT θ lam (x - t) = 0
      have htle : t ≤ gammaT θ lam := by
        rcases Set.mem_uIcc.mp ht with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · linarith
      have habs : gammaT θ lam ≤ |x - t| := by
        have h1 : 0 ≤ x - t := by linarith
        rw [abs_of_nonneg h1]
        linarith
      rw [gT_eq_zero_of_gamma_le_abs hθ1 hθ2 hlam habs, mul_zero]
    rw [this]

end

end Work.LinnikAreas.Density4
