import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.phase_of_split
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.parGerm_conj
import Submission.Work.PARIMPL.ParSplit.parChart_algebra
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split
import Submission.Work.PARIMPL.ParSplit.phase_re_lower
import Submission.Work.PARIMPL.ParSplit.parU0_sq_eq_dirW
import Submission.Work.PARIMPL.ParSplit.parSigma_phase

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## The phase variable -/

/-- `W S c = 2 · (m c - F c (m c)) / E c`: the phase variable of `phase_of_split`, i.e. the
quantity `W = 2D/E` whose argument carries the phase of the splitting. -/
noncomputable def parW (S : SplitData d) (c : ℂ) : ℂ :=
  2 * (S.m c - Work.EL.F c (S.m c)) / S.E c

/-! ## `u₀ ^ 2 = σ · dir W ^ 2`

The chart constant `u₀ = parU0 S c` has square `parLam · ρ²/‖ρ‖²`.  Off the collision locus
`parLam = σ · dir Gc`, and since `D = m - F(m) = Gc · ρ` one has `ρ/‖ρ‖ = (D/‖D‖)·conj(dir Gc)`,
so that `u₀ ^ 2 = σ · (W/‖W‖) ^ 2` with `W = 2D/E`: the direction of `parU0` is the direction of
the phase variable `W`, transported by the branch sign `σ`. -/

theorem parU0_sq_eq_sigma_parW (S : SplitData d) {c : ℂ} (hρ : parRho S c ≠ 0)
    (hE : S.E c ≠ 0) (hD : S.m c - Work.EL.F c (S.m c) = Gc S c * parRho S c)
    (hlam : parLam S c = (parSigma S c : ℂ) * Gc S c / ((‖Gc S c‖ : ℝ) : ℂ)) :
    (parU0 S c) ^ 2
      = (parSigma S c : ℂ) * (parW S c / (((‖parW S c‖ : ℝ)) : ℂ)) ^ 2 := by
  have hG : Gc S c ≠ 0 := by
    unfold Gc
    exact pow_ne_zero 2 (div_ne_zero hE two_ne_zero)
  have key := parU0_sq_eq_dirW (E := S.E c) (G := Gc S c) (ρ := parRho S c)
    (D := S.m c - Work.EL.F c (S.m c)) hG hρ (by rfl) hD
  rw [parChart_parU0_sq, hlam]
  rw [show ((parSigma S c : ℂ) * Gc S c / ((‖Gc S c‖ : ℝ) : ℂ)) * (parRho S c) ^ 2
        / ((Complex.ofReal ‖parRho S c‖) ^ 2)
      = (parSigma S c : ℂ) * ((Gc S c / ((‖Gc S c‖ : ℝ) : ℂ)) * (parRho S c) ^ 2
        / ((Complex.ofReal ‖parRho S c‖) ^ 2)) from by ring]
  rw [key]
  rfl

/-! ## The real-part lower bound -/

/-- The phase inequalities of `phase_of_split`, read through `parSigma` and the phase variable
`parW`, give `Re (u₀ ^ 2) ≥ 17/32`. -/
theorem parU0_sq_re_of_phase (S : SplitData d) {c : ℂ} (hρ : parRho S c ≠ 0)
    (hE : S.E c ≠ 0) (hD : S.m c - Work.EL.F c (S.m c) = Gc S c * parRho S c)
    (hlam : parLam S c = (parSigma S c : ℂ) * Gc S c / ((‖Gc S c‖ : ℝ) : ℂ))
    (hswap : parSigma S c = -1 → 7 * ‖parW S c‖ ≤ 8 * |(parW S c).im|)
    (hfix : parSigma S c = 1 → 7 * ‖parW S c‖ ≤ 8 * |(parW S c).re|) :
    (17 : ℝ) / 32 ≤ ((parU0 S c) ^ 2).re := by
  have hkey := parU0_sq_eq_sigma_parW S hρ hE hD hlam
  have hG0 : Gc S c ≠ 0 := by
    unfold Gc
    exact pow_ne_zero 2 (div_ne_zero hE two_ne_zero)
  have hW0 : parW S c ≠ 0 := by
    have hD0 : S.m c - Work.EL.F c (S.m c) ≠ 0 := by
      rw [hD]
      exact mul_ne_zero hG0 hρ
    unfold parW
    exact div_ne_zero (mul_ne_zero two_ne_zero hD0) hE
  have hph := phase_re_lower (parW S c) hW0
  rw [hkey]
  rcases parSigma_eq_neg_one_or_one S c with hσ | hσ
  · rw [hσ, show (((-1 : ℝ) : ℂ) * (parW S c / (((‖parW S c‖ : ℝ)) : ℂ)) ^ 2)
        = -((parW S c / (((‖parW S c‖ : ℝ)) : ℂ)) ^ 2) from by norm_num]
    exact hph.2 (hswap hσ)
  · rw [hσ, show (((1 : ℝ) : ℂ) * (parW S c / (((‖parW S c‖ : ℝ)) : ℂ)) ^ 2)
        = (parW S c / (((‖parW S c‖ : ℝ)) : ℂ)) ^ 2 from by norm_num]
    exact hph.1 (hfix hσ)

/-! ## The target -/

theorem parU0_sq_re_lower {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      S.E c ≠ 0 → (17 : ℝ)/32 ≤ (((Work.PARIMPL.ParSplit.parU0 S c) ^ 2).re) := by
  obtain ⟨ρ₁, hρ₁, hρ₁ρ, h₁⟩ := parLam_eq S
  obtain ⟨ρ₂, hρ₂, hρ₂ρ, h₂⟩ := parRho_ne_zero S
  obtain ⟨ρ₃, hρ₃, hρ₃ρ, h₃⟩ := parSigma_phase S
  set ρ' : ℝ := min (min ρ₁ ρ₂) ρ₃ with hρ'def
  have hρ'pos : 0 < ρ' := by rw [hρ'def]; exact lt_min (lt_min hρ₁ hρ₂) hρ₃
  have hρ'ρ : ρ' ≤ S.ρ := by
    rw [hρ'def]
    exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) hρ₁ρ
  refine ⟨ρ', hρ'pos, hρ'ρ, ?_⟩
  intro c hc hE
  have hcρ : c ∈ Metric.ball c₀ S.ρ :=
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) hρ'ρ)
  have hc₁ : c ∈ Metric.ball c₀ ρ₁ := by
    refine mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) ?_)
    rw [hρ'def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hc₂ : c ∈ Metric.ball c₀ ρ₂ := by
    refine mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) ?_)
    rw [hρ'def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hc₃ : c ∈ Metric.ball c₀ ρ₃ := by
    refine mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) ?_)
    rw [hρ'def]; exact min_le_right _ _
  have hρne : parRho S c ≠ 0 := h₂ c hc₂
  have hG0 : Gc S c ≠ 0 := by
    unfold Gc
    exact pow_ne_zero 2 (div_ne_zero hE two_ne_zero)
  have hlam : parLam S c = (parSigma S c : ℂ) * Gc S c / ((‖Gc S c‖ : ℝ) : ℂ) :=
    h₁ c hc₁ hG0
  have hD : S.m c - Work.EL.F c (S.m c) = Gc S c * parRho S c := by
    have hq := Qpoly_eval_shift_local S hcρ (fun h0 => absurd h0 hE) 0
    rw [Qpoly_eval, add_zero, Rfun_zero] at hq
    rw [show (0 : ℂ) ^ 2 = 0 from by ring, zero_sub] at hq
    rw [show S.m c - Work.EL.F c (S.m c) = -(Work.EL.F c (S.m c) - S.m c) from by ring, hq]
    ring
  have hσ := h₃ c hc₃ hE
  exact parU0_sq_re_of_phase S hρne hE hD hlam (fun h => hσ.1 h) (fun h => hσ.2 h)

end Work.PARIMPL.ParSplit
