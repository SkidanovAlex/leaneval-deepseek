import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.phase_of_split
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-- `parSigma S c = -1` forces the `swap` branch of the dichotomy. -/
theorem parSigma_eq_neg_one_imp {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : SplitData d) (c : ℂ) (hsig : parSigma S c = -1) :
    gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 := by
  by_contra hnp
  have h1 : parSigma S c = 1 := by
    unfold parSigma
    rw [ite_eq_right hnp]
  rw [h1] at hsig
  norm_num at hsig

/-- `parSigma S c = 1` forces the `fix` branch of the dichotomy. -/
theorem parSigma_eq_one_imp {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : SplitData d) (c : ℂ) (hsig : parSigma S c = 1) :
    ¬ (gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2) := by
  intro hswap
  have h1 : parSigma S c = -1 := by
    unfold parSigma
    rw [ite_eq_left hswap]
  rw [h1] at hsig
  norm_num at hsig

theorem parSigma_phase {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ', S.E c ≠ 0 →
      (Work.PARIMPL.ParSplit.parSigma S c = -1 →
        7 * ‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖
          ≤ 8 * |(2 * (S.m c - Work.EL.F c (S.m c)) / S.E c).im|) ∧
      (Work.PARIMPL.ParSplit.parSigma S c = 1 →
        7 * ‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖
          ≤ 8 * |(2 * (S.m c - Work.EL.F c (S.m c)) / S.E c).re|) := by
  obtain ⟨ρ₁, hρ₁, hρ₁S, hphase⟩ := phase_of_split S
  obtain ⟨ρ₂, hρ₂, _hρ₂S, hmem⟩ := g_mem_of_split S
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, le_trans (min_le_left _ _) hρ₁S, ?_⟩
  intro c hc hE
  have hd := mem_ball.mp hc
  have hc₁ : c ∈ Metric.ball c₀ ρ₁ := mem_ball.mpr (lt_of_lt_of_le hd (min_le_left _ _))
  have hc₂ : c ∈ Metric.ball c₀ ρ₂ := mem_ball.mpr (lt_of_lt_of_le hd (min_le_right _ _))
  have hcS : c ∈ Metric.ball c₀ S.ρ :=
    mem_ball.mpr (lt_of_lt_of_le hd (le_trans (min_le_left _ _) hρ₁S))
  have hP := hphase c hc₁ hE
  refine ⟨fun hsig => hP.1 (parSigma_eq_neg_one_imp S c hsig), fun hsig => ?_⟩
  have hnotswap := parSigma_eq_one_imp S c hsig
  have hfix : gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 := by
    rcases S.swap_or_fix_of_split hcS (hmem c hc₂) with h | h
    · exact h
    · exact absurd h hnotswap
  exact hP.2 hfix

end Work.PARIMPL.ParSplit
