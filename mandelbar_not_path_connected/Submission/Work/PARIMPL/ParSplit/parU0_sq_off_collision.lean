import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parChart_algebra
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.parGerm_conj
import Submission.Work.PARIMPL.ParSplit.Hp_double_root_count
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

/-- **The value of the germ at `0` off the collision locus.**  Writing `W := 2·(m c - F c (m c))/E c`,
one has `parU0 S c ^ 2 = parSigma S c * W^2 / ‖W‖^2`, i.e. `parU0` is one of the two square roots
of `σ · dir(W)^2` (`σ = parSigma = ±1` is the swap/fix sign).

Proof ingredients (all already proved in the workspace):
* `parChart_algebra`/`parChartSq`: `parU0^2 = parLam * parRho^2 / ‖parRho‖^2`;
* `parLam_eq`: off the collision locus `parLam = σ * Gc / ‖Gc‖` with `Gc = (E/2)^2`;
* at `w = 0` the identity `Qpoly_eval_shift_local` gives `m c - F c (m c) = Gc c * parRho c`,
  so `W = 2 Gc ρ / E = E ρ / 2`;
* hence `parU0^2 = σ (E/2)^2 (ρ/‖ρ‖)^2 / (‖E/2‖^2) = σ W^2/‖W‖^2`. -/
theorem parU0_sq_off_collision {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ', S.E c ≠ 0 →
      Work.PARIMPL.ParSplit.parU0 S c ^ 2 =
        (Work.PARIMPL.ParSplit.parSigma S c : ℂ) *
          ((2 * (S.m c - Work.EL.F c (S.m c)) / S.E c) ^ 2 /
            ((‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖ : ℝ) : ℂ) ^ 2) := by
  obtain ⟨ρ₁, hρ₁0, hρ₁ρ, hlam⟩ := parLam_eq S
  obtain ⟨ρ₂, hρ₂0, hρ₂ρ, hrho⟩ := parRho_ne_zero S
  obtain ⟨ρ₃, hρ₃0, hρ₃ρ, hdr⟩ := Hp_double_root_count S
  refine ⟨min (min ρ₁ ρ₂) ρ₃, lt_min (lt_min hρ₁0 hρ₂0) hρ₃0,
    le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) hρ₁ρ, ?_⟩
  intro c hc hE
  have hle1 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hle2 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hle3 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₃ := min_le_right _ _
  have hd := Metric.mem_ball.mp hc
  have hcS : c ∈ Metric.ball c₀ S.ρ := Metric.mem_ball.mpr (lt_of_lt_of_le hd (le_trans hle1 hρ₁ρ))
  have hc₁ : c ∈ Metric.ball c₀ ρ₁ := Metric.mem_ball.mpr (lt_of_lt_of_le hd hle1)
  have hc₂ : c ∈ Metric.ball c₀ ρ₂ := Metric.mem_ball.mpr (lt_of_lt_of_le hd hle2)
  have hc₃ : c ∈ Metric.ball c₀ ρ₃ := Metric.mem_ball.mpr (lt_of_lt_of_le hd hle3)
  have hρne : parRho S c ≠ 0 := hrho c hc₂
  have hGne : Gc S c ≠ 0 := by
    rw [show Gc S c = (S.E c / 2) ^ 2 from rfl]
    exact pow_ne_zero 2 (div_ne_zero hE two_ne_zero)
  have hlamc : parLam S c = (parSigma S c : ℂ) * Gc S c / (‖Gc S c‖ : ℂ) :=
    hlam c hc₁ hGne
  set W : ℂ := 2 * (S.m c - Work.EL.F c (S.m c)) / S.E c with hWdef
  have h0 := Qpoly_eval_shift_local S hcS (hdr c hc₃) 0
  rw [add_zero, Qpoly_eval, Rfun_zero] at h0
  have hmF : S.m c - Work.EL.F c (S.m c) = Gc S c * parRho S c := by
    have h1 : S.m c - Work.EL.F c (S.m c) = -(Work.EL.F c (S.m c) - S.m c) := by ring
    rw [h1, h0]; ring
  have hWval : W = (S.E c / 2) * parRho S c := by
    rw [hWdef, hmF, show Gc S c = (S.E c / 2) ^ 2 from rfl]
    field_simp
  rw [parChart_parU0_sq S c, hlamc]
  rw [hWval]
  rw [show Gc S c = (S.E c / 2) ^ 2 from rfl]
  rw [norm_pow, norm_mul]
  push_cast
  have hΔ : (S.E c / 2) ≠ 0 := div_ne_zero hE two_ne_zero
  have hnd : ((‖S.E c / 2‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hΔ
  have hnr : ((‖parRho S c‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hρne
  field_simp

end Work.PARIMPL.ParSplit
