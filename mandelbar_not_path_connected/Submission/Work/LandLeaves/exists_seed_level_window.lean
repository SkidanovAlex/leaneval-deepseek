import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Set Metric
open scoped Topology

set_option linter.unusedVariables false

/-- For `ρ > 1`, `η > 0` and any `D : ℕ` there is a real `r₀` with `1 < r₀`, `r₀ < ρ` and
`r₀ ^ D < 1 + η`: take `r₀` close enough to `1` (the existence of such an `r₀` is the continuity
of `t ↦ t ^ D` at `1`, and it holds vacuously for `D = 0` too, where `r₀ ^ 0 = 1 < 1 + η`). -/
lemma exists_lt_pow_lt_one_add {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 < η) (D : ℕ) :
    ∃ r₀ : ℝ, 1 < r₀ ∧ r₀ < ρ ∧ r₀ ^ D < 1 + η := by
  have hnb : {t : ℝ | t ^ D < (1 : ℝ) + η} ∈ nhds (1 : ℝ) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ D) 1 := (continuous_id.pow D).continuousAt
    have heq : {t : ℝ | t ^ D < (1 : ℝ) + η} = (fun t : ℝ => t ^ D) ⁻¹' Set.Iio ((1:ℝ) + η) :=
      rfl
    rw [heq]
    exact hc.preimage_mem_nhds (Iio_mem_nhds (by rw [one_pow]; linarith))
  rw [Metric.mem_nhds_iff] at hnb
  obtain ⟨ε, hε, hεsub⟩ := hnb
  set m : ℝ := min ε (ρ - 1) with hm
  have hmpos : 0 < m := lt_min hε (by linarith)
  refine ⟨1 + m / 2, by linarith, ?_, ?_⟩
  · have hle : m ≤ ρ - 1 := min_le_right _ _
    linarith
  · have hb : (1 + m / 2) ∈ Metric.ball (1 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 : (1 + m / 2) - 1 = m / 2 := by ring
      rw [h1, abs_of_pos (by linarith)]
      have hle : m ≤ ε := min_le_left _ _
      linarith
    exact hεsub hb

theorem exists_seed_level_window {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {y : ℂ} {θ₀ : ℝ} (hθ₀ : Work.EL.LandsN hN θ₀ y) {D : ℕ} {ε ρ R : ℝ}
    (hε : 0 < ε) (hεR : ε < R) (hρ : 1 < ρ)
    (hshr : ∀ θ t : ℝ, 1 < t → t < ρ → ∀ s₁ s₂ : ℝ, t ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t ^ D →
        ‖Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ s₁‖ ≤ ε) :
    ∃ r₀ : ℝ, 1 < r₀ ∧ r₀ < ρ ∧
      Work.EL.rayPt hN θ₀ '' Set.Icc r₀ (r₀ ^ D) ⊆ Metric.ball y R := by
  -- landing gives a level window `(1, 1 + δ)` on which the ray stays inside `ball y R`
  obtain ⟨δ, hδ, hδb⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hθ₀) R (lt_trans hε hεR)
  -- and we can pick `r₀ ∈ (1, ρ)` with `r₀ ^ D < 1 + δ`
  obtain ⟨r₀, hr₀1, hr₀ρ, hr₀D⟩ := exists_lt_pow_lt_one_add hρ hδ D
  refine ⟨r₀, hr₀1, hr₀ρ, ?_⟩
  rintro z ⟨s, hs, rfl⟩
  rw [Metric.mem_ball]
  refine hδb ?_ ?_
  · exact lt_of_lt_of_le hr₀1 hs.1
  · rw [Real.dist_eq, abs_of_pos (by linarith [hs.1] : (0:ℝ) < s - 1)]
    linarith [hs.2]

end Work.LandLeaves
