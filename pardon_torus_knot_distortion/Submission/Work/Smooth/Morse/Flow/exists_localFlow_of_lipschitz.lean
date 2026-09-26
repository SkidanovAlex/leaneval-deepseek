import Mathlib
import Submission.Work.Smooth.Morse.Defs

open Set Metric
open scoped NNReal

namespace Work.Smooth.Morse.Flow

/-- A bounded, globally Lipschitz vector field on `ℝ × ℝ` admits a local flow: for any radius `R`
of initial conditions and any time horizon `T ≥ 0`, there is a (total) map `Φ` whose time-`0` slice
is the identity on `closedBall q₀ R`, whose trajectories solve `Φ' = W ∘ Φ` on `Icc 0 T`, and
which is continuous on `Icc 0 T ×ˢ closedBall q₀ R`. -/
theorem exists_localFlow_of_lipschitz (W : ℝ × ℝ → ℝ × ℝ) {K : NNReal} (hW : LipschitzWith K W) (hb : ∀ q : ℝ × ℝ, ‖W q‖ ≤ 1) (q₀ : ℝ × ℝ) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) : ∃ Φ : ℝ × (ℝ × ℝ) → ℝ × ℝ, (∀ q ∈ Metric.closedBall q₀ R, Φ (0, q) = q) ∧ (∀ q ∈ Metric.closedBall q₀ R, ∀ u ∈ Set.Icc 0 T, HasDerivWithinAt (fun s : ℝ => Φ (s, q)) (W (Φ (u, q))) (Set.Icc 0 T) u) ∧ ContinuousOn Φ (Set.Icc 0 T ×ˢ Metric.closedBall q₀ R) := by
  -- The vector field is globally Lipschitz with constant `K` and globally bounded by `1`, so the
  -- Picard–Lindelöf theorem applies on the whole time interval `[0, T]` and on all initial points
  -- in `closedBall q₀ R`: the field conditions only need to hold on the ball of radius `R + T`,
  -- and the consistency condition `L * max (tmax - t₀) (t₀ - tmin) ≤ a - r` reads `T ≤ (R+T) - R`.
  let f : ℝ → (ℝ × ℝ) → (ℝ × ℝ) := fun _ x => W x
  let t₀ : ↑(Set.Icc (0 : ℝ) T) := ⟨0, le_rfl, hT⟩
  have hpl : IsPicardLindelof f t₀ q₀ (NNReal.mk (R + T) (add_nonneg hR hT)) (NNReal.mk R hR) 1 K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      simpa only [f] using hW.lipschitzOnWith
    · intro x hx
      simpa only [f] using continuousOn_const
    · intro t ht x hx
      simpa only [f, NNReal.coe_one] using hb x
    · have ht₀ : (↑t₀ : ℝ) = 0 := rfl
      have ha : ((NNReal.mk (R + T) (add_nonneg hR hT)) : ℝ) = R + T := rfl
      have hr : ((NNReal.mk R hR) : ℝ) = R := rfl
      have h1 : ((1 : ℝ≥0) : ℝ) = 1 := rfl
      rw [h1, ht₀, ha, hr]
      simp only [sub_zero, max_eq_left hT, one_mul]
      linarith
  obtain ⟨α, hα, hcont⟩ := hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨fun p : ℝ × (ℝ × ℝ) => α (p.2, p.1), ?_, ?_, ?_⟩
  · intro q hq
    exact (hα q hq).1
  · intro q hq u hu
    simpa only [f] using (hα q hq).2 u hu
  · have hmap : MapsTo (Prod.swap : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ)
        (Set.Icc 0 T ×ˢ Metric.closedBall q₀ R)
        (Metric.closedBall q₀ ((NNReal.mk R hR : ℝ≥0) : ℝ) ×ˢ Set.Icc 0 T) := by
      intro p hp
      exact ⟨hp.2, hp.1⟩
    exact hcont.comp continuous_swap.continuousOn hmap

end Work.Smooth.Morse.Flow
