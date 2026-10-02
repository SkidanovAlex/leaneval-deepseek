import Mathlib
import Submission.Work.LandLeaves.snailDescentDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Set
open scoped Topology

/-- If the directions of a nonvanishing path `q` are asymptotically multiplied by `lam` along the
path, `‖q (t+1)/‖q (t+1)‖ - lam * (q t/‖q t‖)‖ → 0`, then the set of limit directions
`Work.LandLeaves.directionLimitSet q` is invariant under multiplication by `lam`.

Hint. Given `d` in the limit set and `ε > 0`, pick `t` large with `‖q t/‖q t‖ - d‖ < ε/2`, and
with `‖q t/‖q t‖ - lam * (q (t-1)/‖q (t-1)‖)‖ < ε/2` (the twist bound at `t - 1`); then
`‖q t/‖q t‖ - lam * d‖ < ε`, so `lam * d` is also an accumulation point of directions. -/
theorem directionLimitSet_invariant {q : ℝ → ℂ} {lam : ℂ}
    (hqc : ContinuousOn q (Set.Ici 0)) (hqne : ∀ t ∈ Set.Ici (0 : ℝ), q t ≠ 0)
    (htwist : Filter.Tendsto (fun t : ℝ => q (t + 1) / ((‖q (t + 1)‖ : ℝ) : ℂ)
      - lam * (q t / ((‖q t‖ : ℝ) : ℂ))) Filter.atTop (nhds 0)) :
    ∀ d ∈ Work.LandLeaves.directionLimitSet q, lam * d ∈ Work.LandLeaves.directionLimitSet q := by
  intro d hd
  -- Unfold the limit set into a pointwise statement: `d` is approached by directions at
  -- arbitrarily large times.
  simp only [directionLimitSet, Set.mem_iInter, Set.mem_Ici] at hd ⊢
  intro T hT
  -- It suffices to show that `lam * d` is in the closure of the directions past `T`, i.e. that
  -- some direction past `T` is within `ε` of `lam * d`, for every `ε > 0`.
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- The twist hypothesis bounds the deviation by `ε/2` beyond some threshold `M`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t : ℝ, M ≤ t →
      ‖q (t + 1) / ((‖q (t + 1)‖ : ℝ) : ℂ) - lam * (q t / ((‖q t‖ : ℝ) : ℂ))‖ < ε / 2 := by
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp htwist (ε / 2) hε2
    exact ⟨M, fun t ht => by simpa [dist_eq_norm] using hM t ht⟩
  -- The tolerance for the approximation of `d`: `δ := ε / (2 * (1 + ‖lam‖))`, so that
  -- `‖lam‖ * δ ≤ ε / 2` without any case distinction on `lam = 0`.
  set δ : ℝ := ε / (2 * (1 + ‖lam‖)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos hε (by positivity)
  -- Beyond `max (T+1) M` both the limit-set description of `d` and the twist bound are available.
  have hT' : (0 : ℝ) ≤ max (T + 1) M :=
    le_trans (by linarith : (0 : ℝ) ≤ T + 1) (le_max_left _ _)
  obtain ⟨y, ⟨u, hu, rfl⟩, hdy⟩ :=
    Metric.mem_closure_iff.mp (hd (max (T + 1) M) hT') δ hδpos
  simp only [Set.mem_Ici] at hu
  have huT : T ≤ u := by linarith [le_max_left (T + 1) M]
  have huM : M ≤ u := by linarith [le_max_right (T + 1) M]
  -- The witness direction: the direction at time `u + 1`, which is past `T` and close to `lam * d`
  -- because it is close both to `lam * (q u / ‖q u‖)` (twist) and to `lam * d` (`d` is a limit
  -- direction and `q u / ‖q u‖` is close to `d`).
  refine ⟨q (u + 1) / ((‖q (u + 1)‖ : ℝ) : ℂ),
    ⟨u + 1, by simp only [Set.mem_Ici]; linarith, rfl⟩, ?_⟩
  have htw : ‖q (u + 1) / ((‖q (u + 1)‖ : ℝ) : ℂ)
      - lam * (q u / ((‖q u‖ : ℝ) : ℂ))‖ < ε / 2 := hM u huM
  have hmul : dist (lam * d) (lam * (q u / ((‖q u‖ : ℝ) : ℂ)))
      = ‖lam‖ * dist d (q u / ((‖q u‖ : ℝ) : ℂ)) := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
  have htw' : dist (lam * (q u / ((‖q u‖ : ℝ) : ℂ)))
      (q (u + 1) / ((‖q (u + 1)‖ : ℝ) : ℂ))
      = ‖q (u + 1) / ((‖q (u + 1)‖ : ℝ) : ℂ)
      - lam * (q u / ((‖q u‖ : ℝ) : ℂ))‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  -- `‖lam‖ * δ ≤ ε / 2`.
  have hle : ‖lam‖ * δ ≤ ε / 2 := by
    rw [hδdef, ← mul_div_assoc]
    rw [div_le_iff₀ (show (0 : ℝ) < 2 * (1 + ‖lam‖) by positivity)]
    nlinarith [norm_nonneg lam]
  -- The triangle inequality estimate.
  have hstep : dist (lam * d) (q (u + 1) / ((‖q (u + 1)‖ : ℝ) : ℂ))
      ≤ ‖lam‖ * δ + ‖q (u + 1) / ((‖q (u + 1)‖ : ℝ) : ℂ)
          - lam * (q u / ((‖q u‖ : ℝ) : ℂ))‖ := by
    have h := dist_triangle (lam * d) (lam * (q u / ((‖q u‖ : ℝ) : ℂ)))
      (q (u + 1) / ((‖q (u + 1)‖ : ℝ) : ℂ))
    rw [hmul, htw'] at h
    exact le_trans h
      (add_le_add (mul_le_mul_of_nonneg_left hdy.le (norm_nonneg lam)) le_rfl)
  linarith

end Work.LandLeaves
