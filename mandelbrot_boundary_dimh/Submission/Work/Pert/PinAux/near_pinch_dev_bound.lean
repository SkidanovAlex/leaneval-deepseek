import Mathlib
import Submission.Work.Pert.PinAux.Defs

namespace Work.Pert.PinAux

open MandelDim Complex Metric Set

/-!
# `Work.Pert.PinAux.near_pinch_dev_bound`

The deviation `Dev Φ = Φ - id` of a Fatou coordinate `Φ` (holomorphic on the gate `Qm Ξ α`) is
bounded, uniformly in the height `t` running over a bounded window `|t| ≤ Tmax`, at the medial
points `med Ξ α t` of the gate — *provided* that at each such height some point `z` of the gate
carries an `R₁`-ball still inside the gate.

The point of the hypothesis is that the existence of such a `z` at height `t` forces both margins
of the *medial* point at height `t` to be at least `R₁ > 0` (`marg_med_ge_of_ball`).  Hence all
admissible medians lie in the compact set

  `K = (med Ξ α '' [−Tmax, Tmax]) ∩ {w | R₁ ≤ margA Ξ α w ∧ R₁ ≤ margB Ξ α w}`,

which is a compact subset of the (open) gate `Qm Ξ α`.  A function continuous on the gate is
bounded on `K`, and `w ↦ ‖w‖` is bounded on the compact `med Ξ α '' [−Tmax, Tmax]`; the sum of the
two bounds is the required `M`.  (No openness of the gate is needed: `ContinuousOn.mono` restricts
`ContinuousOn Φ (Qm Ξ α)` to `K`.)
-/

/-- Continuity of the medial map `t ↦ med Ξ α t`. -/
private lemma continuous_med (Ξ : ℝ) (α : ℂ) : Continuous (fun t : ℝ => med Ξ α t) := by
  unfold med xMid sliceLo sliceHi
  fun_prop

/-- The set of medial points admissible at heights `|t| ≤ Tmax` is contained in a compact subset
of the gate, so `Dev Φ` is bounded on it. -/
theorem near_pinch_dev_bound {Φ : ℂ → ℂ} {Ξ R₁ Tmax : ℝ} {α : ℂ}
    (hR₁ : 0 < R₁) (hΦ : DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α)) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, |t| ≤ Tmax → ∀ z : ℂ, z.im = t →
      z ∈ Work.Pert.Qm Ξ α → Metric.ball z R₁ ⊆ Work.Pert.Qm Ξ α →
        ‖Work.Pert.PinAux.Dev Φ (Work.Pert.PinAux.med Ξ α t)‖ ≤ M := by
  -- the compact set of medial points over the height window
  have hcpt : IsCompact (med Ξ α '' Set.Icc (-Tmax) Tmax) :=
    isCompact_Icc.image (continuous_med Ξ α)
  -- the margin condition `R₁ ≤ margA ∧ R₁ ≤ margB` is closed
  have hclosed : IsClosed {w : ℂ | R₁ ≤ margA Ξ α w ∧ R₁ ≤ margB Ξ α w} := by
    have h1 : IsClosed {w : ℂ | R₁ ≤ margA Ξ α w} :=
      isClosed_le continuous_const (by unfold margA; fun_prop)
    have h2 : IsClosed {w : ℂ | R₁ ≤ margB Ξ α w} :=
      isClosed_le continuous_const (by unfold margB; fun_prop)
    simpa [Set.ofPred_and] using h1.inter h2
  -- the compact carrier of all admissible medial points
  have hKcpt : IsCompact ((med Ξ α '' Set.Icc (-Tmax) Tmax)
      ∩ {w : ℂ | R₁ ≤ margA Ξ α w ∧ R₁ ≤ margB Ξ α w}) :=
    hcpt.inter_right hclosed
  -- it lies in the gate, where `Φ` is continuous
  have hKQ : ((med Ξ α '' Set.Icc (-Tmax) Tmax)
      ∩ {w : ℂ | R₁ ≤ margA Ξ α w ∧ R₁ ≤ margB Ξ α w}) ⊆ Qm Ξ α := by
    intro w hw
    obtain ⟨-, hA, hB⟩ := hw
    rw [mem_Qm_iff_marg]
    exact ⟨lt_of_lt_of_le hR₁ hA, lt_of_lt_of_le hR₁ hB⟩
  have hcontΦ : ContinuousOn Φ ((med Ξ α '' Set.Icc (-Tmax) Tmax)
      ∩ {w : ℂ | R₁ ≤ margA Ξ α w ∧ R₁ ≤ margB Ξ α w}) :=
    hΦ.continuousOn.mono hKQ
  obtain ⟨C₁, hC₁⟩ := hKcpt.exists_bound_of_continuousOn hcontΦ
  obtain ⟨C₂, hC₂⟩ := hcpt.exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨max 1 (C₁ + C₂), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht z hz _hzQ hball
  have htI : t ∈ Set.Icc (-Tmax) Tmax := by
    rw [Set.mem_Icc]
    exact ⟨(abs_le.mp ht).1, (abs_le.mp ht).2⟩
  -- the medial point at height `t` carries both margins `≥ R₁`, hence lies in the carrier
  have hmedK : med Ξ α t ∈ (med Ξ α '' Set.Icc (-Tmax) Tmax)
      ∩ {w : ℂ | R₁ ≤ margA Ξ α w ∧ R₁ ≤ margB Ξ α w} := by
    refine ⟨⟨t, htI, rfl⟩, ?_⟩
    have hge := marg_med_ge_of_ball (Ξ := Ξ) (α := α) (z := z) hR₁ hball
    rwa [hz] at hge
  have hb1 : ‖Φ (med Ξ α t)‖ ≤ C₁ := hC₁ _ hmedK
  have hb2 : ‖med Ξ α t‖ ≤ C₂ := hC₂ _ hmedK.1
  have hb3 : ‖Dev Φ (med Ξ α t)‖ ≤ ‖Φ (med Ξ α t)‖ + ‖med Ξ α t‖ := by
    rw [Dev]; exact norm_sub_le _ _
  linarith [hb1, hb2, hb3, le_max_right (1 : ℝ) (C₁ + C₂)]

end Work.Pert.PinAux
