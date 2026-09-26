import Mathlib
import Submission.Work.Smooth.Jordan.All

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.BoxShrink.PinchOff

open Set Metric

/-- **Collar lemma for the model disc.**  An open subset of the closed unit disc that contains the
whole boundary circle contains a thin annulus `{z | 1 - δ ≤ ‖z‖}`.

Indeed the complement is closed in the compact disc, hence compact; if it is nonempty it attains
its maximum norm `≤ 1`, which is `< 1` because the boundary circle misses it. -/
theorem exists_annulus_subset_of_isOpen_of_sphere_subset
    {W : Set Work.Smooth.Jordan.Disc} (hW : IsOpen W)
    (hS : ∀ z : Work.Smooth.Jordan.Disc, ‖(z : ℂ)‖ = 1 → z ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : Work.Smooth.Jordan.Disc, 1 - δ ≤ ‖(z : ℂ)‖ → z ∈ W := by
  classical
  haveI : CompactSpace Work.Smooth.Jordan.Disc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  rcases eq_empty_or_nonempty (Wᶜ) with hempty | hne
  · have hWuniv : W = univ := by rw [← compl_compl W, hempty, compl_empty]
    exact ⟨1/2, by norm_num, fun z _ => by rw [hWuniv]; exact mem_univ z⟩
  · obtain ⟨w₀, hw₀T, hw₀max⟩ := (hW.isClosed_compl.isCompact).exists_isMaxOn hne
      (continuous_subtype_val.norm.continuousOn)
    have hw₀le : ‖(w₀ : ℂ)‖ ≤ 1 := by
      have h := w₀.2
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hw₀ne : ‖(w₀ : ℂ)‖ ≠ 1 := fun h1 => hw₀T (hS w₀ h1)
    have hw₀lt : ‖(w₀ : ℂ)‖ < 1 := lt_of_le_of_ne hw₀le hw₀ne
    refine ⟨(1 - ‖(w₀ : ℂ)‖)/2, by linarith, fun z hz => ?_⟩
    by_contra hzW
    have hzT : z ∈ Wᶜ := hzW
    have hmax : ‖(z : ℂ)‖ ≤ ‖(w₀ : ℂ)‖ := hw₀max hzT
    linarith

/-- **Only a thin annulus of the model disc can map near the boundary of the plane.**

For a continuous `E : 𝔻 → S²` with `E (circlePoint θ) = ↑(c.γ θ)` for all `θ`, `E u₀ = ∞`, and
`ε > 0`, there is `δ > 0` such that:

* the marked point `u₀` is *not* in the annulus `{w : 𝔻 | 1 - δ ≤ ‖w‖}` (equivalently
  `‖u₀‖ < 1 - δ`), and
* every `w` in that annulus has `E w` either `∞` or a finite point at distance `< ε` from the curve
  `range c.γ`.

(Proof of the second clause: the sets `E ⁻¹' {p : dist p (c.γ θ) < ε}` for `θ` ranging over a set
of parameters of the boundary circle form an open cover of the compact boundary circle, so by
compactness a finite subcover contains an annulus `{1 - δ ≤ ‖w‖}`.  The first clause then follows
because `E u₀ = ∞` is not in the ball `{p : dist p (c.γ θ) < ε} ⊆ ℂ`.) -/
theorem exists_delta_infDist_lt
    {c : Work.Smooth.Jordan.PlaneCurve} (h : Work.Smooth.Jordan.PlaneSeparation c)
    {ε : ℝ} (hε : 0 < ε)
    {E : Work.Smooth.Jordan.Disc → OnePoint ℂ} (hE : Continuous E)
    (hEb : ∀ θ : ℝ, E (Work.Smooth.Jordan.circlePoint θ) = ((c.γ θ : ℂ) : OnePoint ℂ))
    {u₀ : Work.Smooth.Jordan.Disc} (hEu₀ : E u₀ = OnePoint.infty) :
    ∃ δ : ℝ, 0 < δ ∧ ‖(u₀ : ℂ)‖ < 1 - δ ∧
      ∀ w : Work.Smooth.Jordan.Disc, 1 - δ ≤ ‖(w : ℂ)‖ →
        ¬ (∃ z : ℂ, E w = (z : OnePoint ℂ) ∧ ε ≤ Metric.infDist z (Set.range c.γ)) := by
  classical
  -- The set of plane points strictly within `ε` of the curve; it is open in `ℂ`, and does not
  -- contain the point `∞` of `OnePoint ℂ`.
  set G : Set ℂ := {z : ℂ | Metric.infDist z (Set.range c.γ) < ε}
  have hGopen : IsOpen G := isOpen_Iio.preimage (continuous_infDist_pt (Set.range c.γ))
  -- Its image in `OnePoint ℂ` is open (the coercion is an open embedding and never hits `∞`), so
  -- the preimage `W` is an open set on which `E` is finite and close to the curve.
  set W : Set Work.Smooth.Jordan.Disc := E ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' G)
  have hWopen : IsOpen W := (OnePoint.isOpen_image_coe.mpr hGopen).preimage hE
  -- Every point of the boundary circle maps into `W`.
  have hSsub : ∀ z : Work.Smooth.Jordan.Disc, ‖(z : ℂ)‖ = 1 → z ∈ W := by
    intro z hz
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    have h1 : E z = ((c.γ θ : ℂ) : OnePoint ℂ) := by rw [← hθ]; exact hEb θ
    have hle := Metric.infDist_le_dist_of_mem (x := c.γ θ) (s := Set.range c.γ) ⟨θ, rfl⟩
    have hmem : c.γ θ ∈ G := by
      have : Metric.infDist (c.γ θ) (Set.range c.γ) < ε := by
        linarith [dist_self (c.γ θ)]
      exact this
    exact ⟨c.γ θ, hmem, h1.symm⟩
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := exists_annulus_subset_of_isOpen_of_sphere_subset hWopen hSsub
  -- On `W` the conclusion of the second clause holds: `E` is finite there and strictly within
  -- `ε` of the curve.
  have hgood : ∀ w : Work.Smooth.Jordan.Disc, w ∈ W →
      ¬ (∃ z : ℂ, E w = (z : OnePoint ℂ) ∧ ε ≤ Metric.infDist z (Set.range c.γ)) := by
    rintro w hw ⟨z', hz', hz'le⟩
    obtain ⟨z, hzG, hzEq⟩ := hw
    have hzz : z = z' := OnePoint.coe_injective (hzEq.trans hz')
    rw [hzz] at hzG
    exact absurd hzG (not_lt.mpr hz'le)
  -- The marked point `u₀` is not on the boundary circle, so it lies strictly inside the open disc.
  have hu₀le : ‖(u₀ : ℂ)‖ ≤ 1 := by
    have h := u₀.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hu₀ne : ‖(u₀ : ℂ)‖ ≠ 1 := by
    intro h1
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq u₀ h1
    have h2 : E (Work.Smooth.Jordan.circlePoint θ) = OnePoint.infty := by rw [hθ]; exact hEu₀
    have h3 : ((c.γ θ : ℂ) : OnePoint ℂ) = OnePoint.infty := by rw [← hEb θ]; exact h2
    exact OnePoint.coe_ne_infty (c.γ θ) h3
  have hu₀lt : ‖(u₀ : ℂ)‖ < 1 := lt_of_le_of_ne hu₀le hu₀ne
  -- Shrink the collar width so that `u₀` drops out of the annulus.
  refine ⟨min δ₀ ((1 - ‖(u₀ : ℂ)‖)/2), lt_min hδ₀pos (by linarith), ?_, ?_⟩
  · have h := min_le_right δ₀ ((1 - ‖(u₀ : ℂ)‖)/2); linarith
  · intro w hw
    have hle : min δ₀ ((1 - ‖(u₀ : ℂ)‖)/2) ≤ δ₀ := min_le_left _ _
    exact hgood w (hδ₀ w (by linarith))

end Work.BoxShrink.PinchOff
