import Mathlib
import Submission.Work.Smooth.SphereJordan.radialModelAux

/-!
# Basic geometry of a frontier point of a finite union of equal discs

The four elementary facts about a point `x` of the frontier of `S = ⋃ w ∈ Q, closedBall w r`
(`0 < r`) that the local-arc analysis at `x` rests on:

* `localComplement_eq` -- the local complement in polar coordinates (the form of
  `localRadialModelAux` used below);
* `active_nonempty` -- some sphere passes through `x`;
* `exists_gap_of_ne` -- the balls not passing through `x` keep a uniform positive gap;
* `dist_ge_of_frontier` -- every ball has distance at least `r` from `x`.

They live here (rather than in `frontierComponentLocallyArc`) so that the local analysis can be
layered below the main theorem.
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

open scoped Classical

/-- **The local complement in polar coordinates.**  At a frontier point `x` of a finite union of
equal closed balls there is `ε > 0` such that the points of the complement inside `ball x ε` are
exactly the points `x + ρ * u` with `u` a unit vector, `0 < ρ < ε`, and `ρ` strictly above the
"reach" of every ball whose sphere passes through `x`.  This is the polar-coordinate form of
`localRadialModelAux`. -/
theorem localComplement_eq (Q : Finset ℂ) {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r)) :
    ∃ ε > 0, ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) ∩ Metric.ball x ε =
      {y : ℂ | ∃ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 ∧ 0 < ρ ∧ ρ < ε ∧ y = x + ρ * u ∧
        ∀ w ∈ Q, dist x w = r → 2 * (star u * (w - x)).re < ρ} := by
  obtain ⟨ε, hεpos, hmodel⟩ := localRadialModelAux hr hx
  have hxS : x ∈ ⋃ w ∈ Q, Metric.closedBall w r :=
    (isClosed_biUnion_finset (s := Q) (f := fun w => Metric.closedBall w r)
      (fun w _ => Metric.isClosed_closedBall)).closure_eq ▸ hx.1
  refine ⟨ε, hεpos, ?_⟩
  ext y
  constructor
  · rintro ⟨hyS, hyb⟩
    have hyne : y ≠ x := fun h => hyS (h ▸ hxS)
    have hvne : y - x ≠ 0 := sub_ne_zero.mpr hyne
    have hρ0 : 0 < ‖y - x‖ := norm_pos_iff.mpr hvne
    refine ⟨(y - x) / (‖y - x‖ : ℂ), ‖y - x‖, ?_, hρ0, ?_, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact div_self (ne_of_gt hρ0)
    · rw [Metric.mem_ball, dist_eq_norm] at hyb; exact hyb
    · rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hρ0)), add_sub_cancel]
    · intro w hw hwx
      have hu' : ‖(y - x) / (‖y - x‖ : ℂ)‖ = 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact div_self (ne_of_gt hρ0)
      have hρε : ‖y - x‖ < ε := by
        rw [Metric.mem_ball, dist_eq_norm] at hyb; exact hyb
      by_contra hcon
      rw [not_lt] at hcon
      have hmem : x + ‖y - x‖ * ((y - x) / (‖y - x‖ : ℂ)) ∈ ⋃ w ∈ Q, Metric.closedBall w r :=
        (hmodel _ _ hu' hρ0 hρε).mpr ⟨w, hw, hwx, hcon⟩
      rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hρ0)), add_sub_cancel] at hmem
      exact hyS hmem
  · rintro ⟨u, ρ, hu, hρ0, hρε, rfl, hcond⟩
    refine ⟨?_, ?_⟩
    · intro hmem
      obtain ⟨w, hw, hwx, hle⟩ := (hmodel u ρ hu hρ0 hρε).mp hmem
      have := hcond w hw hwx
      linarith
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : x + ρ * u - x = ρ * u := by ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hu, mul_one]
      exact hρε


/-- **A frontier point lies on the sphere of one of the balls.** -/
theorem active_nonempty {Q : Finset ℂ} {r : ℝ} {x : ℂ}
    (hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r)) :
    ∃ w ∈ Q, dist x w = r := by
  have hxS : x ∈ ⋃ w ∈ Q, Metric.closedBall w r :=
    (isClosed_biUnion_finset (s := Q) (f := fun w => Metric.closedBall w r)
      (fun w _ => Metric.isClosed_closedBall)).closure_eq ▸ hx.1
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxS
  refine ⟨w, hw, le_antisymm (Metric.mem_closedBall.mp hxw) ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hint : x ∈ interior (⋃ w ∈ Q, Metric.closedBall w r) :=
    interior_mono (fun y hy => Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩)
      (Metric.ball_subset_interior_closedBall (Metric.mem_ball.mpr hlt))
  exact hx.2 hint

/-- **Uniform gap for the balls not passing through `x`.** -/
theorem exists_gap_of_ne {Q : Finset ℂ} {r : ℝ} {x : ℂ}
    (hge : ∀ w ∈ Q, r ≤ dist x w) :
    ∃ δ > 0, ∀ w ∈ Q, dist x w ≠ r → r + δ ≤ dist x w := by
  set Q' : Finset ℂ := Q.filter (fun w => dist x w ≠ r) with hQ'
  rcases Q'.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, fun w hw hne' => ?_⟩
    have hmem : w ∈ Q' := by rw [hQ']; exact Finset.mem_filter.mpr ⟨hw, hne'⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty w)
  · obtain ⟨w₀, hw₀, hmin⟩ := Q'.exists_min_image (fun w => dist x w) hne
    have hlt : r < dist x w₀ := lt_of_le_of_ne (hge w₀ (Finset.mem_filter.mp hw₀).1)
      (fun hc => (Finset.mem_filter.mp hw₀).2 hc.symm)
    refine ⟨(dist x w₀ - r) / 2, by linarith, fun w hw hne' => ?_⟩
    have hmem : w ∈ Q' := Finset.mem_filter.mpr ⟨hw, hne'⟩
    have := hmin w hmem
    linarith

/-- At a frontier point the balls have distance at least `r` from `x`. -/
theorem dist_ge_of_frontier {Q : Finset ℂ} {r : ℝ} {x : ℂ}
    (hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r)) :
    ∀ w ∈ Q, r ≤ dist x w := by
  intro w hw
  by_contra hcon
  rw [not_le] at hcon
  have hint : x ∈ interior (⋃ w ∈ Q, Metric.closedBall w r) :=
    interior_mono (fun y hy => Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩)
      (Metric.ball_subset_interior_closedBall (Metric.mem_ball.mpr hcon))
  exact hx.2 hint
end

end Work.Smooth.SphereJordan
