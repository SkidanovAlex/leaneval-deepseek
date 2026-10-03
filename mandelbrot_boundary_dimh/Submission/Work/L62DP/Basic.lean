import Mathlib

/-!
# Auxiliary lemmas for the deep inverse branch

This file collects the elementary ingredients of `Work.L62.deep_preimage_deep`:

* `mem_comap_im_atBot_iff` / `tendsto_comap_im_atBot_iff` — the filter
  `Filter.comap Complex.im Filter.atBot` (convergence at the lower end, uniformly in `Re`) is
  membership in a deep half plane, and its `ε`-form.
* `norm_deriv_le_of_halfplane_deep` — Cauchy's estimate on a deep half plane: a function
  holomorphic and bounded by `B` on `{im < Y}` has `‖deriv f u‖ ≤ B / r` on `{im < Y - r}`.
* `im_le_of_mem_closedBall`, `mem_closedBall_of_le` — small `im`/distance conversions.
-/

namespace Work.L62DP

open Filter Set Metric

/-! ## The filter `comap Complex.im atBot` -/

/-- Membership in `Filter.comap Complex.im Filter.atBot` is membership in some deep half plane
`{z | z.im < T}`. -/
theorem mem_comap_im_atBot_iff {S : Set ℂ} :
    S ∈ Filter.comap Complex.im Filter.atBot ↔ ∃ T : ℝ, ∀ z : ℂ, z.im < T → z ∈ S := by
  constructor
  · intro hS
    rw [Filter.mem_comap] at hS
    obtain ⟨t, ht, hts⟩ := hS
    obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp ht
    exact ⟨a, fun z hz => hts (ha z.im (le_of_lt hz))⟩
  · rintro ⟨T, hT⟩
    rw [Filter.mem_comap]
    refine ⟨Set.Iio T, ?_, ?_⟩
    · exact Filter.eventually_atBot.mpr ⟨T - 1, fun b hb => by linarith⟩
    · intro z hz
      exact hT z hz

/-- `ε`-form of convergence along the lower end. -/
theorem tendsto_comap_im_atBot_iff {f : ℂ → ℂ} {a : ℂ} :
    Filter.Tendsto f (Filter.comap Complex.im Filter.atBot) (nhds a) ↔
      ∀ ε > 0, ∃ T : ℝ, ∀ z : ℂ, z.im < T → ‖f z - a‖ < ε := by
  constructor
  · intro h ε hε
    have hS : {z : ℂ | f z ∈ Metric.ball a ε} ∈ Filter.comap Complex.im Filter.atBot :=
      h (Metric.ball_mem_nhds a hε)
    obtain ⟨T, hT⟩ := mem_comap_im_atBot_iff.mp hS
    exact ⟨T, fun z hz => by
      simpa [Metric.mem_ball, dist_eq_norm] using hT z hz⟩
  · intro h
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨T, hT⟩ := h ε hε
    exact mem_comap_im_atBot_iff.mpr ⟨T, fun z hz => by
      simpa [dist_eq_norm] using hT z hz⟩

/-! ## Cauchy's estimate on a deep half plane -/

/-- **Cauchy estimate on a deep half plane.**  A function holomorphic on the half plane
`{z | z.im < Y}` and bounded there by `B` has derivative bounded by `B / r` at every point of the
strictly deeper half plane `{z | z.im < Y - r}` (the ball of radius `r` about such a point is
contained in `{z | z.im < Y}`). -/
theorem norm_deriv_le_of_halfplane_deep {f : ℂ → ℂ} {Y B r : ℝ} (hr : 0 < r)
    (hhol : DifferentiableOn ℂ f {z : ℂ | z.im < Y})
    (hbd : ∀ z : ℂ, z.im < Y → ‖f z‖ ≤ B) {u : ℂ} (hu : u.im < Y - r) :
    ‖deriv f u‖ ≤ B / r := by
  have hclosed : Metric.closedBall u r ⊆ {z : ℂ | z.im < Y} := by
    intro z hz
    have h1 : ‖z - u‖ ≤ r := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact hz
    have h2 : z.im - u.im ≤ ‖z - u‖ := by
      have h3 := Complex.im_le_norm (z - u)
      rw [Complex.sub_im] at h3
      exact h3
    show z.im < Y
    linarith
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ ?_
  · exact (hhol.mono hclosed).diffContOnCl_ball subset_rfl
  · intro z hz
    exact hbd z (hclosed (Metric.sphere_subset_closedBall hz))

/-! ## Elementary `im`/distance conversions -/

theorem im_sub_le_norm (a b : ℂ) : a.im - b.im ≤ ‖a - b‖ := by
  have h := Complex.im_le_norm (a - b)
  rwa [Complex.sub_im] at h

/-- A point of a closed ball lies at most `r` above the centre's imaginary part. -/
theorem im_le_of_mem_closedBall {a b : ℂ} {r : ℝ} (h : b ∈ Metric.closedBall a r) :
    b.im ≤ a.im + r := by
  have h1 : ‖b - a‖ ≤ r := by
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    exact h
  have h2 := im_sub_le_norm b a
  linarith

theorem mem_closedBall_of_le {a b : ℂ} {r : ℝ} (h : ‖b - a‖ ≤ r) :
    b ∈ Metric.closedBall a r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact h

end Work.L62DP
