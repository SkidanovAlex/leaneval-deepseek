import Mathlib
import Submission.Work.Geo.Radial.RadialDefs
import Submission.Work.Geo.Radial.radRho_continuous
import Submission.Work.Geo.Radial.radRho_facts
import Submission.Work.Geo.Radial.radStretchInv_facts

namespace Work.Geo.Radial

open Set Metric
open scoped Topology

theorem radPushInv_continuous {n : ℕ} [NeZero n] {ε R S s : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (hεS : ε < S) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hmono : StrictMono (radStretch ε R S s))
    (hsurj : Function.Surjective (radStretch ε R S s)) :
    Continuous (radPushInv (n := n) ε R S s) := by
  obtain ⟨hinv, hright, hcont, hnonneg, hle⟩ :=
    radStretchInv_facts hε hεR hεS hs0 hs1 hmono hsurj
  obtain ⟨hrho0, hrhobound, hrhozero, hrhosmul, hrhocube, hrhocube2⟩ := radRho_facts (n := n)
  -- The scalar coefficient `radStretchInv r / r` is bounded by `1` on `r ≥ 0`.
  have hcbound : ∀ r : ℝ, 0 ≤ r → |radStretchInv ε R S s r / r| ≤ 1 := by
    intro r hr
    rcases eq_or_lt_of_le hr with h | h
    · subst h; simp
    · rw [abs_of_nonneg (div_nonneg (hnonneg r hr) hr), div_le_one h]
      exact hle r hr
  -- Hence `radPushInv` does not increase the norm.
  have hnorm : ∀ y : PL.E n, ‖radPushInv ε R S s y‖ ≤ ‖y‖ := by
    intro y
    have hy : 0 ≤ radRho y := hrho0 y
    change ‖(radStretchInv ε R S s (radRho y) / radRho y) • y‖ ≤ ‖y‖
    rw [norm_smul, Real.norm_eq_abs]
    calc |radStretchInv ε R S s (radRho y) / radRho y| * ‖y‖
        ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hcbound (radRho y) hy) (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  have hzero : radPushInv ε R S s (0 : PL.E n) = 0 := by simp [radPushInv]
  rw [continuous_iff_continuousAt]
  intro y₀
  rcases eq_or_ne y₀ 0 with rfl | hy₀
  · -- At the origin the coefficient is singular, but the norm bound makes the map tend to `0`.
    show Filter.Tendsto (radPushInv ε R S s) (𝓝 0) (𝓝 (radPushInv ε R S s 0))
    rw [hzero, tendsto_zero_iff_norm_tendsto_zero]
    have hnorm_tend : Filter.Tendsto (fun y : PL.E n => ‖y‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : PL.E n))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := (0 : ℝ)))
      hnorm_tend ?_ ?_
    · intro y; exact norm_nonneg _
    · intro y; exact hnorm y
  · -- Away from the origin `radRho y₀ > 0`, so the coefficient is continuous.
    have hy₀pos : 0 < radRho y₀ := by
      have hne : radRho y₀ ≠ 0 := fun h => hy₀ ((hrhozero y₀).mp h)
      exact lt_of_le_of_ne (hrho0 y₀) (Ne.symm hne)
    change ContinuousAt (fun y : PL.E n =>
      (radStretchInv ε R S s (radRho y) / radRho y) • y) y₀
    exact ContinuousAt.smul
      (ContinuousAt.div (hcont.continuousAt.comp radRho_continuous.continuousAt)
        radRho_continuous.continuousAt (ne_of_gt hy₀pos))
      continuousAt_id

end Work.Geo.Radial
