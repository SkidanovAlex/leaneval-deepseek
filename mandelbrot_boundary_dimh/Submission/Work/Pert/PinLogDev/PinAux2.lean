import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.PinLogDev.PinAux2`

Small algebraic/arithmetic helpers shared by the assembly of
`Work.Pert.PinLogDev.anchor_point_bound2` and its children.

* the σ-normalisation of `τ_f` (`tauC_mul_u0`, `one_sub_mul_eq`), copied from
  `Submission/Work/Pert/PinLogDev/anchor_point_bound.lean` (which is NOT importable: its target
  still carries a `sorry`);
* the "relative lattice separation" at `c = 1/2` (`half_norm_le_iInf_dist`): a point of modulus
  `≤ 2/3` is at distance `≥ ‖z‖/2` from `ℤ`;
* `‖α‖ M ≤ 1/2` and `InF1 α` force `(1/α).re ≥ √2 M` (`sqrt2_mul_le_re_inv`);
* margins of the gate imply the ball of the corresponding radius is contained in the gate
  (`ball_subset_Qm_of_marg`).
-/

namespace Work.Pert.PinLogDev

open Complex Metric Set

noncomputable section

/-! ## The σ-normalisation of `τ` -/

/-- `τ` with the normalised `σ' = σ u 0` is `u 0` times `τ` with `σ`. -/
theorem tauC_mul_u0 (u : ℂ → ℂ) (σ α w : ℂ) :
    Work.Pert.tauC (σ * u 0) α w = u 0 * Work.Pert.tauC σ α w := by
  unfold Work.Pert.tauC
  rw [mul_div_assoc', mul_comm σ (u 0)]

/-- The gate hypothesis `1 - σ u 0 = exp (2π i α)` says that `σ u 0` is the normalised
value `1 - exp (2π i α)`. -/
theorem one_sub_mul_eq {u : ℂ → ℂ} {σ α : ℂ}
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α)) :
    σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
  rw [← hnorm]; ring

/-! ## Separation from the lattice -/

/-- If `‖α * w‖ ≤ 1/2`, then `‖α‖ ‖w‖ ≤ dist (α * w) ℤ` (the relative separation at `c = 1`). -/
theorem norm_mul_le_iInf_dist {α w : ℂ} (h : ‖α * w‖ ≤ 1 / 2) :
    ‖α‖ * ‖w‖ ≤ (⨅ k : ℤ, dist (α * w) (k : ℂ)) := by
  rw [← norm_mul]
  refine le_ciInf ?_
  intro k
  rw [dist_eq_norm]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have hk1' : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast hk1'
    have h2 : ‖(k : ℂ)‖ = |(k : ℝ)| := by simp
    have h3 : ‖(k : ℂ)‖ ≤ ‖α * w‖ + ‖α * w - (k : ℂ)‖ := by
      have hb := norm_add_le (α * w) ((k : ℂ) - α * w)
      have he : α * w + ((k : ℂ) - α * w) = (k : ℂ) := by ring
      rw [he] at hb
      have he2 : ‖(k : ℂ) - α * w‖ = ‖α * w - (k : ℂ)‖ := norm_sub_rev _ _
      linarith [hb, he2.le, he2.ge]
    rw [h2] at h3
    linarith

/-- A complex number of modulus `≤ 2/3` is at distance `≥ ‖z‖/2` from `ℤ`. -/
theorem half_norm_le_iInf_dist {z : ℂ} (hz : ‖z‖ ≤ 2 / 3) :
    (1 / 2) * ‖z‖ ≤ (⨅ k : ℤ, dist z (k : ℂ)) := by
  refine le_ciInf ?_
  intro k
  rw [dist_eq_norm]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    rw [Int.cast_zero, sub_zero]
    linarith [norm_nonneg z]
  · have hk1 : (1 : ℝ) ≤ ‖(k : ℂ)‖ := by
      have hk1' : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      have h2 : ‖(k : ℂ)‖ = |(k : ℝ)| := by simp
      rw [h2]
      exact_mod_cast hk1'
    have h3 : ‖(k : ℂ)‖ - ‖z‖ ≤ ‖(k : ℂ) - z‖ := norm_sub_norm_le _ _
    have h4 : ‖(k : ℂ) - z‖ = ‖z - (k : ℂ)‖ := norm_sub_rev _ _
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    linarith [h3, h4, hz, hk1, hz0]

/-! ## The apex `1/α` of the gate is large -/

/-- Under `InF1 α` and `‖α‖ M ≤ 1/2` the real part of the apex `1/α` of the gate dominates
`√2 M`. -/
theorem sqrt2_mul_le_re_inv {α : ℂ} {M : ℝ} (hα : MandelDim.InF1 α) (hM : 0 < M)
    (hαM : ‖α‖ * M ≤ 1 / 2) : Real.sqrt 2 * M ≤ (1 / α).re := by
  have hposre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hα
  have hne : α ≠ 0 := fun h => by rw [h] at hposre; simp at hposre
  have hnormα : 0 < ‖α‖ := norm_pos_iff.mpr hne
  -- the imaginary part of `1/α` is bounded by its real part
  have him : |(1 / α).im| ≤ (1 / α).re := by
    rw [one_div, Complex.inv_re, Complex.inv_im]
    have h2 : 0 < Complex.normSq α := by
      rw [Complex.normSq_pos]; exact hne
    rw [abs_div, abs_neg, abs_of_pos h2, div_le_div_iff_of_pos_right h2]
    exact le_of_lt hα
  have hre0 : 0 ≤ (1 / α).re := le_trans (abs_nonneg _) him
  have hsq : ‖1 / α‖ ^ 2 = (1 / α).re ^ 2 + (1 / α).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnorm1 : ‖1 / α‖ = 1 / ‖α‖ := by rw [norm_div, norm_one]
  have h2M : 2 * M ≤ ‖1 / α‖ := by
    rw [hnorm1, le_div_iff₀ hnormα]
    linarith
  have hsq2 : (2 * M) ^ 2 ≤ ((1 / α).re) ^ 2 + ((1 / α).im) ^ 2 := by
    rw [← hsq]
    exact pow_le_pow_left₀ (by positivity) h2M 2
  have himsq : ((1 / α).im) ^ 2 ≤ ((1 / α).re) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg ((1 / α).im)) him 2
    simpa using this
  have hkey : 2 * M ≤ Real.sqrt 2 * (1 / α).re := by
    have hle : (2 * M) ^ 2 ≤ (Real.sqrt 2 * (1 / α).re) ^ 2 := by
      have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [hsq2, himsq, hs]
    have hnn : 0 ≤ Real.sqrt 2 * (1 / α).re := by positivity
    calc 2 * M = Real.sqrt ((2 * M) ^ 2) := by rw [Real.sqrt_sq (by linarith)]
      _ ≤ Real.sqrt ((Real.sqrt 2 * (1 / α).re) ^ 2) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt 2 * (1 / α).re := Real.sqrt_sq hnn
  have h3 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hgoal : Real.sqrt 2 * M ≤ (1 / α).re := by
    have h2 : Real.sqrt 2 * M = (2 * M) / Real.sqrt 2 := by
      rw [eq_div_iff (ne_of_gt h3)]
      have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [hs]
    rw [h2, div_le_iff₀ h3]
    linarith [hkey]
  exact hgoal

/-! ## Margins and the gate -/

/-- If `z` is in the gate with both margins `≥ √2 r`, then `ball z r ⊆ Qm ξ α`. -/
theorem ball_subset_Qm_of_marg {ξ : ℝ} {α z : ℂ} {r : ℝ} (hz : z ∈ Work.Pert.Qm ξ α)
    (hA : Real.sqrt 2 * r ≤ Work.Pert.margA ξ α z)
    (hB : Real.sqrt 2 * r ≤ Work.Pert.margB ξ α z) :
    Metric.ball z r ⊆ Work.Pert.Qm ξ α := by
  intro u hu
  by_contra hcon
  have h := Work.Pert.min_marg_div_le_dist hz hcon
  rw [dist_comm, dist_eq_norm] at h
  have h2 : Real.sqrt 2 * r ≤ min (Work.Pert.margA ξ α z) (Work.Pert.margB ξ α z) :=
    le_min hA hB
  have h3 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h4 : r ≤ min (Work.Pert.margA ξ α z) (Work.Pert.margB ξ α z) / Real.sqrt 2 := by
    rw [le_div_iff₀ h3]; linarith
  have hu' : ‖u - z‖ < r := by simpa [dist_eq_norm] using hu
  linarith

end

end Work.Pert.PinLogDev
