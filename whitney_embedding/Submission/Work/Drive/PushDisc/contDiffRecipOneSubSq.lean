import Mathlib

open Filter

namespace Work.Drive.PushDisc

/-- The function `x ↦ (1 - x ^ 2)⁻¹`, which is smooth on the interval `[-r, r]` when `0 ≤ r < 1`,
extends to a smooth function on all of `ℝ`. (The extension is obtained by multiplying with a
smooth bump that is `1` on `[-r, r]` and supported in `(-1, 1)`.) -/
theorem contDiffRecipOneSubSq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ Set.Icc (-r) r, g x = (1 - x ^ 2)⁻¹ := by
  -- A smooth bump which is `1` on `[-r, r]` and supported in `(-1, 1)`.
  have hrIn_pos : 0 < (r + 1) / 2 := by linarith
  have hrIn_lt_rOut : (r + 1) / 2 < (r + 3) / 4 := by linarith
  have hr_lt_hrIn : r < (r + 1) / 2 := by linarith
  let φ : ContDiffBump (0 : ℝ) := ⟨(r + 1) / 2, (r + 3) / 4, hrIn_pos, hrIn_lt_rOut⟩
  refine ⟨fun x => φ x * (1 - x ^ 2)⁻¹, ?_, ?_⟩
  · -- Smoothness: pointwise, using that `φ` vanishes near the poles `x = ±1`.
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne (x ^ 2) 1 with hx | hx
    · -- `x = ±1`: the product vanishes on a neighbourhood of `x`.
      have habs : |x| = 1 := by
        have h2 : |x| ^ 2 = 1 := by rw [sq_abs]; exact hx
        nlinarith [abs_nonneg x]
      have hxabs : (r + 3) / 4 < |x| := by rw [habs]; linarith
      have hopen : IsOpen {y : ℝ | (r + 3) / 4 < |y|} :=
        isOpen_lt continuous_const continuous_abs
      have hev0 : (fun y : ℝ => φ y) =ᶠ[nhds x] (fun _ => (0 : ℝ)) :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hxabs) (fun y hy => by
          exact φ.zero_of_le_dist (by simpa [Real.dist_eq] using le_of_lt hy))
      have hev : (fun y : ℝ => φ y * (1 - y ^ 2)⁻¹) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hev0] with y hy
        rw [hy, zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ)) (x := x)).congr_of_eventuallyEq hev
    · -- `x ≠ ±1`: both factors are smooth at `x`.
      have hsq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => y ^ 2) x :=
        contDiffAt_id.pow 2
      have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => 1 - y ^ 2) x :=
        contDiffAt_const.sub hsq
      have hne : (1 - x ^ 2) ≠ 0 := sub_ne_zero.mpr (fun h => hx h.symm)
      have h1 := hsub.inv hne
      exact φ.contDiffAt.mul h1
  · -- On `[-r, r]` the bump equals `1`.
    intro x hx
    have hxabs : |x| ≤ r := abs_le.mpr hx
    have hxmem : x ∈ Metric.closedBall (0 : ℝ) φ.rIn := by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      show |x| ≤ (r + 1) / 2
      linarith
    change φ x * (1 - x ^ 2)⁻¹ = (1 - x ^ 2)⁻¹
    rw [φ.one_of_mem_closedBall hxmem, one_mul]

end Work.Drive.PushDisc
