import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk
import Submission.Work.Pert.Ksub2.deriv_phi_deep_upper

namespace Work.Pert.Ksub2

open Complex Metric

/-- If `z` lies in the closed `r`-thickening of a set `s` all of whose points have norm at most
`T`, then `Re z ≤ T + r`.  (Only used with `s ⊆ d.Dφ`, but the statement needs no such hypothesis.)

The closed thickening is defined by `infEDist`, so the proof compares `infEDist z s` with
`ENNReal.ofReal (z.re - T)` and uses `Metric.le_infEDist`. -/
theorem re_le_of_mem_cthickening {s : Set ℂ} {r T : ℝ} {z : ℂ} (hr : 0 ≤ r)
    (hz : z ∈ Metric.cthickening r s) (hT : ∀ w ∈ s, ‖w‖ ≤ T) : z.re ≤ T + r := by
  have hinf : Metric.infEDist z s ≤ ENNReal.ofReal r := hz
  have hle : ENNReal.ofReal (z.re - T) ≤ Metric.infEDist z s := by
    rw [Metric.le_infEDist]
    intro w hw
    rw [edist_dist, dist_eq_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : w.re ≤ T := le_trans (Complex.re_le_norm w) (hT w hw)
    calc z.re - T ≤ z.re - w.re := by linarith
      _ = (z - w).re := by simp
      _ ≤ ‖z - w‖ := Complex.re_le_norm _
  have h3 : z.re - T ≤ r :=
    (ENNReal.ofReal_le_ofReal_iff hr).mp (le_trans hle hinf)
  linarith

/-- If `z` lies in the closed `r`-thickening of a set `s` all of whose points have norm at most
`T`, then `|Im z| ≤ T + r`. -/
theorem im_le_of_mem_cthickening {s : Set ℂ} {r T : ℝ} {z : ℂ} (hr : 0 ≤ r)
    (hz : z ∈ Metric.cthickening r s) (hT : ∀ w ∈ s, ‖w‖ ≤ T) : |z.im| ≤ T + r := by
  have hinf : Metric.infEDist z s ≤ ENNReal.ofReal r := hz
  have hle : ENNReal.ofReal (|z.im| - T) ≤ Metric.infEDist z s := by
    rw [Metric.le_infEDist]
    intro w hw
    rw [edist_dist, dist_eq_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : |w.im| ≤ T := le_trans (Complex.abs_im_le_norm w) (hT w hw)
    calc |z.im| - T ≤ |z.im| - |w.im| := by linarith
      _ ≤ |z.im - w.im| := abs_sub_abs_le_abs_sub _ _
      _ = |(z - w).im| := by simp
      _ ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  have h3 : |z.im| - T ≤ r :=
    (ENNReal.ofReal_le_ofReal_iff hr).mp (le_trans hle hinf)
  linarith

theorem deriv_phi_le_of_deep_or_shallow {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) {K' : Set ℂ} {ρe R Tb C Cd : ℝ} {m : ℕ} {z z₀ : ℂ}
    (hρe : 0 ≤ ρe) (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hdeep : ∀ u : ℂ, u ∈ d.Dφ → R ≤ -u.re → |u.im| ≤ Tb + ρe → ‖deriv d.φ u‖ ≤ C)
    (hshallow : ∀ u ∈ (⋃ k ∈ Finset.range (⌈R + Tb + ρe⌉₊ + 1),
        (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K')), ‖deriv d.φ u‖ ≤ Cd)
    (hz₀ : z₀ ∈ Metric.cthickening ρe K') (hz : z = z₀ - (m : ℂ)) (hzD : z ∈ d.Dφ) :
    ‖deriv d.φ z‖ ≤ max C Cd := by
  -- `z = z₀ - m` with `z₀` in the closed `ρe`-thickening of `K'`: the imaginary part of `z`
  -- is that of `z₀`, and both coordinates of `z₀` are bounded by `Tb + ρe`.
  have hz0re : z₀.re ≤ Tb + ρe := re_le_of_mem_cthickening hρe hz₀ hTb
  have hz0im : |z₀.im| ≤ Tb + ρe := im_le_of_mem_cthickening hρe hz₀ hTb
  have hzim : z.im = z₀.im := by rw [hz]; simp
  have hzre : z.re = z₀.re - (m : ℝ) := by rw [hz]; simp
  rcases le_or_gt m ⌈R + Tb + ρe⌉₊ with hm | hm
  · -- shallow: `m ≤ N`, so `z = z₀ - m` is one of the listed translates of `cthickening ρe K'`.
    have hmem : z ∈ ⋃ k ∈ Finset.range (⌈R + Tb + ρe⌉₊ + 1),
        (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K') := by
      refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
      · exact ⟨z₀, hz₀, by rw [hz]⟩
    exact le_trans (hshallow z hmem) (le_max_right _ _)
  · -- deep: `m > N ≥ R + Tb + ρe`, so `Re z = Re z₀ - m ≤ -R - 1 < -R`.
    have hR : R ≤ -z.re := by
      have h1 : R + Tb + ρe ≤ ((⌈R + Tb + ρe⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈R + Tb + ρe⌉₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hm
      rw [hzre]; linarith
    have hzim' : |z.im| ≤ Tb + ρe := by rw [hzim]; exact hz0im
    exact le_trans (hdeep z hzD hR hzim') (le_max_left _ _)

end Work.Pert.Ksub2
