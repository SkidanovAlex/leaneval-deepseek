import Mathlib
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.Rl4Aux

namespace Work.GM.S3

open scoped Topology

/-- `ψ₂` vanishes below `1/C₀` when its support is `⊆ [1/C₀, C₀]`. -/
theorem IsBumpAtOne.eq_zero_of_lt_inv {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtOne ψ C) {v : ℝ}
    (hv : v < 1 / C) : ψ v = 0 := by
  by_contra hne
  exact absurd (Set.mem_Icc.mp (h.2.2.1 v hne)).1 (not_le.mpr hv)

/-- **Continuity of `u ↦ ψ₂ u * ‖Rfun W u‖²`.** `ψ₂` is continuous; `Rfun W v = Σ_{t∈W} |v|^{it}`
is continuous at every `v ≠ 0`; and near `u = 0` the product is `0` because `ψ₂` vanishes on a
neighbourhood of `0` (`IsBumpAtOne ψ₂ C₀` with `C₀ ≥ 1` gives `ψ₂ x ≠ 0 → x ∈ Icc (1/C₀) C₀`, so
`ψ₂ = 0` on `(-1/C₀, 1/C₀)`). -/
theorem gSq_continuous (ψ₂ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (h₂ : IsBumpAtOne ψ₂ C₀)
    (W : Finset ℝ) :
    Continuous (fun u : ℝ => ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2) := by
  have hCpos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hcpos : 0 < 1 / C₀ := one_div_pos.mpr hCpos
  have hψcont : Continuous ψ₂ := h₂.1.continuous
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_or_ge u (1 / C₀) with hlt | hge
  · -- `u < 1/C₀`: the function is `0` on the open neighbourhood `(-∞, 1/C₀)` of `u`
    have hmem : Set.Iio (1 / C₀) ∈ 𝓝 u := IsOpen.mem_nhds isOpen_Iio hlt
    have hEv : (fun u : ℝ => ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2) =ᶠ[𝓝 u] (fun _ => 0) := by
      filter_upwards [hmem] with v hv
      rw [h₂.eq_zero_of_lt_inv hv, zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq hEv
  · -- `u ≥ 1/C₀ > 0`: `Rfun W` is continuous near `u`
    have hupos : 0 < u := lt_of_lt_of_le hcpos hge
    have hR : ContinuousAt (fun v : ℝ => Submission.GM.Rfun W v) u :=
      (Rfun_continuousOn_Ioi W).continuousAt (IsOpen.mem_nhds isOpen_Ioi hupos)
    exact hψcont.continuousAt.mul (hR.norm.pow 2)

end Work.GM.S3
