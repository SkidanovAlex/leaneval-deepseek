import Mathlib
import Submission.Work.F0Facts.Basic
import Submission.Work.F0Facts.Petal
import Submission.Work.F0Facts.RealOrbit
import Submission.Work.F0Facts.Connectivity
import Submission.Work.F0Facts.Orbit

/-!
# `f₀(z) = z + z²` belongs to Shishikura's class `𝓕₀`

The parabolic basin `Basin = ParabolicBasin f0 univ` is open, connected, invariant, proper, and
contains the unique critical point `-1/2`; so it is an immediate parabolic basin of `0` and
`f₀ ∈ 𝓕₀`.
-/

namespace Work.F0Facts

open MandelDim Filter Set Metric Topology
open scoped Topology

noncomputable section

lemma neg_half_mem_Basin : (-1/2 : ℂ) ∈ Basin := by
  simpa using ofReal_mem_Basin (t := -1/2) (by norm_num) (by norm_num)

theorem isImmediateBasin_Basin : IsImmediateBasin f0 univ Basin := by
  refine ⟨isOpen_Basin, isConnected_Basin, fun z hz => hz, ?_, ?_, ?_, ?_⟩
  · intro D _ hDB _
    exact hDB
  · intro z hz
    exact f0_mem_Basin hz
  · intro z hz
    obtain ⟨w, hw⟩ := f0_surjective z
    exact ⟨w, mem_Basin_of_f0_mem (by rw [hw]; exact hz), hw⟩
  · intro L hL hLc
    have hclosed : IsClosed (Basin ∩ f0 ⁻¹' L) := by
      rw [← closure_subset_iff_isClosed]
      intro x hx
      have hxL : f0 x ∈ L := by
        have hmap : MapsTo f0 (Basin ∩ f0 ⁻¹' L) L := fun y hy => hy.2
        have h1 : f0 x ∈ closure L := map_mem_closure continuous_f0 hx hmap
        rwa [hLc.isClosed.closure_eq] at h1
      exact ⟨mem_Basin_of_f0_mem (hL hxL), hxL⟩
    have hbdd : Bornology.IsBounded (Basin ∩ f0 ⁻¹' L) := by
      obtain ⟨R, hR⟩ := hLc.isBounded.exists_norm_le
      refine Bornology.IsBounded.subset
        (Metric.isBounded_ball (x := (0 : ℂ)) (r := |R| + 2)) ?_
      rintro z ⟨hzB, hzL⟩
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖f0 z‖ ≤ R := hR (f0 z) hzL
      have h5 : ‖z‖ ^ 2 - ‖z‖ ≤ ‖f0 z‖ := by
        have h6 : ‖z ^ 2‖ ≤ ‖f0 z‖ + ‖z‖ := by
          have h7 := norm_sub_le (f0 z) z
          rw [show f0 z - z = z ^ 2 from by rw [f0_eq]; ring] at h7
          linarith
        rw [norm_pow] at h6
        linarith
      have habs : ‖z‖ ^ 2 - ‖z‖ ≤ |R| := le_trans h5 (le_trans h1 (le_abs_self R))
      by_contra hlt
      push_neg at hlt
      nlinarith [norm_nonneg z, abs_nonneg R, habs]
    exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

theorem inF0_f0 : InF0 f0 univ := by
  refine ⟨isParabolicGerm_f0, Basin, isImmediateBasin_Basin, ?_⟩
  refine ⟨-1/2, ⟨neg_half_mem_Basin, ?_⟩, ?_⟩
  · rw [deriv_f0]; norm_num
  · intro c hc
    have h : 1 + 2 * c = 0 := by
      have h2 := hc.2
      rw [deriv_f0] at h2
      exact h2
    linear_combination (1/2) * h

end
end Work.F0Facts
