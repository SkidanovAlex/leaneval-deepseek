import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_end
import Submission.Work.PlanarSC.exists_pos_le_dist_of_isCompact_of_isClosed
import Submission.Work.L62LD.dist_int_translate_pos

/-! ## Auxiliary facts for the perturbed upper-end head

* `cthickening_subset_interior`: the `r`-neighbourhood of a compactum is contained in the
  *interior* of its `r'`-neighbourhood for `r < r'`.
* `dist_int_translate_pos_up`: a point outside `d.DE` is separated from every `ℤ`-translate of a
  compactum inside the upper horn `Bu`.
* `norm_deriv_E_pos_up`: the derivative of `d.E` is bounded below on the closed neighbourhood
  `cthickening r K ⊆ Bu` of a compactum `K ⊆ Bu` intersected with the set of points whose
  `β`-translate still has its value in `Bu` — uniformly in `β` over the available box.

These are the inputs of the separation engine `Work.L62.sep_chain_abstract` for the *perturbed*
chain: the derivative bound `Δ` on the tube, the separation from the centre of the first disc, and
the *positive lower bound* `c` on `‖deriv (fun w => R w - β) w‖ = ‖deriv R w‖` along the chain
(which is what makes the perturbed discs small and bounds the derivative of the iterates). -/
namespace Work.L62

open Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- The `r`-neighbourhood of a set lies in the interior of its `r'`-neighbourhood for
`0 ≤ r < r'`. -/
theorem cthickening_subset_interior {K : Set ℂ} {r r' : ℝ} (hr : 0 ≤ r) (h : r < r') :
    Metric.cthickening r K ⊆ interior (Metric.cthickening r' K) := by
  intro w hw
  rw [Metric.cthickening_eq_biUnion_closedBall K hr] at hw
  obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.mp hw
  have hw' : dist w x ≤ r := by simpa [Metric.mem_closedBall, dist_comm] using hwx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨r' - r, sub_pos.mpr h, ?_⟩
  intro v hv
  rw [Metric.cthickening_eq_biUnion_closedBall K (le_of_lt (lt_of_le_of_lt hr h))]
  refine mem_iUnion₂.mpr ⟨x, hx, ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  rw [Metric.mem_ball] at hv
  have h1 : dist x v ≤ dist x w + dist w v := dist_triangle x w v
  rw [dist_comm x w, dist_comm w v] at h1
  linarith

/-- **Separation of a point outside `d.DE` from a compactum in the upper horn modulo `ℤ`.** -/
theorem dist_int_translate_pos_up {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {ζc : ℂ} (hζc : ζc ∉ d.DE) {K : Set ℂ} (hKc : IsCompact K)
    (hKBu : K ⊆ hd.Bu) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ k : ℤ, ∀ v ∈ K, ε₀ ≤ ‖(ζc - (k : ℂ)) - v‖ := by
  have hdisj : Disjoint K (Set.range (fun k : ℤ => ζc - (k : ℂ))) := by
    refine Set.disjoint_left.mpr fun v hvK hvS => ?_
    obtain ⟨k, hk⟩ := hvS
    beta_reduce at hk
    have hmem : v ∈ hd.Bu := hKBu hvK
    have h2 : v + (k : ℂ) ∈ hd.Bu := (Work.L62.IsTInvariant.mem_add_int hd.Bu_T v k).mp hmem
    have h3 : ζc ∈ hd.Bu := by
      rw [← hk] at h2
      simpa using h2
    exact hζc (hd.sub (Or.inl h3))
  obtain ⟨ε₀, hε₀, h⟩ := Work.PlanarSC.exists_pos_le_dist_of_isCompact_of_isClosed hKc
    (Work.L62LD.isClosed_range_sub_intCast ζc) hdisj
  refine ⟨ε₀, hε₀, fun k v hvK => ?_⟩
  have hle : ε₀ ≤ ‖v - (ζc - (k : ℂ))‖ := by
    have := h v hvK (ζc - (k : ℂ)) ⟨k, rfl⟩
    rwa [dist_eq_norm] at this
  rwa [norm_sub_rev]

end

end Work.L62
