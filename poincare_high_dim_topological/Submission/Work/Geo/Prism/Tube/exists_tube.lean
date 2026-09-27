import Mathlib
import Submission.Work.Geo.Prism.Defs
import Submission.Work.PL.Defs

/-!
# The tube lemma for the prism construction

If a compact `K` has `{0} × K` inside an open `U ⊆ E a × X`, then `{0} × K` can be
thickened simultaneously in the `E a` direction and around `K`.  This is the only
topological input of `prism_push` besides the explicit formulae.
-/

open Set Metric
open scoped Topology

namespace Work.Geo.Prism.Tube

/-- Tube result for the prism construction: if a compact `K` in `X` has `{0} × K` inside an
open `U ⊆ E a × X`, then `{0} × K` can be thickened simultaneously in the `E a` direction
and around `K`.  The conclusion is stated in "proximity to a point of `K`" form so that it
is also correct for `K = ∅`. -/
theorem exists_tube {a : ℕ} {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K)
    {U : Set (PL.E a × X)} (hU : IsOpen U) (h : ({0} : Set (PL.E a)) ×ˢ K ⊆ U) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧
      {p : PL.E a × X | ‖p.1‖ ≤ η ∧ ∃ q ∈ K, dist p.2 q ≤ ρ} ⊆ U := by
  have hc : IsCompact (({0} : Set (PL.E a)) ×ˢ K) := isCompact_singleton.prod hK
  obtain ⟨ε, hε, hsub⟩ := hc.exists_cthickening_subset_open hU h
  refine ⟨ε / 2, ε / 2, by linarith, by linarith, ?_⟩
  rintro ⟨y, x⟩ ⟨hy, q, hq, hxq⟩
  have hy' : ‖y‖ ≤ ε / 2 := hy
  have hxq' : dist x q ≤ ε / 2 := hxq
  refine hsub ?_
  rw [mem_cthickening_iff]
  have hmem : ((0 : PL.E a), q) ∈ ({0} : Set (PL.E a)) ×ˢ K := ⟨by simp, hq⟩
  have h1 : Metric.infEDist (y, x) (({0} : Set (PL.E a)) ×ˢ K)
      ≤ edist (y, x) ((0 : PL.E a), q) := Metric.infEDist_le_edist_of_mem hmem
  refine le_trans h1 ?_
  rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by linarith : (0 : ℝ) ≤ ε), Prod.dist_eq]
  refine max_le ?_ ?_
  · rw [dist_zero_right]; linarith
  · linarith

end Work.Geo.Prism.Tube
