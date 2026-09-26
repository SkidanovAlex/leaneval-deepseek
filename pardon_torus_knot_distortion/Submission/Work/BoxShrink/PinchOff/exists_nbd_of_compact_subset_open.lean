import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Defs

namespace Work.BoxShrink.PinchOff

/-- **A lattice-periodic neighbourhood of the translates of a compact set inside an open set.**

Let `Y ⊆ ℂ` be open and invariant under the period lattice, let `K ⊆ ℂ` be compact, non-empty and
contained in `Y`.  Then the union `⋃ ν ∈ periodLattice, {z | z - ν ∈ K}` of the translates of `K`
has a uniform neighbourhood contained in `Y`: there is `r > 0` such that every point at distance
`< r` from that union lies in `Y`.

(The union lies in `Y` by periodicity; the uniformity comes from the compactness of `K`: each point
of `K` has a ball contained in `Y`, finitely many of them cover `K`, and the same radius then works
on every translate.) -/
theorem exists_nbd_of_compact_subset_open
    {Y : Set ℂ} (hYo : IsOpen Y)
    (K : Set ℂ) (hKc : IsCompact K) (hKne : K.Nonempty) (hKY : K ⊆ Y)
    (hYper : ∀ w : ℂ, w ∈ Work.BoxShrink.PinchOff.periodLattice → ∀ z : ℂ, z ∈ Y ↔ z + w ∈ Y) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ,
      Metric.infDist z (⋃ ν ∈ Work.BoxShrink.PinchOff.periodLattice,
        {z' : ℂ | z' - ν ∈ K}) < r → z ∈ Y := by
  -- A uniform thickening radius for the compact `K` inside the open `Y`.
  obtain ⟨r, hrpos, hr⟩ := hKc.exists_thickening_subset_open hYo hKY
  refine ⟨r, hrpos, ?_⟩
  intro z hz
  -- The union of translates is non-empty (it contains `K` itself, at the lattice element `0`).
  have h0Λ : (0 : ℂ) ∈ periodLattice := ⟨(0, 0), periodPt_zero⟩
  have hne : (⋃ ν ∈ periodLattice, {z' : ℂ | z' - ν ∈ K}).Nonempty := by
    obtain ⟨k, hk⟩ := hKne
    refine ⟨k, ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨0, h0Λ, by simpa using hk⟩
  -- A close point `p` of the union: `p - ν ∈ K`.
  obtain ⟨p, hpU, hpd⟩ := (Metric.infDist_lt_iff hne).1 hz
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hpU
  obtain ⟨ν, hν, hpK⟩ := hpU
  -- Translating back by `ν`, the point `z - ν` lies in the thickening of `K`.
  have hmem : z - ν ∈ Metric.thickening r K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨p - ν, hpK, ?_⟩
    have hdist : dist (z - ν) (p - ν) = dist z p := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      ring
    rw [hdist]
    exact hpd
  have hzνY : z - ν ∈ Y := hr hmem
  -- Periodicity converts `z - ν ∈ Y` into `z ∈ Y`.
  have h := (hYper ν hν (z - ν)).1 hzνY
  simpa using h

end Work.BoxShrink.PinchOff
