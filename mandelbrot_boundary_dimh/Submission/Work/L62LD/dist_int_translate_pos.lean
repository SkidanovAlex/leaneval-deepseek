import Mathlib
import Submission.Work.L62LD.setup

/-!
# L62LD — the translate class `ζc - ℤ` keeps a positive distance from `K ⊆ hd.Bl`

The lower-end head of Lemma 6.2 chooses a centre `ζc ∉ d.DE` (one of the two inverse orbits of
Lemma 6.1) and works with the backward chain of discs built from it.  Since the discs of positive
index are *lifts* of points in the pulled-back cylinder, the chain marches along the translate
class `ζc - ℤ`; to make the "disjoint discs" clause of Lemma 6.2 quantitative one needs that this
whole translate class stays a positive distance away from the fixed compact `K ⊆ hd.Bl` that
confines the chain (`Work.L62LD.dist_int_translate_pos_chk`).

The mechanism is:

* `hd.Bl` is `T`-invariant (`IsTInvariant`) and contained in `d.DE`, so from `ζc ∉ d.DE` we get
  `ζc - k ∉ hd.Bl` for every `k : ℤ`, hence `{ζc - k} ∩ K = ∅`;
* `Set.range (fun k : ℤ => ζc - (k : ℂ))` is closed (image of the closed embedding
  `Int.cast : ℤ → ℂ` under the continuous map `w ↦ ζc - w`);
* the general metric fact `Work.L62LD.exists_pos_dist_of_isCompact_isClosed`: a compact set and a
  disjoint closed set have positive distance.
-/

namespace Work.L62LD

open Classical MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Two elementary lemmas -/

/-- A compact set and a disjoint closed set in a metric space have positive distance,
in the uniform form `ε ≤ dist v s` for `v ∈ K`, `s ∈ S`. -/
theorem exists_pos_dist_of_isCompact_isClosed {α : Type*} [MetricSpace α] {K S : Set α}
    (hK : IsCompact K) (hS : IsClosed S) (hdisj : Disjoint K S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ K, ∀ s ∈ S, ε ≤ dist v s := by
  rcases K.eq_empty_or_nonempty with hKemp | hKne
  · exact ⟨1, one_pos, fun v hv => by simp [hKemp] at hv⟩
  rcases S.eq_empty_or_nonempty with hSemp | hSne
  · exact ⟨1, one_pos, fun v hv s hs => by simp [hSemp] at hs⟩
  obtain ⟨v₀, hv₀K, hmin⟩ :=
    hK.exists_isMinOn hKne (Metric.continuous_infDist_pt S).continuousOn
  have hv₀S : v₀ ∉ S := fun h => (Set.disjoint_left.mp hdisj) hv₀K h
  have hpos : 0 < Metric.infDist v₀ S := (hS.notMem_iff_infDist_pos hSne).mp hv₀S
  refine ⟨Metric.infDist v₀ S, hpos, fun v hvK s hs => ?_⟩
  have h1 : Metric.infDist v₀ S ≤ Metric.infDist v S := hmin hvK
  have h2 : Metric.infDist v S ≤ dist v s := Metric.infDist_le_dist_of_mem hs
  linarith

/-- The translate class `ζc - ℤ` is closed in `ℂ`. -/
theorem isClosed_range_sub_intCast (ζc : ℂ) :
    IsClosed (Set.range (fun k : ℤ => ζc - (k : ℂ))) := by
  have h : Set.range (fun k : ℤ => ζc - (k : ℂ))
      = (fun w : ℂ => ζc - w) ⁻¹' (Set.range (Int.cast : ℤ → ℂ)) := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ring⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      show ζc - (k : ℂ) = w
      rw [hk]; ring
  rw [h]
  exact Complex.isClosedEmbedding_intCast.isClosed_range.preimage
    (continuous_const.sub continuous_id)

/-! ## The target -/

theorem dist_int_translate_pos {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {ζc : ℂ} (hζc : ζc ∉ d.DE) {K : Set ℂ} (hKc : IsCompact K)
    (hKBl : K ⊆ hd.Bl) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ k : ℤ, ∀ v ∈ K, ε₀ ≤ ‖(ζc - (k : ℂ)) - v‖ := by
  -- the translate class misses the compact set
  have hdisj : Disjoint K (Set.range (fun k : ℤ => ζc - (k : ℂ))) := by
    refine Set.disjoint_left.mpr fun v hvK hvS => ?_
    obtain ⟨k, hk⟩ := hvS
    beta_reduce at hk
    have hmem : v ∈ hd.Bl := hKBl hvK
    have h2 : v + (k : ℂ) ∈ hd.Bl := (Work.L62.IsTInvariant.mem_add_int hd.Bl_T v k).mp hmem
    have h3 : ζc ∈ hd.Bl := by
      rw [← hk] at h2
      simpa using h2
    exact hζc (hd.sub (Or.inr h3))
  obtain ⟨ε₀, hε₀, h⟩ := exists_pos_dist_of_isCompact_isClosed hKc
    (isClosed_range_sub_intCast ζc) hdisj
  refine ⟨ε₀, hε₀, fun k v hvK => ?_⟩
  have hle : ε₀ ≤ ‖v - (ζc - (k : ℂ))‖ := by
    have := h v hvK (ζc - (k : ℂ)) ⟨k, rfl⟩
    rwa [dist_eq_norm] at this
  simpa only [norm_sub_rev] using hle

end
end Work.L62LD
