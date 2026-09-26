import Mathlib
import Submission.Work.Drive.oFatDefsS
import Submission.Work.Drive.ofatObstructionS_edges
import Submission.Work.Drive.closure_liftedTrisecant_eq_or_tangent

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

open Filter
open scoped Topology

set_option maxHeartbeats 1600000

/-- **The closure of `ShortMid`.**  For a knot `r` without inflections, a limit point of
`Work.Drive.ShortMid r δs` is either still in `ShortMid r δs`, or its chord is tangent at one of its
endpoints (`Work.Drive.TCset r`).

As `q n → q` the middles `u n ∈ [q n.1, q n.1 + q n.2]` have a convergent subsequence
`u n → u ∈ [q.1, q.1 + q.2]` with `r u ∈ segment ℝ (r q.1) (r (q.1 + q.2))` (the closure of
`openSegment` is the segment).  If `u` is strictly between `q.1` and `q.1 + q.2` then
`q ∈ ShortMid` (all its defining conditions are closed, and `q.2 > 0` and `q.2 < period` hold because
a `ShortMid` point carries a middle, hence lies in `liftedTrisecant`, so
`Work.Drive.shortSecantsFree_of_noInflection` bounds `q.2` away from `0` and `period`).  If `u` hits
an endpoint, say `u = q.1`, then `r (u n) - r (q n.1)` is a positive multiple of the chord direction
for every `n`, and `(r (u n) - r (q n.1)) / (u n - q n.1) → velocity r q.1` shows that
`velocity r q.1` is parallel to `r (q.1 + q.2) - r q.1`, i.e. `q ∈ TCset`.  (The already-proved
`Work.Drive.cross_zero_of_tendsto_middle_endpoint_a`/`_b` cover the endpoint case.) -/
theorem shortMidClosure {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (δs : ℝ) :
    closure (Work.Drive.ShortMid r δs) ⊆ Work.Drive.ShortMid r δs ∪ Work.Drive.TCset r := by
  -- the band away from the two edges of the strip
  obtain ⟨δ, hδpos, hδ⟩ := shortSecantsFree_of_noInflection hr hinfl
  have hband : ∀ q ∈ closure (ShortMid r δs), δ ≤ q.2 ∧ q.2 ≤ period - δ :=
    closure_subset_band (fun q hq => hδ q (shortMid_subset_liftedTrisecant hr δs hq))
  intro z hz
  obtain ⟨hzlo, hzhi⟩ := hband z hz
  have hz0 : 0 < z.2 := lt_of_lt_of_le hδpos hzlo
  have hz1 : z.2 < period := by linarith
  -- a sequence in `ShortMid` converging to `z`
  have hex : ∀ n : ℕ, ∃ y ∈ ShortMid r δs, dist z y < 1 / ((n : ℝ) + 1) := fun n =>
    Metric.mem_closure_iff.mp hz _ (by positivity)
  let w : ℕ → ℝ × ℝ := fun n => Classical.choose (hex n)
  have hwmem : ∀ n, w n ∈ ShortMid r δs := fun n => (Classical.choose_spec (hex n)).1
  have hwd : ∀ n, dist (w n) z < 1 / ((n : ℝ) + 1) := fun n => by
    rw [dist_comm]; exact (Classical.choose_spec (hex n)).2
  have hwlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hwt : Tendsto w atTop (𝓝 z) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hwlim
      (fun n => dist_nonneg) (fun n => le_of_lt (hwd n))
  -- the middles of the chords, on the retained arc
  have hmiddle : ∀ n, ∃ u : ℝ, (w n).1 ≤ u ∧ u ≤ (w n).1 + (w n).2 ∧
      r u ∈ openSegment ℝ (r (w n).1) (r ((w n).1 + (w n).2)) :=
    fun n => (mem_ShortMid_iff.mp (hwmem n)).2.2.2
  let v : ℕ → ℝ := fun n => Classical.choose (hmiddle n)
  have hv1 : ∀ n, (w n).1 ≤ v n := fun n => (Classical.choose_spec (hmiddle n)).1
  have hv2 : ∀ n, v n ≤ (w n).1 + (w n).2 := fun n => (Classical.choose_spec (hmiddle n)).2.1
  have hv3 : ∀ n, r (v n) ∈ openSegment ℝ (r (w n).1) (r ((w n).1 + (w n).2)) :=
    fun n => (Classical.choose_spec (hmiddle n)).2.2
  -- the middles are bounded, so a subsequence converges
  have hcomp : ∀ n, |(w n).1 - z.1| < 1 ∧ |(w n).2 - z.2| < 1 := by
    intro n
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      have h : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h
      simpa using this
    have hd := lt_of_lt_of_le (hwd n) hle
    have h1 : dist (w n).1 z.1 ≤ dist (w n) z := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have h2' : dist (w n).2 z.2 ≤ dist (w n) z := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    exact ⟨by rw [← Real.dist_eq]; exact lt_of_le_of_lt h1 hd,
           by rw [← Real.dist_eq]; exact lt_of_le_of_lt h2' hd⟩
  have hvbd : ∀ n, v n ∈ Set.Icc (z.1 - 1) (z.1 + period + 2) := by
    intro n
    obtain ⟨hb1, hb2⟩ := hcomp n
    obtain ⟨e1, e2⟩ := abs_lt.mp hb1
    obtain ⟨e3, e4⟩ := abs_lt.mp hb2
    have h1 := hv1 n
    have h2 := hv2 n
    constructor <;> linarith
  obtain ⟨u, huIcc, φ, hφmono, hvφ⟩ := isCompact_Icc.tendsto_subseq (x := v) hvbd
  -- limits of the two chord endpoints
  have hwφ : Tendsto (fun k => w (φ k)) atTop (𝓝 z) := hwt.comp hφmono.tendsto_atTop
  have hwa : Tendsto (fun k => (w (φ k)).1) atTop (𝓝 z.1) :=
    (continuous_fst.tendsto z).comp hwφ
  have hwb : Tendsto (fun k => (w (φ k)).1 + (w (φ k)).2) atTop (𝓝 (z.1 + z.2)) :=
    hwa.add ((continuous_snd.tendsto z).comp hwφ)
  have hu_lo : z.1 ≤ u := le_of_tendsto_of_tendsto' hwa hvφ (fun k => hv1 (φ k))
  have hu_hi : u ≤ z.1 + z.2 := le_of_tendsto_of_tendsto' hvφ hwb (fun k => hv2 (φ k))
  -- the "short" alternative is closed
  have hSclosed : IsClosed {y : ℝ | y ≤ δs ∨ period - y ≤ δs} :=
    (isClosed_le continuous_id continuous_const).union
      (isClosed_le (continuous_const.sub continuous_id) continuous_const)
  have hSr : Tendsto (fun k => (w (φ k)).2) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hwφ
  have hδs_mem : z.2 ∈ {y : ℝ | y ≤ δs ∨ period - y ≤ δs} :=
    IsClosed.mem_of_tendsto hSclosed hSr
      (Eventually.of_forall (fun k => (mem_ShortMid_iff.mp (hwmem (φ k))).2.2.1))
  have hδs_or : z.2 ≤ δs ∨ period - z.2 ≤ δs := hδs_mem
  have hAne : r z.1 ≠ r (z.1 + z.2) := by
    intro hk
    have hkeq : knotMap r ((z.1 : ℝ) : KnotParam) = knotMap r (((z.1 + z.2 : ℝ)) : KnotParam) := by
      rw [knotMap_eq_r hr, knotMap_eq_r hr]
      exact hk
    exact coe_ne_coe_of_lt hz0 hz1 (knotMap_injective hr hkeq)
  -- the circle-level middle data
  have hcoe : Continuous (fun x : ℝ => (x : KnotParam)) := QuotientAddGroup.continuous_mk
  let A : ℕ → KnotParam := fun k => ((w (φ k)).1 : KnotParam)
  let B : ℕ → KnotParam := fun k => (((w (φ k)).1 + (w (φ k)).2 : ℝ) : KnotParam)
  let M : ℕ → KnotParam := fun k => ((v (φ k) : ℝ) : KnotParam)
  have haT : Tendsto A atTop (𝓝 ((z.1 : ℝ) : KnotParam)) := (hcoe.tendsto z.1).comp hwa
  have hbT : Tendsto B atTop (𝓝 (((z.1 + z.2 : ℝ)) : KnotParam)) :=
    (hcoe.tendsto (z.1 + z.2)).comp hwb
  have hstr : ∀ k, IsMiddleOnChord r (A k) (B k) (M k) :=
    fun k => (IsMiddleOnChord_iff_real hr ((w (φ k)).1) ((w (φ k)).1 + (w (φ k)).2)
      (v (φ k))).mpr (hv3 (φ k))
  rcases eq_or_ne u z.1 with hua | hua
  · -- the limit middle is the first endpoint: the chord is tangent there
    right
    refine mem_TCset_iff.mpr ⟨hz0, hz1, Or.inl ?_⟩
    have hmT : Tendsto M atTop (𝓝 ((z.1 : ℝ) : KnotParam)) :=
      (hcoe.tendsto z.1).comp (hua ▸ hvφ)
    exact cross_zero_of_tendsto_middle_endpoint_a hr hAne haT hbT hmT (Eventually.of_forall hstr)
  · rcases eq_or_ne u (z.1 + z.2) with hub | hub
    · -- the limit middle is the second endpoint: the chord is tangent there
      right
      refine mem_TCset_iff.mpr ⟨hz0, hz1, Or.inr ?_⟩
      have hmT : Tendsto M atTop (𝓝 (((z.1 + z.2 : ℝ)) : KnotParam)) :=
        (hcoe.tendsto (z.1 + z.2)).comp (hub ▸ hvφ)
      exact cross_zero_of_tendsto_middle_endpoint_b hr hAne haT hbT hmT (Eventually.of_forall hstr)
    · -- the limit middle is strictly inside: `z` is still in `ShortMid`
      left
      refine mem_ShortMid_iff.mpr ⟨hz0, hz1, hδs_or, u, hu_lo, hu_hi, ?_⟩
      have hmT : Tendsto M atTop (𝓝 ((u : ℝ) : KnotParam)) := (hcoe.tendsto u).comp hvφ
      have hpT : Tendsto (fun k => (A k, B k, M k)) atTop
          (𝓝 (((z.1 : ℝ) : KnotParam), (((z.1 + z.2 : ℝ)) : KnotParam),
            ((u : ℝ) : KnotParam))) :=
        Tendsto.prodMk_nhds haT (Tendsto.prodMk_nhds hbT hmT)
      have hp_mem : ∀ k, (A k, B k, M k) ∈ closedMiddleData r :=
        fun k => openMiddleData_subset_closedMiddleData r (hstr k)
      have hlimpt : (((z.1 : ℝ) : KnotParam), (((z.1 + z.2 : ℝ)) : KnotParam),
            ((u : ℝ) : KnotParam)) ∈ closedMiddleData r :=
        IsClosed.mem_of_tendsto (isClosed_closedMiddleData hr) hpT (Eventually.of_forall hp_mem)
      have hcl : IsMiddleOnClosedChord r ((z.1 : ℝ) : KnotParam)
          (((z.1 + z.2 : ℝ)) : KnotParam) ((u : ℝ) : KnotParam) :=
        (mem_closedMiddleData_iff r).mp hlimpt
      have hseg : r u ∈ segment ℝ (r z.1) (r (z.1 + z.2)) := by
        rw [IsMiddleOnClosedChord] at hcl
        rw [knotMap_eq_r hr u, knotMap_eq_r hr z.1, knotMap_eq_r hr (z.1 + z.2)] at hcl
        exact hcl
      have hneA : r u ≠ r z.1 := by
        intro hru
        have hk : knotMap r ((u : ℝ) : KnotParam) = knotMap r ((z.1 : ℝ) : KnotParam) := by
          rw [knotMap_eq_r hr u, knotMap_eq_r hr z.1]; exact hru
        have heq : ((u : ℝ) : KnotParam) = ((z.1 : ℝ) : KnotParam) := knotMap_injective hr hk
        have hpos : 0 < u - z.1 := by
          have := lt_of_le_of_ne hu_lo (Ne.symm hua); linarith
        have hlt : u - z.1 < period := by linarith
        have hne := coe_ne_coe_of_lt (x := z.1) (y := u - z.1) hpos hlt
        rw [show z.1 + (u - z.1) = u by ring] at hne
        exact hne heq.symm
      have hneB : r u ≠ r (z.1 + z.2) := by
        intro hru
        have hk : knotMap r ((u : ℝ) : KnotParam) = knotMap r (((z.1 + z.2 : ℝ)) : KnotParam) := by
          rw [knotMap_eq_r hr u, knotMap_eq_r hr (z.1 + z.2)]; exact hru
        have heq : ((u : ℝ) : KnotParam) = (((z.1 + z.2 : ℝ)) : KnotParam) := knotMap_injective hr hk
        have hlt : u < z.1 + z.2 := lt_of_le_of_ne hu_hi hub
        have hpos : 0 < (z.1 + z.2) - u := by linarith
        have hlt2 : (z.1 + z.2) - u < period := by linarith
        have hne := coe_ne_coe_of_lt (x := u) (y := (z.1 + z.2) - u) hpos hlt2
        rw [show u + ((z.1 + z.2) - u) = z.1 + z.2 by ring] at hne
        exact hne heq
      exact segment_mem_openSegment_of_ne hseg hneA hneB

end Work.Drive
