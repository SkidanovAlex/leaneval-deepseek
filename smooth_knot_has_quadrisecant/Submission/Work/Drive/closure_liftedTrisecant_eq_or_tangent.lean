import Mathlib
import Submission.Work.Drive.noInflectionAPI
import Submission.Work.Drive.shortSecantsFree_of_noInflection
import Submission.EndpointEscape
import Submission.SheetAssembly
import Submission.Work.Drive.middle_locus_basic

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Topology

set_option maxHeartbeats 1600000

noncomputable section

/-!
# The closure of the lifted trisecant locus off the edges

This module proves `Work.Drive.closure_liftedTrisecant_eq_or_tangent`: a point `z` of the
closure of the lifted trisecant locus `liftedTrisecant r ⊆ ℝ × (0, period)`, strictly inside the
strip and not itself a trisecant, must be a *tangent chord* — the chord joining `r z.1` and
`r (z.1 + z.2)` is tangent to the knot at one of its two endpoints.

The three ingredients are

* `exists_middle_of_mem_liftedTrisecant` / `mem_liftedTrisecant_of_middle` — the definitional
  translation between membership in `liftedTrisecant r` and the existence of a strict middle point
  on the chord `{z.1, z.1 + z.2}`;
* `isMiddleOnChord_of_tendsto_middle` — closedness of the strict-middle data: a limit of strict
  middles of chords converging to a chord is a strict middle, unless it is one of the two endpoint
  classes (this is the closedness of `closedMiddleData r`);
* `cross_zero_of_tendsto_middle_endpoint_a` / `_b` — when the middles *do* run to an endpoint class,
  the normalized-limit argument (`middle_to_endpoint_cross_zero`, the quantitative form of the
  endpoint-escape lemma `no_middle_to_endpoint`) forces the chord to be tangent at that endpoint.

Everything is assembled on a convergent sequence in `liftedTrisecant r` and a convergent
subsequence of its middles (compactness of the parameter circle); the three cases are a strict
limit middle (`z` itself is a trisecant), a middle running to the first endpoint (tangency at
`z.1`), or a middle running to the second endpoint (tangency at `z.1 + z.2`).
-/

/-- **Middle extraction from the lifted trisecant locus.**  A point `p` of the lifted trisecant
locus carries a strict middle point `m` on its chord: `r m` lies strictly between `r p.1` and
`r (p.1 + p.2)`. -/
lemma exists_middle_of_mem_liftedTrisecant {r : ℝ → Space} {p : ℝ × ℝ}
    (hp : p ∈ liftedTrisecant r) :
    ∃ m : KnotParam, IsMiddleOnChord r (p.1 : KnotParam) ((p.1 + p.2 : ℝ) : KnotParam) m := by
  rw [mem_liftedTrisecant_iff] at hp
  obtain ⟨h0, h1, hc⟩ := hp
  rw [stripSecantClass_eq_mobiusCover] at hc
  exact (HasMiddleOnClass_iff r (stripPair p h0 h1)).mp hc

/-- **Constructing a trisecant from a middle.**  A strict middle point of the chord joining
`r z.1` and `r (z.1 + z.2)` makes `z` (with `0 < z.2 < period`) a point of the lifted trisecant
locus. -/
lemma mem_liftedTrisecant_of_middle {r : ℝ → Space} {z : ℝ × ℝ} (h0 : 0 < z.2)
    (h1 : z.2 < period)
    (hm : ∃ m : KnotParam, IsMiddleOnChord r (z.1 : KnotParam) ((z.1 + z.2 : ℝ) : KnotParam) m) :
    z ∈ liftedTrisecant r := by
  refine mem_liftedTrisecant_iff.mpr ⟨h0, h1, ?_⟩
  rw [stripSecantClass_eq_mobiusCover]
  exact (HasMiddleOnClass_iff r (stripPair z h0 h1)).mpr (by simpa [stripPair] using hm)

/-- **Closedness of the strict-middle correspondence.**  A limit of strict middle points of chords
which converge to the chord of the real parameters `A₀, B₀` is a strict middle of the limit chord,
provided it is not one of the two endpoint classes.  (The limit is automatically a *closed* middle
— `closedMiddleData r` is closed — and a non-endpoint point of a segment is strictly inside it.) -/
lemma isMiddleOnChord_of_tendsto_middle {r : ℝ → Space} (h : IsSmoothKnot r)
    {A₀ B₀ : ℝ} {a b u : ℕ → KnotParam} {x : KnotParam}
    (ha : Tendsto a atTop (𝓝 (A₀ : KnotParam))) (hb : Tendsto b atTop (𝓝 (B₀ : KnotParam)))
    (hu : Tendsto u atTop (𝓝 x))
    (hstr : ∀ᶠ n in atTop, IsMiddleOnChord r (a n) (b n) (u n))
    (hxA : x ≠ (A₀ : KnotParam)) (hxB : x ≠ (B₀ : KnotParam)) :
    IsMiddleOnChord r (A₀ : KnotParam) (B₀ : KnotParam) x := by
  have hseq : Tendsto (fun n : ℕ => ((a n), ((b n), u n))) atTop
      (𝓝 ((A₀ : KnotParam), ((B₀ : KnotParam), x))) :=
    Filter.Tendsto.prodMk_nhds ha (Filter.Tendsto.prodMk_nhds hb hu)
  have hev : ∀ᶠ n in atTop, ((a n), ((b n), u n)) ∈ closedMiddleData r := by
    filter_upwards [hstr] with n hn
    exact openMiddleData_subset_closedMiddleData r (by
      change IsMiddleOnOpenChord r (a n) (b n) (u n)
      simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using hn)
  have hp : ((A₀ : KnotParam), ((B₀ : KnotParam), x)) ∈ closedMiddleData r :=
    IsClosed.mem_of_tendsto (isClosed_closedMiddleData h) hseq hev
  have hcl : IsMiddleOnClosedChord r (A₀ : KnotParam) (B₀ : KnotParam) x :=
    (mem_closedMiddleData_iff r).mp hp
  exact segment_mem_openSegment_of_ne hcl (fun hk => hxA ((knotMap_injective h) hk))
    (fun hk => hxB ((knotMap_injective h) hk))

/-- **Escape to the first endpoint forces tangency there.**  If the strict middle points of chords
converging to the chord of `A₀, B₀` run to the *first* endpoint class `(A₀ : KnotParam)`, then the
limit chord is tangent to the knot at `A₀`: `cross3 (r B₀ - r A₀) (velocity r A₀) = 0`.

This is `middle_to_endpoint_cross_zero` (the normalized-limit form of the endpoint-escape lemma)
transported from the circle to the line by `exists_real_lift_of_tendsto_circle`. -/
lemma cross_zero_of_tendsto_middle_endpoint_a {r : ℝ → Space} (h : IsSmoothKnot r)
    {A₀ B₀ : ℝ} (hAne : r A₀ ≠ r B₀)
    {a b u : ℕ → KnotParam}
    (ha : Tendsto a atTop (𝓝 (A₀ : KnotParam))) (hb : Tendsto b atTop (𝓝 (B₀ : KnotParam)))
    (hu : Tendsto u atTop (𝓝 (A₀ : KnotParam)))
    (hstr : ∀ᶠ n in atTop, IsMiddleOnChord r (a n) (b n) (u n)) :
    cross3 (r B₀ - r A₀) (velocity r A₀) = 0 := by
  obtain ⟨A, hAt, hAev⟩ :=
    exists_real_lift_of_tendsto_circle (x₀ := (A₀ : KnotParam)) (X₀ := A₀) rfl ha
  obtain ⟨B, hBt, hBev⟩ :=
    exists_real_lift_of_tendsto_circle (x₀ := (B₀ : KnotParam)) (X₀ := B₀) rfl hb
  obtain ⟨M, hMt, hMev⟩ :=
    exists_real_lift_of_tendsto_circle (x₀ := (A₀ : KnotParam)) (X₀ := A₀) rfl hu
  have hstrR : ∀ᶠ n in atTop, r (M n) ∈ openSegment ℝ (r (A n)) (r (B n)) := by
    filter_upwards [hAev, hBev, hMev, hstr] with n hAe hBe hMe hsm
    have hcnv : IsMiddleOnChord r (A n : KnotParam) (B n : KnotParam) (M n : KnotParam) := by
      simpa [← hAe, ← hBe, ← hMe] using hsm
    exact (IsMiddleOnChord_iff_real h (A n) (B n) (M n)).mp hcnv
  have hMneA : ∀ᶠ n in atTop, M n ≠ A n := by
    filter_upwards [hAev, hMev, hstr,
      eventually_chord_endpoints_distinct_circle h hAne ha hb] with n hAe hMe hsm hAnb
    have hmn : u n ≠ a n := (IsMiddleOnChord.ne_params h hAnb hsm).1
    intro hMA
    apply hmn
    calc u n = (M n : KnotParam) := hMe.symm
      _ = (A n : KnotParam) := congrArg (fun z : ℝ => (z : KnotParam)) hMA
      _ = a n := hAe
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hstrR.and hMneA)
  have hd : r B₀ - r A₀ ≠ 0 := sub_ne_zero.mpr hAne.symm
  have ht : ∀ k : ℕ, ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      r (M (k + N)) - r (A (k + N)) = t • (r (B (k + N)) - r (A (k + N))) :=
    fun k => mem_openSegment_smul_sub (hN (k + N) (by omega)).1
  exact middle_to_endpoint_cross_zero h hd (hAt.comp (tendsto_nat_add_atTop N))
    (hBt.comp (tendsto_nat_add_atTop N)) (hMt.comp (tendsto_nat_add_atTop N))
    (fun k => (hN (k + N) (by omega)).2)
    (fun k => (Classical.choose_spec (ht k)).2.2)
    (fun k => ⟨(Classical.choose_spec (ht k)).1, (Classical.choose_spec (ht k)).2.1⟩)

/-- **Escape to the second endpoint forces tangency there.**  If the strict middle points of chords
converging to the chord of `A₀, B₀` run to the *second* endpoint class `(B₀ : KnotParam)`, then the
limit chord is tangent to the knot at `B₀`: `cross3 (r B₀ - r A₀) (velocity r B₀) = 0`. -/
lemma cross_zero_of_tendsto_middle_endpoint_b {r : ℝ → Space} (h : IsSmoothKnot r)
    {A₀ B₀ : ℝ} (hAne : r A₀ ≠ r B₀)
    {a b u : ℕ → KnotParam}
    (ha : Tendsto a atTop (𝓝 (A₀ : KnotParam))) (hb : Tendsto b atTop (𝓝 (B₀ : KnotParam)))
    (hu : Tendsto u atTop (𝓝 (B₀ : KnotParam)))
    (hstr : ∀ᶠ n in atTop, IsMiddleOnChord r (a n) (b n) (u n)) :
    cross3 (r B₀ - r A₀) (velocity r B₀) = 0 := by
  obtain ⟨A, hAt, hAev⟩ :=
    exists_real_lift_of_tendsto_circle (x₀ := (A₀ : KnotParam)) (X₀ := A₀) rfl ha
  obtain ⟨B, hBt, hBev⟩ :=
    exists_real_lift_of_tendsto_circle (x₀ := (B₀ : KnotParam)) (X₀ := B₀) rfl hb
  obtain ⟨M, hMt, hMev⟩ :=
    exists_real_lift_of_tendsto_circle (x₀ := (B₀ : KnotParam)) (X₀ := B₀) rfl hu
  have hstrR : ∀ᶠ n in atTop, r (M n) ∈ openSegment ℝ (r (B n)) (r (A n)) := by
    filter_upwards [hAev, hBev, hMev, hstr] with n hAe hBe hMe hsm
    have hcnv : IsMiddleOnChord r (A n : KnotParam) (B n : KnotParam) (M n : KnotParam) := by
      simpa [← hAe, ← hBe, ← hMe] using hsm
    have h1 := (IsMiddleOnChord_iff_real h (A n) (B n) (M n)).mp hcnv
    rwa [openSegment_symm] at h1
  have hMneB : ∀ᶠ n in atTop, M n ≠ B n := by
    filter_upwards [hBev, hMev, hstr,
      eventually_chord_endpoints_distinct_circle h hAne ha hb] with n hBe hMe hsm hAnb
    have hmn : u n ≠ b n := (IsMiddleOnChord.ne_params h hAnb hsm).2
    intro hMB
    apply hmn
    calc u n = (M n : KnotParam) := hMe.symm
      _ = (B n : KnotParam) := congrArg (fun z : ℝ => (z : KnotParam)) hMB
      _ = b n := hBe
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hstrR.and hMneB)
  have hd : r A₀ - r B₀ ≠ 0 := sub_ne_zero.mpr hAne
  have ht : ∀ k : ℕ, ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      r (M (k + N)) - r (B (k + N)) = t • (r (A (k + N)) - r (B (k + N))) :=
    fun k => mem_openSegment_smul_sub (hN (k + N) (by omega)).1
  have hmain := middle_to_endpoint_cross_zero h hd (hBt.comp (tendsto_nat_add_atTop N))
    (hAt.comp (tendsto_nat_add_atTop N)) (hMt.comp (tendsto_nat_add_atTop N))
    (fun k => (hN (k + N) (by omega)).2)
    (fun k => (Classical.choose_spec (ht k)).2.2)
    (fun k => ⟨(Classical.choose_spec (ht k)).1, (Classical.choose_spec (ht k)).2.1⟩)
  have hneg : r A₀ - r B₀ = -(r B₀ - r A₀) := by abel
  rw [hneg, cross3_neg_left] at hmain
  simpa using hmain

open LeanEval.KnotTheory.Quadrisecant in
/-- **Localisation of the failure of closedness of the trisecant locus**: a point `z` of the
*closure* of the lifted trisecant locus, strictly inside the strip (`0 < z.2 < period`), which is not
itself a trisecant, must be a *tangent chord*: the chord joining the two knot points of parameters
`z.1` and `z.1 + z.2` is tangent to the knot at one of its two endpoints.

Equivalently (contrapositive of `Submission.EndpointEscape.no_middle_to_endpoint` /
`no_middle_to_endpoint_b`): the only way strict trisecants can accumulate at a non-trisecant point is
by their middles running to a chord endpoint, which forces the limit chord to be tangent at that
endpoint.  This is the exact structure of `closure A \ A`, and it is what makes `hg`
(`TorusGeneralPositionTransverse`) insufficient: it does not exclude a tangent chord whose line
carries no third knot point. -/
theorem closure_liftedTrisecant_eq_or_tangent {r : ℝ → Space} (hr : IsSmoothKnot r) {z : ℝ × ℝ}
    (hz : z ∈ closure (liftedTrisecant r)) (h0 : 0 < z.2) (h1 : z.2 < period) :
    z ∈ liftedTrisecant r ∨
      cross3 (r (z.1 + z.2) - r z.1) (velocity r z.1) = 0 ∨
      cross3 (r (z.1 + z.2) - r z.1) (velocity r (z.1 + z.2)) = 0 := by
  -- a sequence in the lifted trisecant locus converging to `z`
  have hex : ∀ n : ℕ, ∃ y ∈ liftedTrisecant r, dist y z < 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hz (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨y, hy, by rwa [dist_comm] at hd⟩
  let w : ℕ → ℝ × ℝ := fun n => Classical.choose (hex n)
  have hwmem : ∀ n, w n ∈ liftedTrisecant r := fun n => (Classical.choose_spec (hex n)).1
  have hwdist : ∀ n, dist (w n) z < 1 / ((n : ℝ) + 1) :=
    fun n => (Classical.choose_spec (hex n)).2
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hwt : Tendsto w atTop (𝓝 z) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => dist_nonneg) (fun n => le_of_lt (hwdist n))
  -- a strict middle of every chord, and a convergent subsequence of the middles
  have hmid : ∀ n : ℕ, ∃ m : KnotParam, IsMiddleOnChord r ((w n).1 : KnotParam)
      (((w n).1 + (w n).2 : ℝ) : KnotParam) m :=
    fun n => exists_middle_of_mem_liftedTrisecant (hwmem n)
  let u : ℕ → KnotParam := fun n => Classical.choose (hmid n)
  have humid : ∀ n, IsMiddleOnChord r ((w n).1 : KnotParam)
      (((w n).1 + (w n).2 : ℝ) : KnotParam) (u n) :=
    fun n => Classical.choose_spec (hmid n)
  obtain ⟨m, -, φ, hφ, hmφ⟩ := (isCompact_univ : IsCompact (Set.univ : Set KnotParam)).tendsto_subseq
    (x := u) (fun n => Set.mem_univ _)
  have hwφ : Tendsto (fun k : ℕ => w (φ k)) atTop (𝓝 z) := hwt.comp hφ.tendsto_atTop
  have hcoe : Continuous (fun x : ℝ => (x : KnotParam)) := QuotientAddGroup.continuous_mk
  have ha : Tendsto (fun k : ℕ => ((w (φ k)).1 : KnotParam)) atTop (𝓝 (z.1 : KnotParam)) :=
    ((hcoe.comp continuous_fst).tendsto z).comp hwφ
  have hb : Tendsto (fun k : ℕ => (((w (φ k)).1 + (w (φ k)).2 : ℝ) : KnotParam)) atTop
      (𝓝 ((z.1 + z.2 : ℝ) : KnotParam)) :=
    ((hcoe.comp (continuous_fst.add continuous_snd)).tendsto z).comp hwφ
  have hm : Tendsto (fun k : ℕ => u (φ k)) atTop (𝓝 m) := hmφ
  have hstrφ : ∀ k, IsMiddleOnChord r ((w (φ k)).1 : KnotParam)
      (((w (φ k)).1 + (w (φ k)).2 : ℝ) : KnotParam) (u (φ k)) := fun k => humid (φ k)
  have hAne : r z.1 ≠ r (z.1 + z.2) := by
    intro hk
    have hkeq : knotMap r ((z.1 : ℝ) : KnotParam)
        = knotMap r (((z.1 + z.2 : ℝ)) : KnotParam) := by
      rw [knotMap_eq_r hr, knotMap_eq_r hr]
      exact hk
    exact coe_ne_coe_of_lt h0 h1 (knotMap_injective hr hkeq)
  -- the three alternatives for the limit of the middles
  rcases eq_or_ne m (z.1 : KnotParam) with hmA | hmA
  · right; left
    exact cross_zero_of_tendsto_middle_endpoint_a hr hAne ha hb (by simpa [hmA] using hm)
      (Eventually.of_forall hstrφ)
  rcases eq_or_ne m (((z.1 + z.2 : ℝ) : KnotParam)) with hmB | hmB
  · right; right
    exact cross_zero_of_tendsto_middle_endpoint_b hr hAne ha hb (by simpa [hmB] using hm)
      (Eventually.of_forall hstrφ)
  · left
    exact mem_liftedTrisecant_of_middle h0 h1 ⟨m, isMiddleOnChord_of_tendsto_middle hr ha hb hm
      (Eventually.of_forall hstrφ) hmA hmB⟩

end

end Work.Drive
