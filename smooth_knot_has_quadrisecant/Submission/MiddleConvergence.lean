import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.SecantSpace
import Submission.QuadrisecantChord
import Submission.TrisecantLocus
import Submission.TrisecantClosed
import Submission.TrisecantStructure
import Submission.StrictZero
import Submission.EndpointEscape
import Submission.TrisecantTransverse
import Submission.SheetAssembly
import Submission.ClassSection

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# Milestone-2 step (iii), assembly item (b) — the middle-convergence lemma

The open-map half of the local 1-manifold structure of the trisecant locus
`O` (`TrisecantTransverse.lean` header) is assembled from (a) the sheet
local section (`ClassSection.lean`), (b) the convergence of strict data
over class sequences along the sheet, and (c) the chart-local open-map
lemma.  Item (b) is the statement that the *strict middle point of a class
is continuous in the class* near a transverse strict class:

**Middle convergence (informal).**  Let `cₙ → c₀` be a sequence of
trisecant classes of a smooth knot (each `cₙ ∈ O`), with `c₀` the class of
the ordered chord `p₀ = (a₀,b₀)`, and let `mₙ` be the (unique under
`QuadrisecantFree`) strict middle point of `cₙ`.  If the chord `{a₀,b₀}`
is *transverse* at both endpoints (no chord direction parallel to either
tangent — `ChordOffEndpointTangents` at real representatives), then
`mₙ → m₀`, where `m₀` is the (unique) strict middle point of `c₀`.

**Proof architecture** (all at the circle/class level, with the
endpoint-escape `EndpointEscape.lean` applied on real lifts):
1. the sheet lifts the classes to ordered chords `Pₙ → p₀` with
   `mobiusCover (Pₙ) = cₙ` eventually (`SheetAssembly`);
2. strict middle points `mₙ` exist on the lifted chords and are unique;
3. **cluster analysis**: the attached strict triples
   `τₙ = (aₙ, (bₙ, mₙ))` lie eventually in the compact closed-middle data
   `closedMiddleData r`, so every cluster point `x` of `mₙ` (with the
   chords already converged to `p₀`) forces `x` to be a *closed* middle of
   the chord `{a₀,b₀}`;
4. **endpoint exclusion**: `x = a₀` or `x = b₀` is impossible — a
   convergent middle subsequence would be lifted to a real sequence
   (`exists_real_lift_of_tendsto_circle`) to which the real-sequence
   endpoint-escape lemmas `no_middle_to_endpoint` / `no_middle_to_endpoint_b`
   apply;
5. **uniqueness**: a non-endpoint closed middle of a transverse strict
   class is a strict middle, and `QuadrisecantFree` (`middle_unique_of_quadrisecantFree`)
   forces it to be `m₀`;
6. by compactness (`IsCompact.tendsto_nhds_of_unique_mapClusterPt` over the
   circle) the unique cluster point property gives `mₙ → m₀`.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-! ## 0. Vocabulary glue: strict middles on representative chords -/

/-- A strict middle point of a class is a strict middle of any ordered
representative of that class (representative independence of the chord). -/
lemma strict_middle_on_chord_of_class_mem {r : ℝ → Space} {c : OpenMobius}
    (hO : c ∈ trisecantSet r) (p : OrderedPairs) (hp : mobiusCover p = c) :
    ∃ m : AddCircle period, IsMiddleOnChord r p.1.1 p.1.2 m := by
  have hc : HasMiddleOnClass r c := hO
  exact (HasMiddleOnClass_iff r p).mp (by simpa [hp] using hc)

/-- Two strict middles of the same ordered chord coincide (no-quadrisecant
case): the strict middle of a chord is a function of the chord. -/
lemma strict_middle_unique_on_chord {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {a b : AddCircle period} (hab : a ≠ b)
    {m₁ m₂ : AddCircle period} (hm₁ : IsMiddleOnChord r a b m₁)
    (hm₂ : IsMiddleOnChord r a b m₂) : m₁ = m₂ :=
  middle_unique_of_quadrisecantFree h hqf hab hm₁ hm₂

/-- Two strict middles of the same *class* coincide: lifting both through
their (possibly different) representatives, `middleOnChord_of_mobiusCover_eq`
transports to a common chord. -/
lemma strict_middle_unique_on_class {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {p q : OrderedPairs}
    (hpq : mobiusCover p = mobiusCover q) {m₁ m₂ : AddCircle period}
    (hm₁ : IsMiddleOnChord r p.1.1 p.1.2 m₁)
    (hm₂ : IsMiddleOnChord r q.1.1 q.1.2 m₂) : m₁ = m₂ := by
  have hm₂' : IsMiddleOnChord r p.1.1 p.1.2 m₂ := by
    exact (middleOnChord_of_mobiusCover_eq p q hpq).mpr hm₂
  exact middle_unique_of_quadrisecantFree h hqf p.2 hm₁ hm₂'

/-- Circle-level strict betweenness transfers to real representatives: with
`knotMap r (x : AddCircle period) = r x`, the strict middle condition on the
circle chord of the real representatives is the real open-segment condition. -/
lemma IsMiddleOnChord_iff_real {r : ℝ → Space} (h : IsSmoothKnot r)
    (A B M : ℝ) : IsMiddleOnChord r (A : AddCircle period) (B : AddCircle period)
      (M : AddCircle period) ↔ r M ∈ openSegment ℝ (r A) (r B) := by
  have hkA : knotMap r (A : AddCircle period) = r A := knotMap_eq_r h A
  have hkB : knotMap r (B : AddCircle period) = r B := knotMap_eq_r h B
  have hkM : knotMap r (M : AddCircle period) = r M := knotMap_eq_r h M
  dsimp [IsMiddleOnChord]
  rw [hkA, hkB, hkM]

/-- The (real) chord of a pair of distinct knot points is nonzero. -/
lemma sub_ne_zero_of_real_ne {r : ℝ → Space} {A B : ℝ} (hAB : r A ≠ r B) :
    r A - r B ≠ 0 := sub_ne_zero.mpr hAB


/-! ## 1. Generic sequence/segment helpers for the cluster analysis -/

/-- A point of a segment which is neither endpoint lies in the open segment
(real-linear convexity: the affine coefficient is strictly inside `(0,1)`). -/
lemma segment_mem_openSegment_of_ne {E : Type*} [AddCommGroup E] [Module ℝ E]
    {x y z : E} (hz : z ∈ segment ℝ x y) (hx : z ≠ x) (hy : z ≠ y) :
    z ∈ openSegment ℝ x y := by
  rw [segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, hz⟩
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hx
    rw [← hz, ht0, AffineMap.lineMap_apply_zero]
  have ht1 : t ≠ 1 := by
    intro ht1
    apply hy
    rw [← hz, ht1, AffineMap.lineMap_apply_one]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  rw [openSegment_eq_image_lineMap]
  exact ⟨t, ⟨htpos, htlt⟩, hz⟩

/-- Two convergent sequences in a metric space with distinct limits have
distinct values eventually (the limits are separated by a positive distance,
and each tail is within half of it). -/
lemma eventually_ne_of_tendsto_limits_ne {Y : Type*} [MetricSpace Y]
    {f g : ℕ → Y} {x y : Y} (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y))
    (hxy : x ≠ y) : ∀ᶠ n in atTop, f n ≠ g n := by
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hδ : 0 < dist x y / 2 := by linarith
  have hfδ : ∀ᶠ n in atTop, dist (f n) x < dist x y / 2 :=
    (Metric.tendsto_nhds.mp hf) (dist x y / 2) hδ
  have hgδ : ∀ᶠ n in atTop, dist (g n) y < dist x y / 2 :=
    (Metric.tendsto_nhds.mp hg) (dist x y / 2) hδ
  filter_upwards [hfδ, hgδ] with n hfn hgn
  intro hfg
  have htri : dist x y ≤ dist x (f n) + dist (g n) y := by
    simpa [hfg] using (dist_triangle x (f n) y)
  have hfn' : dist x (f n) < dist x y / 2 := by simpa [dist_comm] using hfn
  have hlt : dist x (f n) + dist (g n) y < dist x y := by linarith
  linarith

/-- The chord endpoints of a strict middle family with chord classes tending
to two distinct limits are distinct eventually (knot values converge to the
distinct limit values, so they separate). -/
lemma eventually_chord_endpoints_distinct_circle {r : ℝ → Space} (h : IsSmoothKnot r)
    {A₀ B₀ : ℝ} (hAne : r A₀ ≠ r B₀)
    {a b : ℕ → AddCircle period}
    (ha : Tendsto a atTop (𝓝 (A₀ : AddCircle period)))
    (hb : Tendsto b atTop (𝓝 (B₀ : AddCircle period))) :
    ∀ᶠ n in atTop, a n ≠ b n := by
  have hcont : Continuous (knotMap r) := h.knotMap_continuous
  have hf : Tendsto (fun n : ℕ => knotMap r (a n)) atTop (𝓝 (r A₀)) := by
    have hc : ContinuousAt (knotMap r) (A₀ : AddCircle period) := hcont.continuousAt
    have ht0 := (hc.tendsto.comp ha)
    simpa [Function.comp_def, knotMap_eq_r h A₀] using ht0
  have hg : Tendsto (fun n : ℕ => knotMap r (b n)) atTop (𝓝 (r B₀)) := by
    have hc : ContinuousAt (knotMap r) (B₀ : AddCircle period) := hcont.continuousAt
    have ht0 := (hc.tendsto.comp hb)
    simpa [Function.comp_def, knotMap_eq_r h B₀] using ht0
  have hev : ∀ᶠ n in atTop, knotMap r (a n) ≠ knotMap r (b n) :=
    eventually_ne_of_tendsto_limits_ne hf hg hAne
  filter_upwards [hev] with n hn
  intro hab
  exact hn (congrArg (fun z : AddCircle period => knotMap r z) hab)

/-! ## 2. Circle-level endpoint escape (convergent strict middle families) -/

/-- **First-endpoint escape at the circle level.**  Let `(aₙ, bₙ, mₙ)` be
circle families whose chords tend to the chord of the real representatives
`A₀`, `B₀` and whose strict middles `mₙ` tend to the first endpoint class
`(A₀ : AddCircle period)`.  Under the chord transversality at `A₀`
(`cross3 (r A₀ − r B₀) (velocity r A₀) ≠ 0`) this is impossible: real
lifts (`exists_real_lift_of_tendsto_circle`) turn it into the real
endpoint-escape `no_middle_to_endpoint`. -/
lemma no_circle_middle_to_endpoint_a {r : ℝ → Space} (h : IsSmoothKnot r)
    {A₀ B₀ : ℝ} (hAne : r A₀ ≠ r B₀)
    (htrA : cross3 (r A₀ - r B₀) (velocity r A₀) ≠ 0)
    {a b m : ℕ → AddCircle period}
    (ha : Tendsto a atTop (𝓝 (A₀ : AddCircle period)))
    (hb : Tendsto b atTop (𝓝 (B₀ : AddCircle period)))
    (hm : Tendsto m atTop (𝓝 (A₀ : AddCircle period)))
    (hstr : ∀ᶠ n in atTop, IsMiddleOnChord r (a n) (b n) (m n)) : False := by
  rcases exists_real_lift_of_tendsto_circle (x₀ := (A₀ : AddCircle period)) (X₀ := A₀) (by rfl) ha with
    ⟨A, hAt, hAev⟩
  rcases exists_real_lift_of_tendsto_circle (x₀ := (B₀ : AddCircle period)) (X₀ := B₀) (by rfl) hb with
    ⟨B, hBt, hBev⟩
  rcases exists_real_lift_of_tendsto_circle (x₀ := (A₀ : AddCircle period)) (X₀ := A₀) (by rfl) hm with
    ⟨M, hMt, hMev⟩
  have hABne : ∀ᶠ n in atTop, r (A n) ≠ r (B n) := by
    have hf : Tendsto (fun n : ℕ => r (A n)) atTop (𝓝 (r A₀)) :=
      (h.smooth.continuous.tendsto A₀).comp hAt
    have hg : Tendsto (fun n : ℕ => r (B n)) atTop (𝓝 (r B₀)) :=
      (h.smooth.continuous.tendsto B₀).comp hBt
    exact eventually_ne_of_tendsto_limits_ne hf hg hAne
  have hstrR : ∀ᶠ n in atTop, r (M n) ∈ openSegment ℝ (r (A n)) (r (B n)) := by
    filter_upwards [hAev, hBev, hMev, hstr] with n hAe hBe hMe hsm
    have hcnv : IsMiddleOnChord r (A n : AddCircle period) (B n : AddCircle period)
        (M n : AddCircle period) := by
      simpa [← hAe, ← hBe, ← hMe] using hsm
    exact (IsMiddleOnChord_iff_real h (A n) (B n) (M n)).mp hcnv
  have hMneA : ∀ᶠ n in atTop, M n ≠ A n := by
    filter_upwards [hAev, hMev, hstr,
        eventually_chord_endpoints_distinct_circle h hAne ha hb] with n hAe hMe hsm hAnb
    have hmn : m n ≠ a n := (IsMiddleOnChord.ne_params h hAnb hsm).1
    intro hMA
    apply hmn
    calc
      m n = (M n : AddCircle period) := hMe.symm
      _ = (A n : AddCircle period) := congrArg (fun z : ℝ => (z : AddCircle period)) hMA
      _ = a n := hAe
  have hstrMN : ∀ᶠ n in atTop, M n ≠ A n := hMneA
  have hall : ∀ᶠ n in atTop,
      (r (M n) ∈ openSegment ℝ (r (A n)) (r (B n))) ∧ M n ≠ A n :=
    hstrR.and hMneA
  rcases (eventually_atTop.mp hall) with ⟨N, hN⟩
  have hA' : Tendsto (fun k : ℕ => A (k + N)) atTop (𝓝 A₀) :=
    hAt.comp (tendsto_nat_add_atTop N)
  have hB' : Tendsto (fun k : ℕ => B (k + N)) atTop (𝓝 B₀) :=
    hBt.comp (tendsto_nat_add_atTop N)
  have hM' : Tendsto (fun k : ℕ => M (k + N)) atTop (𝓝 A₀) :=
    hMt.comp (tendsto_nat_add_atTop N)
  have hmnA' : ∀ k : ℕ, M (k + N) ≠ A (k + N) := fun k => (hN (k + N) (by omega)).2
  have hmid' : ∀ k : ℕ, r (M (k + N)) ∈ openSegment ℝ (r (A (k + N))) (r (B (k + N))) :=
    fun k => (hN (k + N) (by omega)).1
  exact no_middle_to_endpoint h (sub_ne_zero_of_real_ne hAne) htrA hA' hB' hM' hmnA' hmid'

/-- **Second-endpoint escape at the circle level**: the mirror of
`no_circle_middle_to_endpoint_a` for middles tending to the *second*
endpoint class `(B₀ : AddCircle period)`, excluded by the chord
transversality at `B₀` (via the real endpoint-escape
`no_middle_to_endpoint_b`). -/
lemma no_circle_middle_to_endpoint_b {r : ℝ → Space} (h : IsSmoothKnot r)
    {A₀ B₀ : ℝ} (hAne : r A₀ ≠ r B₀)
    (htrB : cross3 (r A₀ - r B₀) (velocity r B₀) ≠ 0)
    {a b m : ℕ → AddCircle period}
    (ha : Tendsto a atTop (𝓝 (A₀ : AddCircle period)))
    (hb : Tendsto b atTop (𝓝 (B₀ : AddCircle period)))
    (hm : Tendsto m atTop (𝓝 (B₀ : AddCircle period)))
    (hstr : ∀ᶠ n in atTop, IsMiddleOnChord r (a n) (b n) (m n)) : False := by
  rcases exists_real_lift_of_tendsto_circle (x₀ := (A₀ : AddCircle period)) (X₀ := A₀) (by rfl) ha with
    ⟨A, hAt, hAev⟩
  rcases exists_real_lift_of_tendsto_circle (x₀ := (B₀ : AddCircle period)) (X₀ := B₀) (by rfl) hb with
    ⟨B, hBt, hBev⟩
  rcases exists_real_lift_of_tendsto_circle (x₀ := (B₀ : AddCircle period)) (X₀ := B₀) (by rfl) hm with
    ⟨M, hMt, hMev⟩
  have hstrR : ∀ᶠ n in atTop, r (M n) ∈ openSegment ℝ (r (A n)) (r (B n)) := by
    filter_upwards [hAev, hBev, hMev, hstr] with n hAe hBe hMe hsm
    have hcnv : IsMiddleOnChord r (A n : AddCircle period) (B n : AddCircle period)
        (M n : AddCircle period) := by
      simpa [← hAe, ← hBe, ← hMe] using hsm
    exact (IsMiddleOnChord_iff_real h (A n) (B n) (M n)).mp hcnv
  have hMneB : ∀ᶠ n in atTop, M n ≠ B n := by
    filter_upwards [hBev, hMev, hstr,
        eventually_chord_endpoints_distinct_circle h hAne ha hb] with n hBe hMe hsm hAnb
    have hmn : m n ≠ b n := (IsMiddleOnChord.ne_params h hAnb hsm).2
    intro hMB
    apply hmn
    calc
      m n = (M n : AddCircle period) := hMe.symm
      _ = (B n : AddCircle period) := congrArg (fun z : ℝ => (z : AddCircle period)) hMB
      _ = b n := hBe
  have hall : ∀ᶠ n in atTop,
      (r (M n) ∈ openSegment ℝ (r (A n)) (r (B n))) ∧ M n ≠ B n :=
    hstrR.and hMneB
  rcases (eventually_atTop.mp hall) with ⟨N, hN⟩
  have hA' : Tendsto (fun k : ℕ => A (k + N)) atTop (𝓝 A₀) :=
    hAt.comp (tendsto_nat_add_atTop N)
  have hB' : Tendsto (fun k : ℕ => B (k + N)) atTop (𝓝 B₀) :=
    hBt.comp (tendsto_nat_add_atTop N)
  have hM' : Tendsto (fun k : ℕ => M (k + N)) atTop (𝓝 B₀) :=
    hMt.comp (tendsto_nat_add_atTop N)
  have hmnB' : ∀ k : ℕ, M (k + N) ≠ B (k + N) := fun k => (hN (k + N) (by omega)).2
  have hmid' : ∀ k : ℕ, r (M (k + N)) ∈ openSegment ℝ (r (A (k + N))) (r (B (k + N))) :=
    fun k => (hN (k + N) (by omega)).1
  exact no_middle_to_endpoint_b h (sub_ne_zero_of_real_ne hAne) htrB hA' hB' hM' hmnB' hmid'

/-! ## 3. The limit of strict middles of chords converging to a transverse
chord is the unique strict middle of the limit chord -/

/-- **Limit middle of a transverse chord.**  Let strict middle families
`uₙ` on chords `(aₙ, bₙ)` whose chord classes converge to the chord of the
real representatives `A₀`, `B₀` (with `r A₀ ≠ r B₀` and the chord
transverse at both endpoints) converge to some circle point `x`.  Then
`x` is a strict middle of the limit chord: the closed-middle data persist
at the limit (`IsClosed.mem_of_tendsto` on `closedMiddleData r`), the
endpoint alternatives are excluded by the circle endpoint-escape lemmas,
and a non-endpoint point of the chord is a strict middle
(`segment_mem_openSegment_of_ne`). -/
lemma closed_middle_limit_of_transverse_chord {r : ℝ → Space} (h : IsSmoothKnot r)
    {A₀ B₀ : ℝ} (hAne : r A₀ ≠ r B₀)
    (htrA : cross3 (r A₀ - r B₀) (velocity r A₀) ≠ 0)
    (htrB : cross3 (r A₀ - r B₀) (velocity r B₀) ≠ 0)
    {a b u : ℕ → AddCircle period} {x : AddCircle period}
    (ha : Tendsto a atTop (𝓝 (A₀ : AddCircle period)))
    (hb : Tendsto b atTop (𝓝 (B₀ : AddCircle period)))
    (hu : Tendsto u atTop (𝓝 x))
    (hstr : ∀ᶠ n in atTop, IsMiddleOnChord r (a n) (b n) (u n)) :
    IsMiddleOnChord r (A₀ : AddCircle period) (B₀ : AddCircle period) x := by
  have hx_neA : x ≠ (A₀ : AddCircle period) := by
    intro hxA
    exact no_circle_middle_to_endpoint_a h hAne htrA ha hb (by simpa [hxA] using hu) hstr
  have hx_neB : x ≠ (B₀ : AddCircle period) := by
    intro hxB
    exact no_circle_middle_to_endpoint_b h hAne htrB ha hb (by simpa [hxB] using hu) hstr
  let τ : ℕ → KnotParamTriple := fun n => (a n, ((b n), u n))
  have hτ : Tendsto τ atTop (𝓝 ((A₀ : AddCircle period), ((B₀ : AddCircle period), x))) := by
    have hmid : Tendsto (fun n : ℕ => ((b n), u n)) atTop
        (𝓝 ((B₀ : AddCircle period), x)) := Filter.Tendsto.prodMk_nhds hb hu
    dsimp [τ]
    exact Filter.Tendsto.prodMk_nhds ha hmid
  have hclosed : ((A₀ : AddCircle period), ((B₀ : AddCircle period), x)) ∈ closedMiddleData r := by
    have hev : ∀ᶠ n in atTop, τ n ∈ closedMiddleData r := by
      filter_upwards [hstr] with n hsm
      have hmemO : (a n, ((b n), u n)) ∈ openMiddleData r := by
        change IsMiddleOnOpenChord r (a n) (b n) (u n)
        simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using hsm
      simpa [τ] using (openMiddleData_subset_closedMiddleData r hmemO)
    exact IsClosed.mem_of_tendsto (isClosed_closedMiddleData h) hτ hev
  have hxm : knotMap r x ∈ segment ℝ (knotMap r (A₀ : AddCircle period))
      (knotMap r (B₀ : AddCircle period)) := by
    exact (mem_closedMiddleData_iff r).mp hclosed
  have hkxA : knotMap r x ≠ knotMap r (A₀ : AddCircle period) := by
    intro hk
    exact hx_neA ((knotMap_injective h) hk)
  have hkxB : knotMap r x ≠ knotMap r (B₀ : AddCircle period) := by
    intro hk
    exact hx_neB ((knotMap_injective h) hk)
  exact segment_mem_openSegment_of_ne (E := Space) hxm hkxA hkxB

/-- **The limit middle equals any strict middle of the limit chord.**  In
the situation of `closed_middle_limit_of_transverse_chord`, if `m₀` is a
strict middle of the limit chord, then `QuadrisecantFree` (at most one
strict middle per chord) forces `x = m₀`. -/
lemma limit_middle_eq_strict_middle {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r)
    {A₀ B₀ : ℝ} (hAne : r A₀ ≠ r B₀)
    (htrA : cross3 (r A₀ - r B₀) (velocity r A₀) ≠ 0)
    (htrB : cross3 (r A₀ - r B₀) (velocity r B₀) ≠ 0)
    {a b u : ℕ → AddCircle period} {x : AddCircle period}
    (ha : Tendsto a atTop (𝓝 (A₀ : AddCircle period)))
    (hb : Tendsto b atTop (𝓝 (B₀ : AddCircle period)))
    (hu : Tendsto u atTop (𝓝 x))
    (hstr : ∀ᶠ n in atTop, IsMiddleOnChord r (a n) (b n) (u n))
    {m₀ : AddCircle period}
    (hm₀ : IsMiddleOnChord r (A₀ : AddCircle period) (B₀ : AddCircle period) m₀) :
    x = m₀ := by
  have hxstr := closed_middle_limit_of_transverse_chord h hAne htrA htrB ha hb hu hstr
  have habc : (A₀ : AddCircle period) ≠ (B₀ : AddCircle period) := by
    intro hab
    apply hAne
    have hk : knotMap r (A₀ : AddCircle period) = knotMap r (B₀ : AddCircle period) :=
      congrArg (fun z : AddCircle period => knotMap r z) hab
    simpa [knotMap_eq_r h A₀, knotMap_eq_r h B₀] using hk
  exact middle_unique_of_quadrisecantFree h hqf habc hxstr hm₀

/-! ## 4. The canonical strict middle of a class and the middle-convergence
theorem -/

/-- **The canonical strict middle point of a trisecant class**: a class
`c ∈ O` carries a strict middle point (`HasMiddleOnClass`), and one is
chosen canonically by choice; under `QuadrisecantFree` it is unique, so any
two canonical choices coincide. -/
noncomputable def classMiddle (r : ℝ → Space) (c : OpenMobius) (hc : c ∈ trisecantSet r) :
    AddCircle period :=
  Classical.choose ((HasMiddleOnClass_iff_middleSet_nonempty r c).mp hc)

/-- The canonical middle of a class is a middle point of the class. -/
lemma classMiddle_mem_middleSet (r : ℝ → Space) (c : OpenMobius) (hc : c ∈ trisecantSet r) :
    classMiddle r c hc ∈ MiddlePointsOnClass r c :=
  Classical.choose_spec ((HasMiddleOnClass_iff_middleSet_nonempty r c).mp hc)

/-- The canonical middle is a strict middle of any ordered representative of
the class (representative independence of the chord). -/
lemma classMiddle_middle_on_rep {r : ℝ → Space} (c : OpenMobius) (hc : c ∈ trisecantSet r)
    (p : OrderedPairs) (hp : mobiusCover p = c) :
    IsMiddleOnChord r p.1.1 p.1.2 (classMiddle r c hc) := by
  rcases (mem_MiddlePointsOnClass_iff r c (classMiddle r c hc)).mp
      (classMiddle_mem_middleSet r c hc) with ⟨q, hq, hmq⟩
  have hpq : mobiusCover q = mobiusCover p := by rw [hq, hp]
  exact (middleOnChord_of_mobiusCover_eq q p hpq).mp hmq

/-- Along a lifted class sequence (chords `Pₙ` over `cₙ`), the canonical
middles are strict middles of the lifted chords eventually. -/
lemma classMiddle_middle_on_lift {r : ℝ → Space} {c : ℕ → OpenMobius}
    (hcO : ∀ n, c n ∈ trisecantSet r) {P : ℕ → OrderedPairs}
    (hPc : ∀ᶠ n in atTop, mobiusCover (P n) = c n) :
    ∀ᶠ n in atTop, IsMiddleOnChord r (P n).1.1 (P n).1.2 (classMiddle r (c n) (hcO n)) := by
  filter_upwards [hPc] with n hPn
  exact classMiddle_middle_on_rep (c n) (hcO n) (P n) hPn


/-- **Middle convergence over the sheet (the milestone lemma).**  Let
`cₙ → c₀ = mobiusCover (a₀,b₀)` be a sequence of trisecant classes of a
smooth knot, with real representatives `A₀`, `B₀` of the chord endpoints
(`r A₀ ≠ r B₀`, chord transverse at both endpoints —
`ChordOffEndpointTangents r A₀ B₀`).  Under `QuadrisecantFree`, the
canonical strict middles of the classes converge to the (unique) strict
middle `m₀` of the limit chord.  The proof: lift the chords onto the sheet
(`exists_lift_of_tendsto`), so the canonical middles are strict middles of
the lifted chords eventually (`classMiddle_middle_on_lift`); then every
cluster point of the middle sequence is a limit of a convergent middle
subsequence (`MapClusterPt.tendsto_subseq`) whose strict data converge to
a strict middle of the limit chord (`closed_middle_limit_of_transverse_chord`),
hence equals `m₀` (`limit_middle_eq_strict_middle`); compactness of the
circle (`IsCompact.tendsto_nhds_of_unique_mapClusterPt`) upgrades the
unique-cluster-point property to convergence. -/
theorem middle_tendsto_of_class_tendsto {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {p₀ : OrderedPairs} {m₀ : AddCircle period}
    {A₀ B₀ : ℝ}
    (hA₀ : (A₀ : AddCircle period) = p₀.1.1) (hB₀ : (B₀ : AddCircle period) = p₀.1.2)
    (hAne : r A₀ ≠ r B₀) (hchord : ChordOffEndpointTangents r A₀ B₀)
    (hm₀ : IsMiddleOnChord r p₀.1.1 p₀.1.2 m₀)
    {c : ℕ → OpenMobius} (hcO : ∀ n : ℕ, c n ∈ trisecantSet r)
    (hc : Tendsto c atTop (𝓝 (mobiusCover p₀))) :
    Tendsto (fun n : ℕ => classMiddle r (c n) (hcO n)) atTop (𝓝 m₀) := by
  rcases hchord with ⟨htrA, htrB⟩
  have hm₀' : IsMiddleOnChord r (A₀ : AddCircle period) (B₀ : AddCircle period) m₀ := by
    simpa [hA₀, hB₀] using hm₀
  let u : ℕ → AddCircle period := fun n => classMiddle r (c n) (hcO n)
  let sh : MobiusSheet p₀ := Classical.choice (MobiusSheet.nonempty p₀)
  rcases MobiusSheet.exists_lift_of_tendsto sh hc with ⟨P, hP, hPc⟩
  have hstrOn : ∀ᶠ n in atTop,
      IsMiddleOnChord r (P n).1.1 (P n).1.2 (u n) := by
    simpa [u] using (classMiddle_middle_on_lift (r := r) hcO hPc)
  -- cluster-point analysis: every cluster point of u is m₀
  have hunique : ∀ x : AddCircle period, MapClusterPt x atTop u → x = m₀ := by
    intro x hxcl
    rcases MapClusterPt.tendsto_subseq hxcl with ⟨ψ, hψ, hux⟩
    have hle : ∀ k : ℕ, k ≤ ψ k := fun k => hψ.id_le k
    have hstrψ : ∀ᶠ k in atTop,
        IsMiddleOnChord r (P (ψ k)).1.1 (P (ψ k)).1.2 (u (ψ k)) := by
      rcases (eventually_atTop.mp hstrOn) with ⟨N, hN⟩
      filter_upwards [eventually_ge_atTop N] with k hk
      exact hN (ψ k) (le_trans hk (hle k))
    have hPψ : Tendsto (P ∘ ψ) atTop (𝓝 p₀) := hP.comp hψ.tendsto_atTop
    have ha : Tendsto (fun k : ℕ => (P (ψ k)).1.1) atTop (𝓝 (A₀ : AddCircle period)) := by
      have hf : Continuous (fun pp : OrderedPairs => pp.1.1) :=
        continuous_fst.comp continuous_subtype_val
      have hbase : Tendsto (fun k : ℕ => (P (ψ k)).1.1) atTop (𝓝 p₀.1.1) := by
        simpa [Function.comp_def] using ((hf.tendsto p₀).comp hPψ)
      simpa [hA₀] using hbase
    have hb : Tendsto (fun k : ℕ => (P (ψ k)).1.2) atTop (𝓝 (B₀ : AddCircle period)) := by
      have hf : Continuous (fun pp : OrderedPairs => pp.1.2) :=
        continuous_snd.comp continuous_subtype_val
      have hbase : Tendsto (fun k : ℕ => (P (ψ k)).1.2) atTop (𝓝 p₀.1.2) := by
        simpa [Function.comp_def] using ((hf.tendsto p₀).comp hPψ)
      simpa [hB₀] using hbase
    have hux' : Tendsto (fun k : ℕ => u (ψ k)) atTop (𝓝 x) := hux
    exact limit_middle_eq_strict_middle h hqf hAne htrA htrB ha hb hux' hstrψ hm₀'
  -- compactness upgrades unique cluster points to convergence
  have hmain := IsCompact.tendsto_nhds_of_unique_mapClusterPt
    (s := (Set.univ : Set (AddCircle period))) (l := atTop) (y := m₀) (f := u)
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set (AddCircle period))))
    (by simp [u])
    (by intro x hx hxc; exact hunique x hxc)
  simpa [u] using hmain

end LeanEval.KnotTheory.Quadrisecant
