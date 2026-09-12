import Submission.Work.FlatDeck
import Submission.Work.FlatBetweenFrontier
import Submission.Work.RegionDecomposition
import Submission.Work.RegionBetween
import Submission.Work.FlatFrontierFinite
import Submission.Work.DeckFrontier
import Submission.Commons.Topology.Connected.homeo_connectedComponentIn_eq

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Frontier-component deck (Brick B0/B1)

The deck map `period a` (homeomorphism of the plane) carries the flat
component `C = flatComponent f p` to `flatComponent f (period a p)`
(FlatDeck.flatComponent_deck), hence carries the frontier-component data
of `C` to that of its deck image:

* `homeo_conn_image` — generic: a homeomorphism `e : X ≃ₜ Y` maps
  `connectedComponentIn s x` onto `connectedComponentIn (e '' s) (e x)`;
* `frComp_deck` — `period a '' frComp f p z = frComp f (period a p)
  (period a z)` (frontier components of the deck-image component);
* `frSlice_period_image`, `frHeights_deck` — the slice and its heights
  are deck-invariant (`h ↦ h + a`);
* `frCompAt_deck` — `period a '' frCompAt f p h = frCompAt f (period a p)
  (h + a)`;
* chord data uniqueness `stripChord_eq_iff`;
* **`frCompData_deck_flip`** — the canonical chord data of the deck
  component at height `h + a` are the flipped data `(β+a, α+a)` of the
  data at `h`;
* `flatComponent_deck_betweenChord` — the deck image of a
  between-representation is the between-region of the flipped data;
* `sideH_flipped_lt` — pointwise order passes to flipped data;
* **`frHeights_deck_extremes`** — if `C` is the between-region of the
  chords at heights `h₁ < h₂`, then
  `frHeights f (period a p) = {h₁+a, h₂+a}` (Brick (A) +
  `frHeights_deck_mem`);
* **`between_data_deck_heights`** (B3a) — any between-representation
  witness heights `h₁' < h₂'` of the deck component are the shifted
  heights `h₁ + a, h₂ + a`;
* **`between_data_deck_data`** (B3b) — at those witness heights the
  `frCompData` data are the flipped data `(βᵢ+a, αᵢ+a)` (chord-set
  equality `frCompAt_deck` + `stripChord_eq_iff`).

Build: `lake build Submission.Work.FrontierDeck` rc=0, zero sorry.
-/


noncomputable section
namespace Submission.PaperBand

/-- A homeomorphism maps connected-component-in sets onto those of the
image set: `e '' conn s x = conn (e '' s) (e x)`. -/
lemma homeo_conn_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (s : Set X) (x : X) (hx : x ∈ s) :
    e '' connectedComponentIn s x = connectedComponentIn (e '' s) (e x) := by
  apply le_antisymm
  · exact ContinuousOn.image_connectedComponentIn_subset (f := e) (s := s) (a := x)
      e.continuous.continuousOn hx
  · intro y hy
    have hex : e x ∈ e '' s := ⟨x, hx, rfl⟩
    have hback : e.symm '' connectedComponentIn (e '' s) (e x) ⊆
        connectedComponentIn (e.symm '' (e '' s)) (e.symm (e x)) :=
      ContinuousOn.image_connectedComponentIn_subset (f := e.symm) (s := e '' s) (a := e x)
        e.symm.continuous.continuousOn hex
    have hsymm : e.symm (e x) = x := e.left_inv x
    have hset : e.symm '' (e '' s) = s := by
      rw [← Set.image_comp]
      have hcomp : e.symm ∘ e = id := by
        funext z
        exact e.left_inv z
      rw [hcomp]
      ext z
      simp
    have hz : e.symm y ∈ connectedComponentIn s x := by
      have hy1 : e.symm y ∈ e.symm '' connectedComponentIn (e '' s) (e x) :=
        ⟨y, hy, rfl⟩
      have hy2 := hback hy1
      simpa [hsymm, hset] using hy2
    exact ⟨e.symm y, hz, e.right_inv y⟩

/-- `period a` maps the open strip onto itself. -/
lemma period_image_stripInterior (a : ℝ) :
    period a '' stripInterior = stripInterior := by
  ext x
  rw [mem_period_image]
  exact periodInv_stripInterior_iff

/-- The deck map sends the frontier of a flat component onto the frontier
of its deck image component. -/
lemma period_image_frontier_flatComponent {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    period a '' frontier (flatComponent f p) = frontier (flatComponent f (period a p)) := by
  calc
    period a '' frontier (flatComponent f p) = frontier (period a '' flatComponent f p) :=
      homeomorph_image_frontier (periodHomeo a) (flatComponent f p)
    _ = frontier (flatComponent f (period a p)) := by rw [flatComponent_deck hf hp]

/-- The deck map preserves the frontier+strip-interior set of a flat
component. -/
lemma period_image_frontierStrip {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    period a '' (frontier (flatComponent f p) ∩ stripInterior) =
      frontier (flatComponent f (period a p)) ∩ stripInterior := by
  calc
    period a '' (frontier (flatComponent f p) ∩ stripInterior)
        = (period a '' frontier (flatComponent f p)) ∩ (period a '' stripInterior) := by
          change (periodHomeo a) '' (frontier (flatComponent f p) ∩ stripInterior) =
            (periodHomeo a) '' (frontier (flatComponent f p)) ∩
              (periodHomeo a) '' stripInterior
          exact Set.image_inter (periodHomeo a).injective
    _ = frontier (flatComponent f (period a p)) ∩ stripInterior := by
          rw [period_image_frontier_flatComponent hf hp, period_image_stripInterior a]

/-- **Frontier components are deck-invariant**: the deck image of the
component of `z` is the component of `period a z` in the deck-image
component. -/
theorem frComp_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {z : ℝ²}
    (hz : z ∈ frontier (flatComponent f p) ∩ stripInterior) :
    period a '' frComp f p z = frComp f (period a p) (period a z) := by
  change period a '' connectedComponentIn
      (frontier (flatComponent f p) ∩ stripInterior) z =
      connectedComponentIn (frontier (flatComponent f (period a p)) ∩ stripInterior)
        (period a z)
  have hset : period a '' (frontier (flatComponent f p) ∩ stripInterior) =
      frontier (flatComponent f (period a p)) ∩ stripInterior :=
    period_image_frontierStrip hf hp
  have himg := homeo_conn_image (periodHomeo a)
    (frontier (flatComponent f p) ∩ stripInterior) z hz
  simpa [periodHomeo, hset] using himg

/-- The deck map preserves membership in the frontier slice. -/
lemma frSlice_period_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {z : ℝ²} (hz : z ∈ frSlice f p) :
    period a z ∈ frSlice f (period a p) := by
  rw [mem_frSlice_iff]
  have hzF : z ∈ frontier (flatComponent f p) := (mem_frSlice_iff.mp hz).1
  have hz0 : z 0 = 1 / 2 := (mem_frSlice_iff.mp hz).2
  have hzS : z ∈ stripInterior := by
    rw [stripInterior]
    change z 0 ∈ Set.Ioo (0 : ℝ) 1
    rw [hz0]
    constructor <;> norm_num
  constructor
  · have hcl := period_image_frontier_flatComponent hf hp
    have hpm : period a z ∈ period a '' frontier (flatComponent f p) := ⟨z, hzF, rfl⟩
    rwa [hcl] at hpm
  · dsimp [period]
    rw [hz0]
    norm_num

/-- The inverse deck map preserves membership in the frontier slice. -/
lemma frSlice_periodInv_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {z : ℝ²}
    (hz : z ∈ frSlice f (period a p)) :
    periodInv a z ∈ frSlice f p := by
  rw [mem_frSlice_iff]
  rw [mem_frSlice_iff] at hz
  rcases hz with ⟨hzF, hz0⟩
  constructor
  · -- periodInv z ∈ frontier(flatComponent f p): since z = period(periodInv z)
    have hcl := period_image_frontier_flatComponent hf hp
    have hpre : z ∈ period a '' frontier (flatComponent f p) := by
      rw [hcl]
      exact hzF
    rcases hpre with ⟨w, hwF, hw⟩
    have hw' : w = periodInv a z := by
      have h := periodInv_period a w
      rw [hw] at h
      exact h.symm
    rw [hw'] at hwF
    exact hwF
  · dsimp [periodInv]
    rw [hz0]
    norm_num

/-- **The deck image of the slice**: `period` maps the slice of `C` onto
the slice of the deck-image component. -/
theorem frSlice_period_image {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    period a '' frSlice f p = frSlice f (period a p) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact frSlice_period_mem hf hp hz
  · intro y hy
    have hpin : periodInv a y ∈ frSlice f p := frSlice_periodInv_mem hf hp hy
    exact ⟨periodInv a y, hpin, period_periodInv a y⟩

/-- Membership in the height set is deck-invariant: `h` is a slice height
of `C` iff `h + a` is one of the deck-image component. -/
theorem frHeights_deck_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h : ℝ} :
    h + a ∈ frHeights f (period a p) ↔ h ∈ frHeights f p := by
  constructor
  · intro hh
    rw [mem_frHeights_iff] at hh ⊢
    rcases hh with ⟨z, hz, hz1⟩
    have hzi : periodInv a z ∈ frSlice f p := frSlice_periodInv_mem hf hp hz
    have hzi1 : (periodInv a z) 1 = h := by
      have hz1' : z 1 = h + a := hz1
      dsimp [periodInv]
      linarith
    exact ⟨periodInv a z, hzi, hzi1⟩
  · intro hh
    rw [mem_frHeights_iff] at hh ⊢
    rcases hh with ⟨z, hz, hz1⟩
    have hzp : period a z ∈ frSlice f (period a p) := frSlice_period_mem hf hp hz
    have hzp1 : (period a z) 1 = h + a := by
      have hz1' : z 1 = h := hz1
      dsimp [period]
      linarith
    exact ⟨period a z, hzp, hzp1⟩

/-- Slice points are deck-paired: `period a` maps the slice point over
`h` of `C` to the slice point over `h+a` of the deck component. -/
lemma frSlicePoint_period {f : ℝ² → ℝ³} {p : ℝ²} (a h : ℝ) :
    period a (frSlicePoint f p h) = frSlicePoint f (period a p) (h + a) := by
  ext i <;> fin_cases i <;> simp [frSlicePoint, period] <;> norm_num

/-- **Components at slice heights are deck-invariant**. -/
theorem frCompAt_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h : ℝ} (hh : h ∈ frHeights f p) :
    period a '' frCompAt f p h = frCompAt f (period a p) (h + a) := by
  unfold frCompAt
  -- frCompAt f p h = frComp f p (frSlicePoint f p h)
  have hzS : frSlicePoint f p h ∈ frSlice f p := (frSlicePoint_mem hh).1
  have hzFS : frSlicePoint f p h ∈ frontier (flatComponent f p) ∩ stripInterior :=
    mem_frontierStrip_of_frSlice hzS
  have hdeck := frComp_deck hf hp hzFS
  -- hdeck : period '' frComp f p (frSlicePoint f p h) = frComp f (period a p) (period a (frSlicePoint f p h))
  have hp1 : period a (frSlicePoint f p h) = frSlicePoint f (period a p) (h + a) := frSlicePoint_period a h
  simpa [hp1] using hdeck

/-- Two equal strip chords have equal data. -/
lemma stripChord_eq_iff {α β α' β' : ℝ} :
    stripChord α β = stripChord α' β' ↔ α = α' ∧ β = β' := by
  constructor
  · intro h
    have h12 : sideH₁ α β (1 / 2) = sideH₁ α' β' (1 / 2) := by
      have hp : (!₂[(1 / 2 : ℝ), sideH₁ α β (1 / 2)] : ℝ²) ∈ stripChord α β :=
        chord_point_mem (by norm_num) (by norm_num)
      have hp' : (!₂[(1 / 2 : ℝ), sideH₁ α β (1 / 2)] : ℝ²) ∈ stripChord α' β' := by
        rw [h] at hp
        exact hp
      have hx1 : (!₂[(1 / 2 : ℝ), sideH₁ α β (1 / 2)] : ℝ²) 1 =
          sideH₁ α' β' ((!₂[(1 / 2 : ℝ), sideH₁ α β (1 / 2)] : ℝ²) 0) := (mem_stripChord.mp hp').2
      simpa using hx1
    have h13 : sideH₁ α β (1 / 3) = sideH₁ α' β' (1 / 3) := by
      have hp : (!₂[(1 / 3 : ℝ), sideH₁ α β (1 / 3)] : ℝ²) ∈ stripChord α β :=
        chord_point_mem (by norm_num) (by norm_num)
      have hp' : (!₂[(1 / 3 : ℝ), sideH₁ α β (1 / 3)] : ℝ²) ∈ stripChord α' β' := by
        rw [h] at hp
        exact hp
      have hx1 : (!₂[(1 / 3 : ℝ), sideH₁ α β (1 / 3)] : ℝ²) 1 =
          sideH₁ α' β' ((!₂[(1 / 3 : ℝ), sideH₁ α β (1 / 3)] : ℝ²) 0) := (mem_stripChord.mp hp').2
      simpa using hx1
    dsimp [sideH₁] at h12 h13
    constructor <;> nlinarith
  · intro hpair
    rcases hpair with ⟨hα, hβ⟩
    subst hα
    subst hβ
    rfl

/-- **Canonical chord data of the deck component are the flipped data**:
if `(α,β)` is the chord data of the component at height `h`, then the
chord data of the deck component at height `h + a` is `(β+a, α+a)`. -/
theorem frCompData_deck_flip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hh : h ∈ frHeights f p) :
    frCompData hf ha (period a p) (mem_interior_FlatSet_period hf hp) (h + a)
        ((frHeights_deck_mem hf hp).mpr hh) =
      ((frCompData hf ha p hp h hh).2 + a, (frCompData hf ha p hp h hh).1 + a) := by
  let α : ℝ := (frCompData hf ha p hp h hh).1
  let β : ℝ := (frCompData hf ha p hp h hh).2
  let α' : ℝ := (frCompData hf ha (period a p) (mem_interior_FlatSet_period hf hp) (h + a)
      ((frHeights_deck_mem hf hp).mpr hh)).1
  let β' : ℝ := (frCompData hf ha (period a p) (mem_interior_FlatSet_period hf hp) (h + a)
      ((frHeights_deck_mem hf hp).mpr hh)).2
  have hp' : period a p ∈ interior (FlatSet f) := mem_interior_FlatSet_period hf hp
  have hh' : h + a ∈ frHeights f (period a p) := (frHeights_deck_mem hf hp).mpr hh
  -- the data of the deck component realise its component at h+a:
  have hspec' : frCompAt f (period a p) (h + a) =
      stripChord α' β' := by
    simpa [α', β'] using (frCompData_spec hf ha (period a p) hp' hh')
  -- the deck image of the component at h is exactly that:
  have hdeckAt : period a '' frCompAt f p h = frCompAt f (period a p) (h + a) :=
    frCompAt_deck hf hp hh
  -- and the deck image of stripChord α β is stripChord (β+a) (α+a):
  have himg : period a '' frCompAt f p h = stripChord (β + a) (α + a) := by
    have hspec : frCompAt f p h = stripChord α β := by
      simpa [α, β] using (frCompData_spec hf ha p hp hh)
    calc
      period a '' frCompAt f p h = period a '' stripChord α β := by rw [hspec]
      _ = stripChord (β + a) (α + a) := period_image_stripChord (a := a) (α := α) (β := β)
  have heq : stripChord α' β' = stripChord (β + a) (α + a) := by
    rw [← hspec']
    rw [← himg]
    exact hdeckAt.symm
  have hpair := (stripChord_eq_iff (α := α') (β := β') (α' := β + a) (β' := α + a)).mp heq
  apply Prod.ext
  · change α' = β + a
    exact hpair.1
  · change β' = α + a
    exact hpair.2

/-- The deck image of a between-representation is the between-region of
the flipped data: if `flatComponent f p = betweenChord α₁β₁ α₂β₂` then
`flatComponent f (period a p) = betweenChord (β₁+a,α₁+a) (β₂+a,α₂+a)`. -/
lemma flatComponent_deck_betweenChord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {α₁ β₁ α₂ β₂ : ℝ}
    (hC : flatComponent f p = betweenChord α₁ β₁ α₂ β₂) :
    flatComponent f (period a p) = betweenChord (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) := by
  calc
    flatComponent f (period a p) = period a '' flatComponent f p := (flatComponent_deck hf hp).symm
    _ = period a '' betweenChord α₁ β₁ α₂ β₂ := by rw [hC]
    _ = betweenChord (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) :=
      period_image_betweenChord (a := a) (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂)

/-- The pointwise order of the original data gives the pointwise order of
the flipped data (over `u ∈ (0,1)`). -/
lemma sideH_flipped_lt {a α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (β₁ + a) (α₁ + a) u < sideH₁ (β₂ + a) (α₂ + a) u := by
  intro u hu
  have h1 := sideH_deck_flip a α₁ β₁ u
  have h2 := sideH_deck_flip a α₂ β₂ u
  have hlt' : sideH₁ α₁ β₁ (1 - u) < sideH₁ α₂ β₂ (1 - u) := by
    apply hlt (1 - u)
    rw [Set.mem_Ioo] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  rw [h1, h2]
  linarith

/-- **The height set of the deck-image component is the shifted height
set**: if `C` is the between-region of the chords at heights `h₁ < h₂`
(so its only frontier heights are `h₁, h₂`), then the frontier heights
of `period''C` are exactly `{h₁+a, h₂+a}`. -/
theorem frHeights_deck_extremes {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) :
    frHeights f (period a p) = {x : ℝ | x = h₁ + a ∨ x = h₂ + a} := by
  let d₁ : ℝ × ℝ := frCompData hf ha p hp h₁ hh₁
  let d₂ : ℝ × ℝ := frCompData hf ha p hp h₂ hh₂
  -- pointwise order of the original data:
  have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ d₁.1 d₁.2 u < sideH₁ d₂.1 d₂.2 u := by
    intro u hu
    simpa [d₁, d₂] using (sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt u hu)
  -- flipped order:
  have hordF : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (d₁.2 + a) (d₁.1 + a) u < sideH₁ (d₂.2 + a) (d₂.1 + a) u :=
    sideH_flipped_lt (a := a) hord
  -- the deck image of C is the flipped between region:
  have hC' : flatComponent f (period a p) =
      betweenChord (d₁.2 + a) (d₁.1 + a) (d₂.2 + a) (d₂.1 + a) := by
    simpa [d₁, d₂] using (flatComponent_deck_betweenChord hf hp (hC := hC))
  have hhalf₁ : sideH₁ (d₁.2 + a) (d₁.1 + a) (1 / 2) = h₁ + a := by
    have hdata : sideH₁ d₁.1 d₁.2 (1 / 2) = h₁ := by
      simpa [d₁] using (sideH₁_data_half hf ha p hp hh₁)
    dsimp [sideH₁]
    have hd : d₁.1 + (d₁.2 - d₁.1) * (1 / 2) = h₁ := by simpa [sideH₁] using hdata
    calc
      (d₁.2 + a) + ((d₁.1 + a) - (d₁.2 + a)) * (1 / 2) =
          d₁.1 + (d₁.2 - d₁.1) * (1 / 2) + a := by ring
      _ = h₁ + a := by rw [hd]
  have hhalf₂ : sideH₁ (d₂.2 + a) (d₂.1 + a) (1 / 2) = h₂ + a := by
    have hdata : sideH₁ d₂.1 d₂.2 (1 / 2) = h₂ := by
      simpa [d₂] using (sideH₁_data_half hf ha p hp hh₂)
    dsimp [sideH₁]
    have hd : d₂.1 + (d₂.2 - d₂.1) * (1 / 2) = h₂ := by simpa [sideH₁] using hdata
    calc
      (d₂.2 + a) + ((d₂.1 + a) - (d₂.2 + a)) * (1 / 2) =
          d₂.1 + (d₂.2 - d₂.1) * (1 / 2) + a := by ring
      _ = h₂ + a := by rw [hd]
  ext x
  constructor
  · intro hx
    rw [mem_frHeights_iff] at hx
    rcases hx with ⟨z, hzS, hz1⟩
    have hz0 : z 0 = 1 / 2 := (mem_frSlice_iff.mp hzS).2
    have hzF : z ∈ frontier (flatComponent f (period a p)) := (mem_frSlice_iff.mp hzS).1
    have hzS' : z ∈ stripInterior := by
      rw [stripInterior]
      change z 0 ∈ Set.Ioo (0 : ℝ) 1
      rw [hz0]
      constructor <;> norm_num
    have hzF' : z ∈ frontier (betweenChord (d₁.2 + a) (d₁.1 + a) (d₂.2 + a) (d₂.1 + a)) := by
      rw [hC'] at hzF
      exact hzF
    have hzch : z ∈ stripChord (d₁.2 + a) (d₁.1 + a) ∪ stripChord (d₂.2 + a) (d₂.1 + a) := by
      have hzA : z ∈ frontier (betweenChord (d₁.2 + a) (d₁.1 + a) (d₂.2 + a) (d₂.1 + a)) ∩ stripInterior :=
        ⟨hzF', hzS'⟩
      have hEq := frontier_betweenChord (α₁ := d₁.2 + a) (β₁ := d₁.1 + a)
        (α₂ := d₂.2 + a) (β₂ := d₂.1 + a) hordF
      exact hEq ▸ hzA
    rw [Set.mem_union] at hzch
    rcases hzch with hz1ch | hz2ch
    · left
      have hz1' : z 1 = sideH₁ (d₁.2 + a) (d₁.1 + a) (z 0) := (mem_stripChord.mp hz1ch).2
      have hz1eq : z 1 = h₁ + a := by
        rw [hz1', hz0, hhalf₁]
      have : x = h₁ + a := by
        rw [hz1] at hz1eq
        exact hz1eq
      exact this
    · right
      have hz2' : z 1 = sideH₁ (d₂.2 + a) (d₂.1 + a) (z 0) := (mem_stripChord.mp hz2ch).2
      have hz2eq : z 1 = h₂ + a := by
        rw [hz2', hz0, hhalf₂]
      have : x = h₂ + a := by
        rw [hz1] at hz2eq
        exact hz2eq
      exact this
  · intro hx
    rcases hx with hx1 | hx2
    · rw [hx1]
      exact (frHeights_deck_mem hf hp).mpr hh₁
    · rw [hx2]
      exact (frHeights_deck_mem hf hp).mpr hh₂


/-- **Canonical extremal heights of the deck component are the shifted
canonical heights (B3a)**: if `C = flatComponent f p` is the
between-region of the chords at heights `h₁ < h₂`, then ANY
between-representation witness heights `h₁' < h₂'` of the deck-image
component `flatComponent f (period a p)` are exactly `h₁ + a, h₂ + a`. -/
theorem between_data_deck_heights {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ h₁' h₂' : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    (hh₁' : h₁' ∈ frHeights f (period a p)) (hh₂' : h₂' ∈ frHeights f (period a p))
    (hlt' : h₁' < h₂') :
    h₁' = h₁ + a ∧ h₂' = h₂ + a := by
  have hset := frHeights_deck_extremes hf ha hp hh₁ hh₂ hlt hC
  have h₁m : h₁' = h₁ + a ∨ h₁' = h₂ + a := by
    have hh := hset ▸ hh₁'
    change h₁' = h₁ + a ∨ h₁' = h₂ + a at hh
    exact hh
  have h₂m : h₂' = h₁ + a ∨ h₂' = h₂ + a := by
    have hh := hset ▸ hh₂'
    change h₂' = h₁ + a ∨ h₂' = h₂ + a at hh
    exact hh
  have h₁lt₂ : h₁ + a < h₂ + a := by linarith
  rcases h₁m with h₁eq₁ | h₁eq₂
  · constructor
    · exact h₁eq₁
    · rcases h₂m with h₂eq₁ | h₂eq₂
      · exfalso
        linarith
      · exact h₂eq₂
  · exfalso
    rcases h₂m with h₂eq₁ | h₂eq₂
    · linarith
    · linarith

/-- **Canonical chord data of the deck component are the flipped data
(B3b)**: at the (shifted) witness heights `h₁' = h₁ + a` of the deck
component, the `frCompData` data equal `(βᵢ + a, αᵢ + a)` for the data
`(αᵢ, βᵢ)` of the original component.  Proved through chord-set equality:
`frCompAt` at the witness height is the deck image of the chord at `hᵢ`
(`frCompAt_deck`), i.e. `stripChord (βᵢ+a) (αᵢ+a)`, and chord data are
unique (`stripChord_eq_iff`). -/
theorem between_data_deck_data {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ h₁' h₂' : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    {hp' : period a p ∈ interior (FlatSet f)}
    (hh₁' : h₁' ∈ frHeights f (period a p)) (hh₂' : h₂' ∈ frHeights f (period a p))
    (hlt' : h₁' < h₂') :
    frCompData hf ha (period a p) hp' h₁' hh₁' =
        ((frCompData hf ha p hp h₁ hh₁).2 + a, (frCompData hf ha p hp h₁ hh₁).1 + a) ∧
      frCompData hf ha (period a p) hp' h₂' hh₂' =
        ((frCompData hf ha p hp h₂ hh₂).2 + a, (frCompData hf ha p hp h₂ hh₂).1 + a) := by
  have hpair := between_data_deck_heights hf ha hp hh₁ hh₂ hlt hC hh₁' hh₂' hlt'
  rcases hpair with ⟨h₁eq, h₂eq⟩
  constructor
  · -- chord sets at the witness height and at the shifted height agree:
    have hAt₁ : frCompAt f (period a p) h₁' = frCompAt f (period a p) (h₁ + a) := by
      rw [h₁eq]
    have hspec₁' : frCompAt f (period a p) h₁' = stripChord
        (frCompData hf ha (period a p) hp' h₁' hh₁').1
        (frCompData hf ha (period a p) hp' h₁' hh₁').2 :=
      frCompData_spec hf ha (period a p) hp' hh₁'
    have hspec₁ : frCompAt f p h₁ = stripChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 :=
      frCompData_spec hf ha p hp hh₁
    have hflip₁ : frCompAt f (period a p) (h₁ + a) = stripChord
        ((frCompData hf ha p hp h₁ hh₁).2 + a) ((frCompData hf ha p hp h₁ hh₁).1 + a) := by
      calc
        frCompAt f (period a p) (h₁ + a) = period a '' frCompAt f p h₁ := (frCompAt_deck hf hp hh₁).symm
        _ = period a '' stripChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 := by
              rw [hspec₁]
        _ = stripChord ((frCompData hf ha p hp h₁ hh₁).2 + a) ((frCompData hf ha p hp h₁ hh₁).1 + a) :=
              period_image_stripChord (a := a)
                (α := (frCompData hf ha p hp h₁ hh₁).1) (β := (frCompData hf ha p hp h₁ hh₁).2)
    have hchordEq : stripChord (frCompData hf ha (period a p) hp' h₁' hh₁').1
          (frCompData hf ha (period a p) hp' h₁' hh₁').2 =
        stripChord ((frCompData hf ha p hp h₁ hh₁).2 + a) ((frCompData hf ha p hp h₁ hh₁).1 + a) := by
      calc
        stripChord (frCompData hf ha (period a p) hp' h₁' hh₁').1
            (frCompData hf ha (period a p) hp' h₁' hh₁').2 = frCompAt f (period a p) h₁' := hspec₁'.symm
        _ = frCompAt f (period a p) (h₁ + a) := hAt₁
        _ = stripChord ((frCompData hf ha p hp h₁ hh₁).2 + a) ((frCompData hf ha p hp h₁ hh₁).1 + a) := hflip₁
    have hdat : (frCompData hf ha (period a p) hp' h₁' hh₁').1 =
          (frCompData hf ha p hp h₁ hh₁).2 + a ∧
        (frCompData hf ha (period a p) hp' h₁' hh₁').2 =
          (frCompData hf ha p hp h₁ hh₁).1 + a :=
      (stripChord_eq_iff (α := (frCompData hf ha (period a p) hp' h₁' hh₁').1)
        (β := (frCompData hf ha (period a p) hp' h₁' hh₁').2)
        (α' := (frCompData hf ha p hp h₁ hh₁).2 + a)
        (β' := (frCompData hf ha p hp h₁ hh₁).1 + a)).mp hchordEq
    apply Prod.ext
    · exact hdat.1
    · exact hdat.2
  · have hAt₂ : frCompAt f (period a p) h₂' = frCompAt f (period a p) (h₂ + a) := by
      rw [h₂eq]
    have hspec₂' : frCompAt f (period a p) h₂' = stripChord
        (frCompData hf ha (period a p) hp' h₂' hh₂').1
        (frCompData hf ha (period a p) hp' h₂' hh₂').2 :=
      frCompData_spec hf ha (period a p) hp' hh₂'
    have hspec₂ : frCompAt f p h₂ = stripChord
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 :=
      frCompData_spec hf ha p hp hh₂
    have hflip₂ : frCompAt f (period a p) (h₂ + a) = stripChord
        ((frCompData hf ha p hp h₂ hh₂).2 + a) ((frCompData hf ha p hp h₂ hh₂).1 + a) := by
      calc
        frCompAt f (period a p) (h₂ + a) = period a '' frCompAt f p h₂ := (frCompAt_deck hf hp hh₂).symm
        _ = period a '' stripChord (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 := by
              rw [hspec₂]
        _ = stripChord ((frCompData hf ha p hp h₂ hh₂).2 + a) ((frCompData hf ha p hp h₂ hh₂).1 + a) :=
              period_image_stripChord (a := a)
                (α := (frCompData hf ha p hp h₂ hh₂).1) (β := (frCompData hf ha p hp h₂ hh₂).2)
    have hchordEq₂ : stripChord (frCompData hf ha (period a p) hp' h₂' hh₂').1
          (frCompData hf ha (period a p) hp' h₂' hh₂').2 =
        stripChord ((frCompData hf ha p hp h₂ hh₂).2 + a) ((frCompData hf ha p hp h₂ hh₂).1 + a) := by
      calc
        stripChord (frCompData hf ha (period a p) hp' h₂' hh₂').1
            (frCompData hf ha (period a p) hp' h₂' hh₂').2 = frCompAt f (period a p) h₂' := hspec₂'.symm
        _ = frCompAt f (period a p) (h₂ + a) := hAt₂
        _ = stripChord ((frCompData hf ha p hp h₂ hh₂).2 + a) ((frCompData hf ha p hp h₂ hh₂).1 + a) := hflip₂
    have hdat₂ : (frCompData hf ha (period a p) hp' h₂' hh₂').1 =
          (frCompData hf ha p hp h₂ hh₂).2 + a ∧
        (frCompData hf ha (period a p) hp' h₂' hh₂').2 =
          (frCompData hf ha p hp h₂ hh₂).1 + a :=
      (stripChord_eq_iff (α := (frCompData hf ha (period a p) hp' h₂' hh₂').1)
        (β := (frCompData hf ha (period a p) hp' h₂' hh₂').2)
        (α' := (frCompData hf ha p hp h₂ hh₂).2 + a)
        (β' := (frCompData hf ha p hp h₂ hh₂).1 + a)).mp hchordEq₂
    apply Prod.ext
    · exact hdat₂.1
    · exact hdat₂.2

end Submission.PaperBand
