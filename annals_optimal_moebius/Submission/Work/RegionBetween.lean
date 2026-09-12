import Submission.Work.RegionDecomposition

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# T1-ii Layer 3 part B, step (3): between-regions of two chords

The open BETWEEN-region of two full chords (`betweenChord α₁β₁ α₂β₂`) is
the set of strip-interior points strictly above the first chord and
strictly below the second:

    {x | x ∈ stripInterior ∧ sideH₁ α₁β₁ (x0) < x1 ∧ x1 < sideH₁ α₂β₂ (x0)}.

For POINTWISE-ORDERED chords (`h₁ < h₂` on all of `(0,1)`) it is
connected (the affine parametrisation `(u,v) ↦ (u, h₁u + v(h₂u−h₁u))`
from the square `(0,1)×(0,1)`).  This file also records the order
interactions needed by the decomposition:
* above/below half-strips are monotone under pointwise chord order
  (`aboveChord_subset_of_below`, `belowChord_subset_of_below`): if chord₁
  is pointwise below chord₂ then `aboveChord(2) ⊆ aboveChord(1)` and
  `belowChord(1) ⊆ belowChord(2)`;
* a connected strip set avoiding both bounding chords and lying between
  them is contained in the between region (`preconnected_between_mem`);
* membership/cover lemmas: any point of `W` between consecutive chords
  lies in the between region etc.

Build: `lake build Submission.Work.RegionBetween` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The open between-region of two full chords: strip-interior points
strictly above `stripChord α₁β₁` and strictly below `stripChord α₂β₂`. -/
def betweenChord (α₁ β₁ α₂ β₂ : ℝ) : Set ℝ² :=
  {x | x ∈ stripInterior ∧ sideH₁ α₁ β₁ (x 0) < x 1 ∧ x 1 < sideH₁ α₂ β₂ (x 0)}

/-- Membership in a between-region. -/
lemma mem_betweenChord {α₁ β₁ α₂ β₂ : ℝ} {x : ℝ²} :
    x ∈ betweenChord α₁ β₁ α₂ β₂ ↔
      x ∈ stripInterior ∧ sideH₁ α₁ β₁ (x 0) < x 1 ∧ x 1 < sideH₁ α₂ β₂ (x 0) := by rfl

/-- Between regions lie in the open strip. -/
lemma betweenChord_subset_stripInterior (α₁ β₁ α₂ β₂ : ℝ) :
    betweenChord α₁ β₁ α₂ β₂ ⊆ stripInterior := by
  intro x hx
  exact (mem_betweenChord.mp hx).1

/-- The parametrisation of the between region of two pointwise ordered
chords: `(u,v) ↦ (u, h₁ u + v (h₂ u − h₁ u))` maps `(0,1)×(0,1)` onto
`betweenChord α₁β₁ α₂β₂`. -/
lemma betweenChord_eq_image {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u) :
    betweenChord α₁ β₁ α₂ β₂ =
      (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α₁ β₁ p.1 +
        p.2 * (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1)]) ''
        ((Set.Ioo 0 1) ×ˢ (Set.Ioo 0 1)) := by
  ext x
  constructor
  · intro hx
    rw [mem_betweenChord] at hx
    rcases hx with ⟨hxS, hx₁, hx₂⟩
    have hdiff : 0 < sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0) := by linarith
    let v : ℝ := (x 1 - sideH₁ α₁ β₁ (x 0)) / (sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0))
    have hv : v ∈ Set.Ioo 0 1 := by
      rw [Set.mem_Ioo]
      constructor
      · dsimp [v]
        rw [div_pos_iff]
        left
        constructor <;> linarith
      · dsimp [v]
        rw [div_lt_one hdiff]
        linarith
    rw [Set.mem_image]
    refine ⟨(x 0, v), ?_, ?_⟩
    · rw [Set.mem_prod]
      constructor
      · rw [Set.mem_Ioo]
        rw [stripInterior] at hxS
        exact ⟨hxS.1, hxS.2⟩
      · exact hv
    · ext i <;> fin_cases i
      · simp
      · dsimp [v]
        field_simp [ne_of_gt hdiff]
        ring
  · intro hx
    rcases hx with ⟨p, hp, hxeq⟩
    rw [Set.mem_prod] at hp
    rcases hp with ⟨hp₁, hp₂⟩
    rw [mem_betweenChord]
    rw [← hxeq]
    have hp₁₀ : 0 < p.1 := (Set.mem_Ioo.mp hp₁).1
    have hp₁₁ : p.1 < 1 := (Set.mem_Ioo.mp hp₁).2
    have hS : (!₂[p.1, sideH₁ α₁ β₁ p.1 + p.2 * (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1)] : ℝ²)
        ∈ stripInterior := by
      rw [stripInterior]
      constructor <;> simp [hp₁₀, hp₁₁]
    refine ⟨hS, ?_, ?_⟩
    · have h₁lt₂ : sideH₁ α₁ β₁ p.1 < sideH₁ α₂ β₂ p.1 := hlt p.1 hp₁
      have hvp : 0 < p.2 := (Set.mem_Ioo.mp hp₂).1
      have hdiff : 0 < sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1 := by linarith
      have hmul : 0 < p.2 * (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1) :=
        mul_pos hvp hdiff
      simp
      exact hmul
    · have hvp : p.2 < 1 := (Set.mem_Ioo.mp hp₂).2
      have h₁lt₂ : sideH₁ α₁ β₁ p.1 < sideH₁ α₂ β₂ p.1 := hlt p.1 hp₁
      have hdiff : 0 < sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1 := by linarith
      have hmul : p.2 * (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1) <
          sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1 := by
        exact (mul_lt_iff_lt_one_left hdiff).mpr hvp
      simp
      calc
        sideH₁ α₁ β₁ p.1 + p.2 * (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1)
            < sideH₁ α₁ β₁ p.1 + (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1) := add_lt_add_right hmul (sideH₁ α₁ β₁ p.1)
        _ = sideH₁ α₂ β₂ p.1 := by ring

/-- The between-region of two pointwise ordered chords is connected. -/
lemma isPreconnected_betweenChord {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u) :
    IsPreconnected (betweenChord α₁ β₁ α₂ β₂) := by
  have hD : IsPreconnected ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioo (0 : ℝ) 1)) :=
    IsPreconnected.prod isPreconnected_Ioo isPreconnected_Ioo
  have hF : ContinuousOn (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α₁ β₁ p.1 +
        p.2 * (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1)])
      ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioo (0 : ℝ) 1)) := by
    intro p hp
    dsimp [sideH₁]
    fun_prop
  have himg : IsPreconnected
      ((fun p : ℝ × ℝ => !₂[p.1, sideH₁ α₁ β₁ p.1 +
        p.2 * (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1)]) ''
        ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioo (0 : ℝ) 1))) :=
    IsPreconnected.image hD (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α₁ β₁ p.1 +
        p.2 * (sideH₁ α₂ β₂ p.1 - sideH₁ α₁ β₁ p.1)]) hF
  simpa [betweenChord_eq_image hlt] using himg

/-- Half-strip monotonicity: if chord₁ is pointwise below chord₂ then
everything above chord₂ is above chord₁. -/
lemma aboveChord_subset_of_below {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u) :
    aboveChord α₂ β₂ ⊆ aboveChord α₁ β₁ := by
  intro x hx
  rw [mem_aboveChord] at hx ⊢
  exact ⟨hx.1, by
    have hlt' := hlt (x 0) (by
      rw [Set.mem_Ioo]
      rw [stripInterior] at hx
      exact ⟨hx.1.1, hx.1.2⟩)
    linarith⟩

/-- Half-strip monotonicity: if chord₁ is pointwise below chord₂ then
everything below chord₁ is below chord₂. -/
lemma belowChord_subset_of_below {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u) :
    belowChord α₁ β₁ ⊆ belowChord α₂ β₂ := by
  intro x hx
  rw [mem_belowChord] at hx ⊢
  exact ⟨hx.1, by
    have hlt' := hlt (x 0) (by
      rw [Set.mem_Ioo]
      rw [stripInterior] at hx
      exact ⟨hx.1.1, hx.1.2⟩)
    linarith⟩

/-- If the second chord is pointwise below the first, everything above
the first is above the second, so a point above `α₂β₂` but below `α₁β₁`
is impossible unless the chords cross: for disjoint ordered chords the
"between" side sets are consistent.  (Concretely: `aboveChord(1)`
avoids `belowChord(2)` when chord₂ < chord₁ pointwise.) -/
lemma aboveChord_disjoint_belowChord_of_below {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₂ β₂ u < sideH₁ α₁ β₁ u) :
    Disjoint (aboveChord α₁ β₁) (belowChord α₂ β₂) := by
  rw [Set.disjoint_left]
  intro x hxAbove hxBelow
  rw [mem_aboveChord] at hxAbove
  rw [mem_belowChord] at hxBelow
  have hlt' := hlt (x 0) (by
    rw [Set.mem_Ioo]
    rw [stripInterior] at hxAbove
    exact ⟨hxAbove.1.1, hxAbove.1.2⟩)
  linarith

/-- A connected set inside the between region structure: if `s` is
preconnected, avoids both chords, meets the region between them, and
lies in `W` (the frontier-free part), it is contained in the
between-region once the bounding chords are consecutive (handled by the
caller).  Here the basic geometric content: a preconnected strip set
that stays above chord₁ and below chord₂ lies in the between region. -/
lemma preconnected_strip_between {α₁ β₁ α₂ β₂ : ℝ} {s : Set ℝ²}
    (hsS : s ⊆ stripInterior) (hspre : IsPreconnected s)
    (h₁ : s ∩ aboveChord α₁ β₁ = s) (h₂ : s ∩ belowChord α₂ β₂ = s) :
    s ⊆ betweenChord α₁ β₁ α₂ β₂ := by
  intro x hx
  rw [mem_betweenChord]
  have hx₁ : x ∈ aboveChord α₁ β₁ := by
    have hmem : x ∈ s ∩ aboveChord α₁ β₁ := by
      rw [h₁]
      exact hx
    exact hmem.2
  have hx₂ : x ∈ belowChord α₂ β₂ := by
    have hmem : x ∈ s ∩ belowChord α₂ β₂ := by
      rw [h₂]
      exact hx
    exact hmem.2
  rw [mem_aboveChord] at hx₁
  rw [mem_belowChord] at hx₂
  exact ⟨hsS hx, hx₁.2, hx₂.2⟩



/-- The chord data of the frontier component at a slice height: a chosen
pair `(α,β)` with `frCompAt f p h = stripChord α β`. -/
noncomputable def frCompData {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) (h : ℝ)
    (hh : h ∈ frHeights f p) : ℝ × ℝ :=
  (Classical.choose (frCompAt_full_chord hf ha hp hh),
    Classical.choose (Classical.choose_spec (frCompAt_full_chord hf ha hp hh)))

/-- The chosen chord data realises the component at `h`. -/
lemma frCompData_spec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hh : h ∈ frHeights f p) :
    frCompAt f p h = stripChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 := by
  have hc := frCompAt_full_chord hf ha hp hh
  have hα := Classical.choose_spec hc
  have hβ := Classical.choose_spec hα
  simpa [frCompData] using hβ

/-- The component at a slice height is contained in the frontier. -/
lemma frCompAt_subset_frontier {f : ℝ² → ℝ³} {p : ℝ²} {h : ℝ} :
    frCompAt f p h ⊆ frontier (flatComponent f p) := by
  intro x hx
  have hx' : x ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior)
      (frSlicePoint f p h) := by
    exact hx
  exact (connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior)
    (frSlicePoint f p h) hx').1

/-- The component at a slice height avoids the flat component `C` (it lies
in the frontier, and `C` is open). -/
lemma flatComponent_disjoint_frCompAt {f : ℝ² → ℝ³} {p : ℝ²} {h : ℝ} :
    Disjoint (flatComponent f p) (frCompAt f p h) := by
  rw [Set.disjoint_left]
  intro x hxC hxK
  have hxF : x ∈ frontier (flatComponent f p) := frCompAt_subset_frontier hxK
  have hxopen : x ∈ interior (flatComponent f p) := by
    rw [(isOpen_flatComponent f p).interior_eq]
    exact hxC
  rw [frontier] at hxF
  exact hxF.2 hxopen

/-- **Side dichotomy**: for each slice height `h`, the flat component `C`
lies strictly on one side of the component chord: entirely above it or
entirely below it. -/
theorem flatComponent_above_or_below {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hh : h ∈ frHeights f p) :
    flatComponent f p ⊆ aboveChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 ∨
    flatComponent f p ⊆ belowChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 := by
  have hC : flatComponent f p ⊆ stripInterior := flatComponent_subset_stripInterior f p
  have hpre : IsPreconnected (flatComponent f p) := isPreconnected_flatComponent f p
  have hdisc : Disjoint (flatComponent f p) (frCompAt f p h) := flatComponent_disjoint_frCompAt
  have hd : Disjoint (flatComponent f p) (stripChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2) := by
    rw [← frCompData_spec hf ha p hp hh]
    exact hdisc
  have hne : (flatComponent f p).Nonempty := ⟨p, mem_flatComponent hp⟩
  rcases preconnected_avoiding_chord_one_side (α := (frCompData hf ha p hp h hh).1)
    (β := (frCompData hf ha p hp h hh).2) hC hpre hd hne with hA | hB
  · exact Or.inl hA
  · exact Or.inr hB

/-- The point of `C` at `x0 = 1/2` on the side of the chord: pick any
point of `C`, it is on one side; the dichotomy is used by the caller via
`above_or_below`.  (Helper: a point of `C` is not on the chord itself.) -/
lemma flatComponent_nonempty (f : ℝ² → ℝ³) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) :
    (flatComponent f p).Nonempty := ⟨p, mem_flatComponent hp⟩



/-- The open strip `{0 < x0 < 1}` is connected: it is the image of the
connected product `(0,1) × ℝ` under `(u,v) ↦ !₂[u,v]`. -/
lemma isPreconnected_stripInterior : IsPreconnected stripInterior := by
  have hD : IsPreconnected ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.univ : Set ℝ)) :=
    IsPreconnected.prod isPreconnected_Ioo PreconnectedSpace.isPreconnected_univ
  have hF : ContinuousOn (fun p : ℝ × ℝ => !₂[p.1, p.2])
      ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.univ : Set ℝ)) := by
    intro p hp
    fun_prop
  have himg : IsPreconnected
      ((fun p : ℝ × ℝ => !₂[p.1, p.2]) '' ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.univ : Set ℝ))) :=
    IsPreconnected.image hD (fun p : ℝ × ℝ => !₂[p.1, p.2]) hF
  have hEq : stripInterior =
      (fun p : ℝ × ℝ => !₂[p.1, p.2]) '' ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.univ : Set ℝ)) := by
    ext x
    constructor
    · intro hx
      rw [stripInterior] at hx
      rw [Set.mem_image]
      refine ⟨(x 0, x 1), ?_, ?_⟩
      · rw [Set.mem_prod]
        constructor
        · exact hx
        · trivial
      · ext i <;> fin_cases i <;> simp
    · intro hx
      rcases hx with ⟨p, hp, hxeq⟩
      rw [Set.mem_prod] at hp
      rw [stripInterior]
      rw [← hxeq]
      exact hp.1
  simpa [hEq] using himg

/-- The frontier of a flat component inside the open strip is nonempty
(otherwise the component would be all of the strip and unbounded). -/
theorem frontierStrip_nonempty {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    (frontier (flatComponent f p) ∩ stripInterior).Nonempty := by
  by_contra h
  have hfe : frontier (flatComponent f p) ∩ stripInterior = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim (h ⟨x, hx⟩)
    · intro hx
      exact False.elim hx
  have hfrW : frW f p = stripInterior := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      rw [mem_frW_iff]
      constructor
      · exact hx
      · intro hxF
        have hmem : x ∈ frontier (flatComponent f p) ∩ stripInterior := ⟨hxF, hx⟩
        rw [hfe] at hmem
        exact hmem
  have hcomp : flatComponent f p = connectedComponentIn stripInterior p := by
    rw [← hfrW]
    exact flatComponent_eq_connectedComponentIn_frW (mem_flatComponent hp)
  have hfull : connectedComponentIn stripInterior p = stripInterior := by
    apply le_antisymm
    · exact connectedComponentIn_subset stripInterior p
    · exact IsPreconnected.subset_connectedComponentIn (F := stripInterior)
        isPreconnected_stripInterior (flatComponent_subset_stripInterior f p (mem_flatComponent hp))
        (by intro x hx; exact hx)
  have hCstrip : flatComponent f p = stripInterior := by
    rw [hcomp, hfull]
  have hb : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ flatComponent f p, ‖z - p‖ ≤ R :=
    flatComponent_bounded hf ha (mem_flatComponent hp)
  rcases hb with ⟨R, hR0, hR⟩
  let z : ℝ² := !₂[1 / 2, p 1 + R + 1]
  have hzS : z ∈ stripInterior := by
    rw [stripInterior]
    constructor <;> simp [z] <;> norm_num
  have hzC : z ∈ flatComponent f p := by
    rw [hCstrip]
    exact hzS
  have hb' : ‖z - p‖ ≤ R := hR z hzC
  have hcoord : R + 1 ≤ ‖z - p‖ := by
    have hz1 : (z - p) 1 = R + 1 := by simp [z]; ring
    have habs : |(z - p) 1| ≤ ‖z - p‖ := abs_coord1_le_norm (z - p)
    rw [hz1] at habs
    have hpos : 0 ≤ R + 1 := by linarith
    rwa [abs_of_nonneg hpos] at habs
  nlinarith

/-- The frontier slice is nonempty. -/
lemma frSlice_nonempty {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : (frSlice f p).Nonempty := by
  rcases frontierStrip_nonempty hf ha hp with ⟨e, he⟩
  rcases frComponent_slice_point hf ha hp he with ⟨z, hz, _⟩
  exact ⟨z, hz⟩

/-- The set of slice heights is nonempty. -/
lemma frHeights_nonempty {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : (frHeights f p).Nonempty := by
  rcases frSlice_nonempty hf ha hp with ⟨z, hz⟩
  refine ⟨z 1, ?_⟩
  rw [mem_frHeights_iff]
  exact ⟨z, hz, rfl⟩




/-- A slice height `h` whose component chord lies BELOW the flat
component `C`: `C` is entirely above that chord. -/
noncomputable def frBelow {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) : Set ℝ :=
  {h | h ∈ frHeights f p ∧ ∃ hh : h ∈ frHeights f p,
    flatComponent f p ⊆
      aboveChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2}

/-- A slice height `h` whose component chord lies ABOVE the flat
component `C`: `C` is entirely below that chord. -/
noncomputable def frAbove {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) : Set ℝ :=
  {h | h ∈ frHeights f p ∧ ∃ hh : h ∈ frHeights f p,
    flatComponent f p ⊆
      belowChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2}

/-- Membership in the below-set. -/
lemma mem_frBelow {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h : ℝ} :
    h ∈ frBelow hf ha p hp ↔ h ∈ frHeights f p ∧ ∃ hh : h ∈ frHeights f p,
      flatComponent f p ⊆ aboveChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 := by rfl

/-- Membership in the above-set. -/
lemma mem_frAbove {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h : ℝ} :
    h ∈ frAbove hf ha p hp ↔ h ∈ frHeights f p ∧ ∃ hh : h ∈ frHeights f p,
      flatComponent f p ⊆ belowChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 := by rfl

/-- The below-set is finite. -/
lemma finite_frBelow {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) : (frBelow hf ha p hp).Finite :=
  Set.Finite.subset (finite_frHeights hf ha hp) (by
    intro h hh
    exact (mem_frBelow hf ha p hp).mp hh |>.1)

/-- The above-set is finite. -/
lemma finite_frAbove {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) : (frAbove hf ha p hp).Finite :=
  Set.Finite.subset (finite_frHeights hf ha hp) (by
    intro h hh
    exact (mem_frAbove hf ha p hp).mp hh |>.1)

/-- Every slice height is in exactly one of the two side sets: it cannot
be in both (that would put `C` in the empty intersection of the two open
half-strips). -/
lemma frBelow_not_frAbove {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hhB : h ∈ frBelow hf ha p hp) : h ∉ frAbove hf ha p hp := by
  intro hhA
  rcases (mem_frBelow hf ha p hp).mp hhB with ⟨hH, hhB', hsubB⟩
  rcases (mem_frAbove hf ha p hp).mp hhA with ⟨_, hhA', hsubA⟩
  have hd : Disjoint (aboveChord (frCompData hf ha p hp h hhB').1 (frCompData hf ha p hp h hhB').2)
      (belowChord (frCompData hf ha p hp h hhB').1 (frCompData hf ha p hp h hhB').2) :=
    aboveChord_disjoint_belowChord _ _
  have hC : (flatComponent f p).Nonempty := flatComponent_nonempty f p hp
  rcases hC with ⟨x, hxC⟩
  have hxAB : x ∈ aboveChord (frCompData hf ha p hp h hhB').1 (frCompData hf ha p hp h hhB').2 := hsubB hxC
  have hxBA : x ∈ belowChord (frCompData hf ha p hp h hhB').1 (frCompData hf ha p hp h hhB').2 := hsubA hxC
  exact (Set.disjoint_left.mp hd hxAB) hxBA

/-- **Side partition**: every slice height is below `C` or above `C`. -/
theorem frBelow_or_frAbove {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hh : h ∈ frHeights f p) : h ∈ frBelow hf ha p hp ∨ h ∈ frAbove hf ha p hp := by
  rcases flatComponent_above_or_below hf ha hp hh with hA | hB
  · left
    rw [mem_frBelow hf ha p hp]
    exact ⟨hh, hh, hA⟩
  · right
    rw [mem_frAbove hf ha p hp]
    exact ⟨hh, hh, hB⟩



/-- A finite nonempty set of reals has a least element. -/
lemma exists_least_of_finite_nonempty {s : Set ℝ} (hfin : s.Finite) (hne : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b := by
  classical
  haveI : Finite {x : ℝ // x ∈ s} := Set.finite_coe_iff.mpr hfin
  letI : Fintype {x : ℝ // x ∈ s} := Fintype.ofFinite _
  have hun : (Finset.univ : Finset {x : ℝ // x ∈ s}).Nonempty := ⟨⟨Classical.choose hne, Classical.choose_spec hne⟩, Finset.mem_univ _⟩
  rcases Finset.exists_max_image (Finset.univ : Finset {x : ℝ // x ∈ s})
    (fun u : {x : ℝ // x ∈ s} => -u.1) hun with ⟨a, _ha, hamax⟩
  refine ⟨a.1, a.2, ?_⟩
  intro b hb
  have hamaxb := hamax ⟨b, hb⟩ (Finset.mem_univ _)
  linarith

/-- A finite nonempty set of reals has a greatest element. -/
lemma exists_greatest_of_finite_nonempty {s : Set ℝ} (hfin : s.Finite) (hne : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, b ≤ a := by
  classical
  haveI : Finite {x : ℝ // x ∈ s} := Set.finite_coe_iff.mpr hfin
  letI : Fintype {x : ℝ // x ∈ s} := Fintype.ofFinite _
  have hun : (Finset.univ : Finset {x : ℝ // x ∈ s}).Nonempty := ⟨⟨Classical.choose hne, Classical.choose_spec hne⟩, Finset.mem_univ _⟩
  rcases Finset.exists_max_image (Finset.univ : Finset {x : ℝ // x ∈ s})
    (fun u : {x : ℝ // x ∈ s} => u.1) hun with ⟨a, _ha, hamax⟩
  refine ⟨a.1, a.2, ?_⟩
  intro b hb
  exact hamax ⟨b, hb⟩ (Finset.mem_univ _)

/-- The component at a slice height meets `x0 = 1/2` at its own height:
`sideH₁ (data h) (1/2) = h`. -/
lemma sideH₁_data_half {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hh : h ∈ frHeights f p) :
    sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 (1 / 2) = h := by
  have hsp : frSlicePoint f p h ∈ frCompAt f p h := frCompAt_slice hf ha hp hh
  have hΓ : frSlicePoint f p h ∈ stripChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 := by
    rw [frCompData_spec hf ha p hp hh] at hsp
    exact hsp
  rw [mem_stripChord] at hΓ
  have h0 : (frSlicePoint f p h) 0 = 1 / 2 := by simp [frSlicePoint]
  have h1 : (frSlicePoint f p h) 1 = h := by simp [frSlicePoint]
  have hΓ1 : (frSlicePoint f p h) 1 = sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 ((frSlicePoint f p h) 0) := hΓ.2
  calc
    sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 (1 / 2)
        = sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 ((frSlicePoint f p h) 0) := by rw [h0]
    _ = (frSlicePoint f p h) 1 := hΓ1.symm
    _ = h := h1

/-- Distinct slice heights give disjoint component chords (the chord
sets are disjoint). -/
lemma frCompData_disjoint_of_heights {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hne : h₁ ≠ h₂) :
    Disjoint (stripChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2)
      (stripChord (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) := by
  have hcomp : frCompAt f p h₁ ≠ frCompAt f p h₂ := frCompAt_ne_of_ne hf ha hp hh₁ hh₂ hne
  rw [← frCompData_spec hf ha p hp hh₁, ← frCompData_spec hf ha p hp hh₂]
  exact frComponent_disjoint hcomp
    (mem_frontierStrip_of_frSlice (frSlicePoint_mem hh₁).1)
    (mem_frontierStrip_of_frSlice (frSlicePoint_mem hh₂).1)

/-- **Slice-order ⟹ pointwise order of the chord data**: if `h₁ < h₂`,
the chord at `h₁` is pointwise below the chord at `h₂` on all of
`(0,1)`. -/
lemma sideH₁_lt_of_heights {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 u <
      sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 u := by
  have hd : Disjoint (stripChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2)
      (stripChord (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) :=
    frCompData_disjoint_of_heights hf ha p hp hh₁ hh₂ (ne_of_lt hlt)
  have hord : sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2) <
      sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2) := by
    rw [sideH₁_data_half hf ha p hp hh₁, sideH₁_data_half hf ha p hp hh₂]
    exact hlt
  exact chord_order_of_ordered_point (α₁ := (frCompData hf ha p hp h₁ hh₁).1)
    (β₁ := (frCompData hf ha p hp h₁ hh₁).2)
    (α₂ := (frCompData hf ha p hp h₂ hh₂).1) (β₂ := (frCompData hf ha p hp h₂ hh₂).2)
    hd ⟨by norm_num, by norm_num⟩ hord



/-- The half-strip strictly below the chord at the LEAST slice height is
free of the frontier: every other slice chord lies pointwise at or above
it, so no chord meets the strict half-strip below it. -/
lemma belowChord_of_lowest_subset_frW {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₀ : ℝ}
    (hh₀ : h₀ ∈ frHeights f p) (hle : ∀ b : ℝ, b ∈ frHeights f p → h₀ ≤ b) :
    belowChord (frCompData hf ha p hp h₀ hh₀).1 (frCompData hf ha p hp h₀ hh₀).2 ⊆ frW f p := by
  intro y hyB
  rw [mem_belowChord] at hyB
  rw [mem_frW_iff]
  constructor
  · exact hyB.1
  · intro hyF
    have hy𝓕 : y ∈ frontier (flatComponent f p) ∩ stripInterior := ⟨hyF, hyB.1⟩
    rw [frSlice_union_components hf ha hp] at hy𝓕
    rw [Set.mem_iUnion₂] at hy𝓕
    rcases hy𝓕 with ⟨z, hzS, hyz⟩
    let h' : ℝ := z 1
    have hh' : h' ∈ frHeights f p := by
      rw [mem_frHeights_iff]
      exact ⟨z, hzS, rfl⟩
    have he𝓕 : z ∈ frontier (flatComponent f p) ∩ stripInterior := mem_frontierStrip_of_frSlice hzS
    have hzIn : z ∈ frComp f p z := mem_connectedComponentIn he𝓕
    have hEq : frComp f p z = frCompAt f p (z 1) := frComp_eq_frCompAt hf ha hp he𝓕 hzS hzIn
    have hyAt : y ∈ frCompAt f p h' := by
      rw [hEq] at hyz
      dsimp [h']
      exact hyz
    have hle' : h₀ ≤ h' := hle h' hh'
    rcases lt_or_eq_of_le hle' with h₀lt | h₀eq
    · have hltu : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
          sideH₁ (frCompData hf ha p hp h₀ hh₀).1 (frCompData hf ha p hp h₀ hh₀).2 u <
          sideH₁ (frCompData hf ha p hp h' hh').1 (frCompData hf ha p hp h' hh').2 u :=
        sideH₁_lt_of_heights hf ha p hp hh₀ hh' h₀lt
      have hyΓ : y ∈ stripChord (frCompData hf ha p hp h' hh').1 (frCompData hf ha p hp h' hh').2 := by
        rw [frCompData_spec hf ha p hp hh'] at hyAt
        exact hyAt
      rw [mem_stripChord] at hyΓ
      have hy0 : y 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        rw [Set.mem_Ioo]
        rw [stripInterior] at hyB
        exact ⟨hyB.1.1, hyB.1.2⟩
      linarith [hyB.2, hyΓ.2, hltu (y 0) hy0]
    · have hy₀At : y ∈ frCompAt f p h₀ := by
        rwa [h₀eq]
      have hy₀Γ : y ∈ stripChord (frCompData hf ha p hp h₀ hh₀).1 (frCompData hf ha p hp h₀ hh₀).2 := by
        rw [frCompData_spec hf ha p hp hh₀] at hy₀At
        exact hy₀At
      rw [mem_stripChord] at hy₀Γ
      linarith [hyB.2, hy₀Γ.2]

/-- The half-strip strictly above the chord at the GREATEST slice height
is free of the frontier (mirror of the above). -/
lemma aboveChord_of_highest_subset_frW {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {hₙ : ℝ}
    (hhₙ : hₙ ∈ frHeights f p) (hge : ∀ b : ℝ, b ∈ frHeights f p → b ≤ hₙ) :
    aboveChord (frCompData hf ha p hp hₙ hhₙ).1 (frCompData hf ha p hp hₙ hhₙ).2 ⊆ frW f p := by
  intro y hyA
  rw [mem_aboveChord] at hyA
  rw [mem_frW_iff]
  constructor
  · exact hyA.1
  · intro hyF
    have hy𝓕 : y ∈ frontier (flatComponent f p) ∩ stripInterior := ⟨hyF, hyA.1⟩
    rw [frSlice_union_components hf ha hp] at hy𝓕
    rw [Set.mem_iUnion₂] at hy𝓕
    rcases hy𝓕 with ⟨z, hzS, hyz⟩
    let h' : ℝ := z 1
    have hh' : h' ∈ frHeights f p := by
      rw [mem_frHeights_iff]
      exact ⟨z, hzS, rfl⟩
    have he𝓕 : z ∈ frontier (flatComponent f p) ∩ stripInterior := mem_frontierStrip_of_frSlice hzS
    have hzIn : z ∈ frComp f p z := mem_connectedComponentIn he𝓕
    have hEq : frComp f p z = frCompAt f p (z 1) := frComp_eq_frCompAt hf ha hp he𝓕 hzS hzIn
    have hyAt : y ∈ frCompAt f p h' := by
      rw [hEq] at hyz
      dsimp [h']
      exact hyz
    have hge' : h' ≤ hₙ := hge h' hh'
    rcases lt_or_eq_of_le hge' with h'lt | hₙeq
    · have hltu : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
          sideH₁ (frCompData hf ha p hp h' hh').1 (frCompData hf ha p hp h' hh').2 u <
          sideH₁ (frCompData hf ha p hp hₙ hhₙ).1 (frCompData hf ha p hp hₙ hhₙ).2 u :=
        sideH₁_lt_of_heights hf ha p hp hh' hhₙ h'lt
      have hyΓ : y ∈ stripChord (frCompData hf ha p hp h' hh').1 (frCompData hf ha p hp h' hh').2 := by
        rw [frCompData_spec hf ha p hp hh'] at hyAt
        exact hyAt
      rw [mem_stripChord] at hyΓ
      have hy0 : y 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        rw [Set.mem_Ioo]
        rw [stripInterior] at hyA
        exact ⟨hyA.1.1, hyA.1.2⟩
      linarith [hyA.2, hyΓ.2, hltu (y 0) hy0]
    · have hyₙAt : y ∈ frCompAt f p hₙ := by
        rwa [← hₙeq]
      have hyₙΓ : y ∈ stripChord (frCompData hf ha p hp hₙ hhₙ).1 (frCompData hf ha p hp hₙ hhₙ).2 := by
        rw [frCompData_spec hf ha p hp hhₙ] at hyₙAt
        exact hyₙAt
      rw [mem_stripChord] at hyₙΓ
      linarith [hyA.2, hyₙΓ.2]

/-- Unbounded half-strips: below a chord there are points arbitrarily far
below any reference point, so a set containing such a half-strip is not
bounded. -/
lemma not_bounded_of_contains_belowChord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {α β : ℝ}
    (hsub : belowChord α β ⊆ flatComponent f p) : False := by
  rcases flatComponent_bounded hf ha (mem_flatComponent hp) with ⟨R, hR0, hR⟩
  let y : ℝ := min (sideH₁ α β (1 / 2)) (p 1) - R - 2
  let z : ℝ² := !₂[1 / 2, y]
  have hzS : z ∈ stripInterior := by
    rw [stripInterior]
    constructor <;> simp [z] <;> norm_num
  have hzB : z ∈ belowChord α β := by
    rw [mem_belowChord]
    constructor
    · exact hzS
    · simp [z]
      have hle1 : y < sideH₁ α β (1 / 2) := by
        dsimp [y]
        have hmin : min (sideH₁ α β (1 / 2)) (p 1) ≤ sideH₁ α β (1 / 2) := min_le_left _ _
        linarith
      simpa using hle1
  have hzC : z ∈ flatComponent f p := hsub hzB
  have hb : ‖z - p‖ ≤ R := hR z hzC
  have hb' : R + 2 ≤ ‖z - p‖ := by
    have hz1 : (z - p) 1 = y - p 1 := by simp [z]
    have habs : |(z - p) 1| ≤ ‖z - p‖ := abs_coord1_le_norm (z - p)
    have hdist : R + 2 ≤ |(z - p) 1| := by
      rw [hz1]
      have hle2 : y ≤ p 1 - R - 2 := by
        dsimp [y]
        have hmin : min (sideH₁ α β (1 / 2)) (p 1) ≤ p 1 := min_le_right _ _
        linarith
      have hle3 : p 1 - y ≥ R + 2 := by linarith
      have hnonpos : y - p 1 ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      nlinarith
    exact le_trans hdist habs
  nlinarith

/-- The mirror unbounded statement for half-strips above a chord. -/
lemma not_bounded_of_contains_aboveChord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {α β : ℝ}
    (hsub : aboveChord α β ⊆ flatComponent f p) : False := by
  rcases flatComponent_bounded hf ha (mem_flatComponent hp) with ⟨R, hR0, hR⟩
  let y : ℝ := max (sideH₁ α β (1 / 2)) (p 1) + R + 2
  let z : ℝ² := !₂[1 / 2, y]
  have hzS : z ∈ stripInterior := by
    rw [stripInterior]
    constructor <;> simp [z] <;> norm_num
  have hzA : z ∈ aboveChord α β := by
    rw [mem_aboveChord]
    constructor
    · exact hzS
    · simp [z]
      have hgt : sideH₁ α β (1 / 2) < y := by
        dsimp [y]
        have hmax : sideH₁ α β (1 / 2) ≤ max (sideH₁ α β (1 / 2)) (p 1) := le_max_left _ _
        linarith
      simpa using hgt
  have hzC : z ∈ flatComponent f p := hsub hzA
  have hb : ‖z - p‖ ≤ R := hR z hzC
  have hb' : R + 2 ≤ ‖z - p‖ := by
    have hz1 : (z - p) 1 = y - p 1 := by simp [z]
    have habs : |(z - p) 1| ≤ ‖z - p‖ := abs_coord1_le_norm (z - p)
    have hdist : R + 2 ≤ |(z - p) 1| := by
      rw [hz1]
      have hge2 : p 1 ≤ y - R - 2 := by
        dsimp [y]
        have hmax : p 1 ≤ max (sideH₁ α β (1 / 2)) (p 1) := le_max_right _ _
        linarith
      have hge3 : y - p 1 ≥ R + 2 := by linarith
      have hypos : 0 ≤ y - p 1 := by linarith
      rw [abs_of_nonneg hypos]
      exact hge3
    exact le_trans hdist habs
  nlinarith

/-- **There is a slice height whose chord lies below `C`.** -/
theorem frBelow_nonempty {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) : (frBelow hf ha p hp).Nonempty := by
  rcases exists_least_of_finite_nonempty (finite_frHeights hf ha hp) (frHeights_nonempty hf ha hp)
    with ⟨h₀, hh₀, hle⟩
  refine ⟨h₀, ?_⟩
  rw [mem_frBelow hf ha p hp]
  refine ⟨hh₀, hh₀, ?_⟩
  rcases flatComponent_above_or_below hf ha hp hh₀ with hA | hB
  · exact hA
  · exfalso
    have hsubW : belowChord (frCompData hf ha p hp h₀ hh₀).1 (frCompData hf ha p hp h₀ hh₀).2
        ⊆ frW f p := belowChord_of_lowest_subset_frW hf ha p hp hh₀ hle
    have hpre : IsPreconnected (belowChord (frCompData hf ha p hp h₀ hh₀).1 (frCompData hf ha p hp h₀ hh₀).2) :=
      isPreconnected_belowChord _ _
    have hmeet : (belowChord (frCompData hf ha p hp h₀ hh₀).1 (frCompData hf ha p hp h₀ hh₀).2 ∩
        flatComponent f p).Nonempty := by
      rcases flatComponent_nonempty f p hp with ⟨x, hxC⟩
      exact ⟨x, hB hxC, hxC⟩
    have hsubC : belowChord (frCompData hf ha p hp h₀ hh₀).1 (frCompData hf ha p hp h₀ hh₀).2 ⊆
        flatComponent f p := preconnected_frW_subset_C hsubW hpre hmeet
    exact not_bounded_of_contains_belowChord hf ha p hp hsubC

/-- **There is a slice height whose chord lies above `C`.** -/
theorem frAbove_nonempty {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) : (frAbove hf ha p hp).Nonempty := by
  rcases exists_greatest_of_finite_nonempty (finite_frHeights hf ha hp) (frHeights_nonempty hf ha hp)
    with ⟨hₙ, hhₙ, hge⟩
  refine ⟨hₙ, ?_⟩
  rw [mem_frAbove hf ha p hp]
  refine ⟨hhₙ, hhₙ, ?_⟩
  rcases flatComponent_above_or_below hf ha hp hhₙ with hA | hB
  · -- C above the highest chord: aboveChord(hₙ) ⊆ frW and meets C, forcing C unbounded above
    exfalso
    have hsubW : aboveChord (frCompData hf ha p hp hₙ hhₙ).1 (frCompData hf ha p hp hₙ hhₙ).2
        ⊆ frW f p := aboveChord_of_highest_subset_frW hf ha p hp hhₙ hge
    have hpre : IsPreconnected (aboveChord (frCompData hf ha p hp hₙ hhₙ).1 (frCompData hf ha p hp hₙ hhₙ).2) :=
      isPreconnected_aboveChord _ _
    have hmeet : (aboveChord (frCompData hf ha p hp hₙ hhₙ).1 (frCompData hf ha p hp hₙ hhₙ).2 ∩
        flatComponent f p).Nonempty := by
      rcases flatComponent_nonempty f p hp with ⟨x, hxC⟩
      exact ⟨x, hA hxC, hxC⟩
    have hsubC : aboveChord (frCompData hf ha p hp hₙ hhₙ).1 (frCompData hf ha p hp hₙ hhₙ).2 ⊆
        flatComponent f p := preconnected_frW_subset_C hsubW hpre hmeet
    exact not_bounded_of_contains_aboveChord hf ha p hp hsubC
  · exact hB



/-- Downward closure of the below-set: a smaller slice height whose chord
is pointwise lower is also below `C`. -/
lemma frBelow_of_lt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h h' : ℝ}
    (hh' : h' ∈ frHeights f p) (hhB : h ∈ frBelow hf ha p hp) (hlt : h' < h) :
    h' ∈ frBelow hf ha p hp := by
  rcases (mem_frBelow hf ha p hp).mp hhB with ⟨_, hh, hsub⟩
  rw [mem_frBelow hf ha p hp]
  refine ⟨hh', hh', ?_⟩
  -- C ⊆ aboveChord(data h) ⊆ aboveChord(data h') since chord h' < chord h pointwise
  have hltu : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (frCompData hf ha p hp h' hh').1 (frCompData hf ha p hp h' hh').2 u <
      sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 u :=
    sideH₁_lt_of_heights hf ha p hp hh' hh hlt
  intro x hxC
  have hx : x ∈ aboveChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 := hsub hxC
  rw [mem_aboveChord] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have hx0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.mem_Ioo]
    rw [stripInterior] at hx
    exact ⟨hx.1.1, hx.1.2⟩
  linarith [hltu (x 0) hx0, hx.2]

/-- Upward closure of the above-set: a larger slice height whose chord is
pointwise higher is also above `C`. -/
lemma frAbove_of_gt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h h' : ℝ}
    (hh' : h' ∈ frHeights f p) (hhA : h ∈ frAbove hf ha p hp) (hgt : h < h') :
    h' ∈ frAbove hf ha p hp := by
  rcases (mem_frAbove hf ha p hp).mp hhA with ⟨_, hh, hsub⟩
  rw [mem_frAbove hf ha p hp]
  refine ⟨hh', hh', ?_⟩
  have hltu : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 u <
      sideH₁ (frCompData hf ha p hp h' hh').1 (frCompData hf ha p hp h' hh').2 u :=
    sideH₁_lt_of_heights hf ha p hp hh hh' hgt
  intro x hxC
  have hx : x ∈ belowChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 := hsub hxC
  rw [mem_belowChord] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have hx0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.mem_Ioo]
    rw [stripInterior] at hx
    exact ⟨hx.1.1, hx.1.2⟩
  linarith [hltu (x 0) hx0, hx.2]

/-- The pointwise height data of the between region lies in the half-strip
above the lower chord and below the upper chord (`C ⊆ between(K₁,K₂)`
when the lower height is below `C` and the upper height above `C`). -/
lemma flatComponent_subset_between {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {hl hu : ℝ}
    (hhl : hl ∈ frHeights f p) (hhu : hu ∈ frHeights f p)
    (hsubB : flatComponent f p ⊆ aboveChord (frCompData hf ha p hp hl hhl).1 (frCompData hf ha p hp hl hhl).2)
    (hsubA : flatComponent f p ⊆ belowChord (frCompData hf ha p hp hu hhu).1 (frCompData hf ha p hp hu hhu).2) :
    flatComponent f p ⊆ betweenChord (frCompData hf ha p hp hl hhl).1 (frCompData hf ha p hp hl hhl).2
      (frCompData hf ha p hp hu hhu).1 (frCompData hf ha p hp hu hhu).2 := by
  intro x hxC
  have hx1 : x ∈ aboveChord (frCompData hf ha p hp hl hhl).1 (frCompData hf ha p hp hl hhl).2 := hsubB hxC
  have hx2 : x ∈ belowChord (frCompData hf ha p hp hu hhu).1 (frCompData hf ha p hp hu hhu).2 := hsubA hxC
  rw [mem_aboveChord] at hx1
  rw [mem_belowChord] at hx2
  rw [mem_betweenChord]
  exact ⟨hx1.1, hx1.2, hx2.2⟩

/-- A slice height strictly between the greatest below-height and the
least above-height cannot exist. -/
lemma no_frHeights_between {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {hl hu : ℝ}
    (hhB' : hl ∈ frBelow hf ha p hp) (hhA' : hu ∈ frAbove hf ha p hp)
    (hleB : ∀ b : ℝ, b ∈ frBelow hf ha p hp → b ≤ hl)
    (hgeA : ∀ b : ℝ, b ∈ frAbove hf ha p hp → hu ≤ b)
    {h : ℝ} (hhh : h ∈ frHeights f p) (h1 : hl < h) (h2 : h < hu) : False := by
  rcases frBelow_or_frAbove hf ha p hp hhh with hhB | hhA
  · exact (not_lt_of_ge (hleB h hhB)) h1
  · exact (not_lt_of_ge (hgeA h hhA)) h2

/-- **Anchor: the flat component is the between-region of two frontier
chords.**  Take `h₁` the greatest slice height below `C` and `h₂` the
least above `C`; the component is exactly the region between their
chords. -/
theorem flatComponent_between_frontier {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    ∃ h₁ h₂ : ℝ, h₁ ∈ frHeights f p ∧ h₂ ∈ frHeights f p ∧ h₁ < h₂ ∧
      ∃ hh₁ : h₁ ∈ frHeights f p, ∃ hh₂ : h₂ ∈ frHeights f p,
        flatComponent f p =
          betweenChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                       (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 := by
  classical
  rcases exists_greatest_of_finite_nonempty (finite_frBelow hf ha p hp) (frBelow_nonempty hf ha p hp)
    with ⟨h₁, hh₁B, hle₁⟩
  rcases exists_least_of_finite_nonempty (finite_frAbove hf ha p hp) (frAbove_nonempty hf ha p hp)
    with ⟨h₂, hh₂A, hge₂⟩
  rcases (mem_frBelow hf ha p hp).mp hh₁B with ⟨hh₁, hh₁', hsub₁⟩
  rcases (mem_frAbove hf ha p hp).mp hh₂A with ⟨hh₂, hh₂', hsub₂⟩
  have hlt : h₁ < h₂ := by
    by_contra hnot
    have hge : h₂ ≤ h₁ := le_of_not_gt hnot
    rcases lt_or_eq_of_le hge with hlt' | heq
    · have hh₂B : h₂ ∈ frBelow hf ha p hp := frBelow_of_lt hf ha p hp hh₂ hh₁B hlt'
      exact (frBelow_not_frAbove hf ha p hp hh₂B) hh₂A
    · have hh₁A : h₁ ∈ frAbove hf ha p hp := by
        rwa [heq] at hh₂A
      exact (frBelow_not_frAbove hf ha p hp hh₁B) hh₁A
  -- C ⊆ between(K₁,K₂)
  have hCsub : flatComponent f p ⊆ betweenChord
      (frCompData hf ha p hp h₁ hh₁').1 (frCompData hf ha p hp h₁ hh₁').2
      (frCompData hf ha p hp h₂ hh₂').1 (frCompData hf ha p hp h₂ hh₂').2 :=
    flatComponent_subset_between hf ha p hp hh₁' hh₂' hsub₁ hsub₂
  -- between(K₁,K₂) ⊆ frW: no slice chord meets the open between region
  have hBW : betweenChord (frCompData hf ha p hp h₁ hh₁').1 (frCompData hf ha p hp h₁ hh₁').2
        (frCompData hf ha p hp h₂ hh₂').1 (frCompData hf ha p hp h₂ hh₂').2 ⊆ frW f p := by
    intro y hyB
    rw [mem_betweenChord] at hyB
    rw [mem_frW_iff]
    constructor
    · exact hyB.1
    · intro hyF
      have hy𝓕 : y ∈ frontier (flatComponent f p) ∩ stripInterior := ⟨hyF, hyB.1⟩
      rw [frSlice_union_components hf ha hp] at hy𝓕
      rw [Set.mem_iUnion₂] at hy𝓕
      rcases hy𝓕 with ⟨z, hzS, hyz⟩
      let h : ℝ := z 1
      have hhh : h ∈ frHeights f p := by
        rw [mem_frHeights_iff]
        exact ⟨z, hzS, rfl⟩
      have he𝓕 : z ∈ frontier (flatComponent f p) ∩ stripInterior := mem_frontierStrip_of_frSlice hzS
      have hzIn : z ∈ frComp f p z := mem_connectedComponentIn he𝓕
      have hEq : frComp f p z = frCompAt f p (z 1) := frComp_eq_frCompAt hf ha hp he𝓕 hzS hzIn
      have hyAt : y ∈ frCompAt f p h := by
        rw [hEq] at hyz
        dsimp [h]
        exact hyz
      have hyΓ : y ∈ stripChord (frCompData hf ha p hp h hhh).1 (frCompData hf ha p hp h hhh).2 := by
        rw [frCompData_spec hf ha p hp hhh] at hyAt
        exact hyAt
      rw [mem_stripChord] at hyΓ
      have hy0 : y 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        rw [Set.mem_Ioo]
        rw [stripInterior] at hyB
        exact ⟨hyB.1.1, hyB.1.2⟩
      -- case analysis on h
      by_cases h1 : h < h₁
      · -- h < h₁: chord h pointwise below chord h₁
        have hltu : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
            sideH₁ (frCompData hf ha p hp h hhh).1 (frCompData hf ha p hp h hhh).2 u <
            sideH₁ (frCompData hf ha p hp h₁ hh₁').1 (frCompData hf ha p hp h₁ hh₁').2 u :=
          sideH₁_lt_of_heights hf ha p hp hhh hh₁' h1
        linarith [hyB.2.1, hyΓ.2, hltu (y 0) hy0]
      · have hge₁ : h₁ ≤ h := le_of_not_gt h1
        by_cases hEq₁ : h = h₁
        · -- h = h₁: y on the lower boundary chord
          have hy₁At : y ∈ frCompAt f p h₁ := by
            rw [hEq₁] at hyAt
            exact hyAt
          have hy₁Γ : y ∈ stripChord (frCompData hf ha p hp h₁ hh₁').1 (frCompData hf ha p hp h₁ hh₁').2 := by
            rw [frCompData_spec hf ha p hp hh₁'] at hy₁At
            exact hy₁At
          rw [mem_stripChord] at hy₁Γ
          linarith [hyB.2.1, hy₁Γ.2]
        · have hgt₁ : h₁ < h := lt_of_le_of_ne hge₁ (Ne.symm hEq₁)
          by_cases h2 : h < h₂
          · -- h₁ < h < h₂: impossible (no slice heights between the extremes)
            exact False.elim (no_frHeights_between hf ha p hp hh₁B hh₂A hle₁ hge₂ hhh hgt₁ h2)
          · have hge₂' : h₂ ≤ h := le_of_not_gt h2
            by_cases hEq₂ : h = h₂
            · -- h = h₂: y on the upper boundary chord
              have hy₂At : y ∈ frCompAt f p h₂ := by
                rw [hEq₂] at hyAt
                exact hyAt
              have hy₂Γ : y ∈ stripChord (frCompData hf ha p hp h₂ hh₂').1 (frCompData hf ha p hp h₂ hh₂').2 := by
                rw [frCompData_spec hf ha p hp hh₂'] at hy₂At
                exact hy₂At
              rw [mem_stripChord] at hy₂Γ
              linarith [hyB.2.2, hy₂Γ.2]
            · -- h > h₂: chord h pointwise above chord h₂
              have hgt₂ : h₂ < h := lt_of_le_of_ne hge₂' (Ne.symm hEq₂)
              have hltu : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
                  sideH₁ (frCompData hf ha p hp h₂ hh₂').1 (frCompData hf ha p hp h₂ hh₂').2 u <
                  sideH₁ (frCompData hf ha p hp h hhh).1 (frCompData hf ha p hp h hhh).2 u :=
                sideH₁_lt_of_heights hf ha p hp hh₂' hhh hgt₂
              linarith [hyB.2.2, hyΓ.2, hltu (y 0) hy0]
  -- between ⊆ C via connectedness
  have hpre : IsPreconnected (betweenChord
      (frCompData hf ha p hp h₁ hh₁').1 (frCompData hf ha p hp h₁ hh₁').2
      (frCompData hf ha p hp h₂ hh₂').1 (frCompData hf ha p hp h₂ hh₂').2) :=
    isPreconnected_betweenChord (sideH₁_lt_of_heights hf ha p hp hh₁' hh₂' hlt)
  have hmeet : (betweenChord
      (frCompData hf ha p hp h₁ hh₁').1 (frCompData hf ha p hp h₁ hh₁').2
      (frCompData hf ha p hp h₂ hh₂').1 (frCompData hf ha p hp h₂ hh₂').2 ∩
        flatComponent f p).Nonempty := by
    rcases flatComponent_nonempty f p hp with ⟨x, hxC⟩
    exact ⟨x, hCsub hxC, hxC⟩
  have hBsubC : betweenChord
      (frCompData hf ha p hp h₁ hh₁').1 (frCompData hf ha p hp h₁ hh₁').2
      (frCompData hf ha p hp h₂ hh₂').1 (frCompData hf ha p hp h₂ hh₂').2 ⊆
      flatComponent f p := preconnected_frW_subset_C hBW hpre hmeet
  refine ⟨h₁, h₂, hh₁, hh₂, hlt, hh₁', hh₂', ?_⟩
  apply le_antisymm
  · exact hCsub
  · exact hBsubC

