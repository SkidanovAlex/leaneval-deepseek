import Submission.Work.FlatBetweenFrontier
import Submission.Work.FlatFrontierFinite
import Submission.Work.ComponentSeparation
import Submission.Work.RegionBetween
import Submission.Work.FrontierDeck
import Submission.Work.LeafContinuity

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Shared-frontier uniqueness (T1-iii glue, step 1)

`flatComponents_no_common_stripInterior_closure` (ComponentSeparation)
says distinct flat components share NO closure point inside the open
strip.  Consequences used by the flat/U splice:

* **`frHeights_eq_extremes`** — a flat component whose canonical data are
  the chords at `h₁ < h₂` has exactly those two frontier centre heights:
  `frHeights f p = {h₁, h₂}` (Brick (A) applied to
  `C = betweenChord (data h₁) (data h₂)`; the slice points of `C` lie on
  the two bounding chords and their heights are `hᵢ`);
* **`frontier_centre_unique_component`** — at a frontier centreline point
  `(1/2, y₀)` at most ONE flat component is adjacent: if two flat
  components both have `(1/2, y₀)` in their frontier then they are the
  same component (contraposition of `flatComponents_no_common…`);
* **`frCompAt_of_component_eq` / `frHeights_of_component_eq` /
  `frCompData_of_equal_components`** — all frontier data depend only on
  the component as a set, not on the interior point `p` representing it:
  equal components give equal `frCompAt`/`frHeights`/`frCompData`
  (`stripChord_eq_iff`).

Together: the frontier chord at a frontier centre height is a
WELL-DEFINED object (unique adjacent component, unique chord data), and
the leaf value at that height computed from any representation agrees —
so the flat-side chord function glues across interval boundaries.

Build: `lake build Submission.Work.FlatNeighbour` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- **The frontier centre heights of a between-represented flat component
are exactly its two canonical heights**: if `C = flatComponent f p` is the
between-region of the chords at heights `h₁ < h₂`, then
`frHeights f p = {h₁, h₂}`. -/
theorem frHeights_eq_extremes {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) :
    frHeights f p = {x : ℝ | x = h₁ ∨ x = h₂} := by
  let d₁ : ℝ × ℝ := frCompData hf ha p hp h₁ hh₁
  let d₂ : ℝ × ℝ := frCompData hf ha p hp h₂ hh₂
  have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ d₁.1 d₁.2 u < sideH₁ d₂.1 d₂.2 u := by
    intro u hu
    simpa [d₁, d₂] using (sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt u hu)
  have hhalf₁ : sideH₁ d₁.1 d₁.2 (1 / 2) = h₁ := by
    simpa [d₁] using (sideH₁_data_half hf ha p hp hh₁)
  have hhalf₂ : sideH₁ d₂.1 d₂.2 (1 / 2) = h₂ := by
    simpa [d₂] using (sideH₁_data_half hf ha p hp hh₂)
  ext x
  constructor
  · intro hx
    rw [mem_frHeights_iff] at hx
    rcases hx with ⟨z, hzS, hz1⟩
    have hz0 : z 0 = 1 / 2 := (mem_frSlice_iff.mp hzS).2
    have hzF : z ∈ frontier (flatComponent f p) := (mem_frSlice_iff.mp hzS).1
    have hzS' : z ∈ stripInterior := by
      rw [stripInterior]
      change z 0 ∈ Set.Ioo (0 : ℝ) 1
      rw [hz0]
      constructor <;> norm_num
    have hzF' : z ∈ frontier (betweenChord d₁.1 d₁.2 d₂.1 d₂.2) := by
      rw [hC] at hzF
      exact hzF
    have hzch : z ∈ stripChord d₁.1 d₁.2 ∪ stripChord d₂.1 d₂.2 := by
      have hzA : z ∈ frontier (betweenChord d₁.1 d₁.2 d₂.1 d₂.2) ∩ stripInterior := ⟨hzF', hzS'⟩
      have hEq := frontier_betweenChord (α₁ := d₁.1) (β₁ := d₁.2) (α₂ := d₂.1) (β₂ := d₂.2) hord
      exact hEq ▸ hzA
    rw [Set.mem_union] at hzch
    rcases hzch with hz1ch | hz2ch
    · left
      have hz1' : z 1 = sideH₁ d₁.1 d₁.2 (z 0) := (mem_stripChord.mp hz1ch).2
      have hz1eq : z 1 = h₁ := by
        rw [hz1', hz0, hhalf₁]
      have : x = h₁ := by
        rw [hz1] at hz1eq
        exact hz1eq
      exact this
    · right
      have hz2' : z 1 = sideH₁ d₂.1 d₂.2 (z 0) := (mem_stripChord.mp hz2ch).2
      have hz2eq : z 1 = h₂ := by
        rw [hz2', hz0, hhalf₂]
      have : x = h₂ := by
        rw [hz1] at hz2eq
        exact hz2eq
      exact this
  · intro hx
    rcases hx with hx1 | hx2
    · rw [hx1]
      exact hh₁
    · rw [hx2]
      exact hh₂

/-- **At a frontier centreline point at most one flat component is
adjacent**: if two flat components both contain `(1/2, y₀)` in their
frontier, they are the same component. -/
theorem frontier_centre_unique_component {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₁ p₂ : ℝ²} (hp₁ : p₁ ∈ interior (FlatSet f))
    (hp₂ : p₂ ∈ interior (FlatSet f)) {y₀ : ℝ}
    (hq₁ : centrePoint y₀ ∈ frontier (flatComponent f p₁))
    (hq₂ : centrePoint y₀ ∈ frontier (flatComponent f p₂)) :
    flatComponent f p₁ = flatComponent f p₂ := by
  by_contra hne
  have hqS : centrePoint y₀ ∈ stripInterior := centrePoint_mem_stripInterior y₀
  have hcl₁ : centrePoint y₀ ∈ closure (flatComponent f p₁) :=
    frontier_subset_closure hq₁
  have hcl₂ : centrePoint y₀ ∈ closure (flatComponent f p₂) :=
    frontier_subset_closure hq₂
  have hne' : flatComponent f p₂ ≠ flatComponent f p₁ := by
    intro h
    exact hne h.symm
  exact flatComponents_no_common_stripInterior_closure hf ha hne' (centrePoint y₀) hqS ⟨hcl₁, hcl₂⟩

/-- `frCompAt` depends only on the component as a set. -/
lemma frCompAt_of_component_eq {f : ℝ² → ℝ³} {p₁ p₂ : ℝ²} {h : ℝ}
    (hcomp : flatComponent f p₁ = flatComponent f p₂) :
    frCompAt f p₁ h = frCompAt f p₂ h := by
  unfold frCompAt frComp
  rw [hcomp]
  simp [frSlicePoint]

/-- `frHeights` depends only on the component as a set. -/
lemma frHeights_of_component_eq {f : ℝ² → ℝ³} {p₁ p₂ : ℝ²}
    (hcomp : flatComponent f p₁ = flatComponent f p₂) :
    frHeights f p₁ = frHeights f p₂ := by
  unfold frHeights frSlice
  rw [hcomp]

/-- **The canonical chord data depend only on the component**, not on the
interior point `p` representing it: equal components give equal
`frCompData` at the same height. -/
theorem frCompData_of_equal_components {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₁ p₂ : ℝ²} (hp₁ : p₁ ∈ interior (FlatSet f))
    (hp₂ : p₂ ∈ interior (FlatSet f)) {h : ℝ}
    (hcomp : flatComponent f p₁ = flatComponent f p₂)
    (hh₁ : h ∈ frHeights f p₁) (hh₂ : h ∈ frHeights f p₂) :
    frCompData hf ha p₁ hp₁ h hh₁ = frCompData hf ha p₂ hp₂ h hh₂ := by
  have hspec₁ := frCompData_spec hf ha p₁ hp₁ hh₁
  have hspec₂ := frCompData_spec hf ha p₂ hp₂ hh₂
  have hAt : frCompAt f p₁ h = frCompAt f p₂ h := frCompAt_of_component_eq hcomp
  have hch : stripChord (frCompData hf ha p₁ hp₁ h hh₁).1 (frCompData hf ha p₁ hp₁ h hh₁).2 =
      stripChord (frCompData hf ha p₂ hp₂ h hh₂).1 (frCompData hf ha p₂ hp₂ h hh₂).2 := by
    rw [← hspec₁, ← hspec₂]
    exact hAt
  have hpair := (stripChord_eq_iff (α := (frCompData hf ha p₁ hp₁ h hh₁).1)
    (β := (frCompData hf ha p₁ hp₁ h hh₁).2)
    (α' := (frCompData hf ha p₂ hp₂ h hh₂).1)
    (β' := (frCompData hf ha p₂ hp₂ h hh₂).2)).mp hch
  apply Prod.ext
  · exact hpair.1
  · exact hpair.2

end Submission.PaperBand
