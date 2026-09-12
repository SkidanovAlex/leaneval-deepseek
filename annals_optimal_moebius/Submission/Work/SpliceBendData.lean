import Submission.Work.FlatGlue
import Submission.Work.FoliationInterface
import Submission.Work.CentrelineUBends
import Submission.Work.Main0Interface

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Domain-restricted per-height BendData (item (a) skeleton)

The total `chord : ℝ → BendData` for `BandFoliation` needs a value at
generic flat-frontier heights (the F1 decision, quarantined).  This file
lays down the honest DOMAIN-RESTRICTED object: a bend family on a height
set `D` with centre/preBend/continuity/deck, plus the instantiation at
one concrete identified frontier height (`h₂` of a flat component):

* `SpliceFoliation a f hf` — structure: `D : Set ℝ`, `chord : ℝ →
  BendData`, `centre`/`preBend` on `D`, `A1`/`B1` continuous on `D`
  (`ContinuousOn (fun y => (chord y).A 1) D` etc.), and `deck` for
  `y ∈ D` with `y + a ∈ D`;
* **`frontierHeight_leaf_valid`** — at the identified frontier height
  `h₂` of a component, the closed-interval family value
  `flatCompBend … h₂` (the frontier chord) is a genuine leaf: centre
  `= h₂` and preBend (instance of `flatCompBend_centre` /
  `flatCompBend_preBend_closed` at `y = h₂`);
* **`frontierHeight_A_eq_seam`** / **`frontierHeight_B_eq_seam`** — its
  endpoints ARE the frontier-chord seam points `(0, α₂)` / `(1, β₂)`
  (`flatCompBend_upper_A/B`), the common one-sided limit of the U and
  flat families (`frontier_glue_*_agree`).

Build: `lake build Submission.Work.SpliceBendData` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **Domain-restricted per-height bend family**: a `BendData`-valued
family on a set `D` of centreline heights, with centre and preBend at
every height of `D`, and the endpoint heights continuous on `D`.  (The
deck pairing is NOT a field here: it pairs `y` with the DECK-IMAGE
component at `y+a`, so it belongs to the deck-invariant total assembly
where it is proved from `flatCompBend_deck`/`blendBend_deck`/B3.) -/
structure SpliceFoliation (a : ℝ) (f : ℝ² → ℝ³) (hf : IsMoebiusEmbedding a f) where
  D : Set ℝ
  chord : ℝ → BendData
  centre : ∀ y : ℝ, y ∈ D → (chord y).centreHeight = y
  preBend : ∀ y : ℝ, y ∈ D →
    ‖f ((chord y).B) - f ((chord y).A)‖ = ‖(chord y).B - (chord y).A‖
  contA1 : ContinuousOn (fun y : ℝ => (chord y).A 1) D
  contB1 : ContinuousOn (fun y : ℝ => (chord y).B 1) D

/-- **The frontier chord is a genuine leaf at the identified frontier
height**: at `y = h₂` (upper frontier height of a component) the
closed-interval family value has centre `h₂` and is a pre-bend. -/
theorem frontierHeight_leaf_valid {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) :
    (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).centreHeight = h₂ ∧
    ‖f ((flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).B) -
        f ((flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).A)‖ =
      ‖(flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).B -
          (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).A‖ := by
  constructor
  · exact flatCompBend_centre hf ha p hp hh₁ hh₂ hlt
  · have hycc : h₂ ∈ Set.Icc h₁ h₂ := (Set.mem_Icc).2 ⟨le_of_lt hlt, le_rfl⟩
    exact flatCompBend_preBend_closed hf ha p hp hh₁ hh₂ hlt hC h₂ hycc

/-- **The frontier leaf's left endpoint is the chord seam point**
`(0, α₂)` — the common limit of the U and flat families. -/
theorem frontierHeight_A_eq_seam {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).A =
      !₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1] := by
  exact flatCompBend_upper_A hf ha p hp hh₁ hh₂ hlt

/-- **The frontier leaf's right endpoint is the chord seam point**
`(1, β₂)`. -/
theorem frontierHeight_B_eq_seam {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).B =
      !₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2] := by
  exact flatCompBend_upper_B hf ha p hp hh₁ hh₂ hlt



/-- **First case — a flat component's closed centre interval**: with the
canonical data (`hh₁,hh₂,hlt,hC`) the `flatCompBend` family over
`Icc h₁ h₂` is a `SpliceFoliation` (centre and preBend everywhere on the
interval, endpoint heights continuous — from
`flatCompBend_centre`, `flatCompBend_preBend_closed`,
`flatCompBend_A_cont/B_cont`).  At the boundary heights the leaves are
the frontier chords (`frontierHeight_leaf_valid`). -/
noncomputable def flatComponentSplice {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) :
    SpliceFoliation a f hf where
  D := Set.Icc h₁ h₂
  chord := fun y : ℝ => flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂
  centre := by
    intro y hy
    exact flatCompBend_centre hf ha p hp hh₁ hh₂ hlt
  preBend := by
    intro y hy
    exact flatCompBend_preBend_closed hf ha p hp hh₁ hh₂ hlt hC y hy
  contA1 := by
    have h : Continuous (fun y : ℝ => (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A) :=
      flatCompBend_A_cont hf ha p hp hh₁ hh₂
    have hproj : Continuous (fun v : ℝ² => v 1) := by fun_prop
    change ContinuousOn
      (fun y : ℝ => ((fun v : ℝ² => v 1) (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A))
      (Set.Icc h₁ h₂)
    exact (hproj.comp h).continuousOn
  contB1 := by
    have h : Continuous (fun y : ℝ => (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B) :=
      flatCompBend_B_cont hf ha p hp hh₁ hh₂
    have hproj : Continuous (fun v : ℝ² => v 1) := by fun_prop
    change ContinuousOn
      (fun y : ℝ => ((fun v : ℝ² => v 1) (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B))
      (Set.Icc h₁ h₂)
    exact (hproj.comp h).continuousOn
/-- **Second case — the `U`-heights**: with `D := UHeight a f` and the
canonical U-leaf family, `centre`/`preBend`/endpoint continuity come from
`uHeightBend_centre`/`uHeightBend_preBend`/`continuous_uHeightA/B`.  The
value outside `UHeight` is the horizontal default (never used on `D`). -/
noncomputable def uHeightSplice {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) : SpliceFoliation a f hf := by
  classical
  exact
    { D := UHeight a f
      chord := fun y : ℝ =>
        if h : y ∈ UHeight a f then uHeightBend hf ha ⟨y, h⟩ else horizBend y
      centre := by
        intro y hy
        simp [hy]
        exact uHeightBend_centre hf ha ⟨y, hy⟩
      preBend := by
        intro y hy
        simp [hy]
        exact uHeightBend_preBend hf ha ⟨y, hy⟩
      contA1 := by
        have hA : Continuous (fun y : UHeight a f => uHeightA hf ha y) :=
          continuous_uHeightA hf ha
        have hproj : Continuous (fun v : ℝ² => v 1) := by fun_prop
        have hclean : Continuous (fun y : UHeight a f => ((uHeightBend hf ha y).A 1)) := by
          change Continuous (fun y : UHeight a f => (uHeightA hf ha y) 1)
          exact hproj.comp hA
        rw [continuousOn_iff_continuous_domRestrict]
        change Continuous
          ((Set.domRestrict (UHeight a f))
            (fun y : ℝ =>
              (if h : y ∈ UHeight a f then uHeightBend hf ha ⟨y, h⟩ else horizBend y).A 1))
        have heq : (fun x : {y : ℝ // y ∈ UHeight a f} =>
            (if h : x.1 ∈ UHeight a f then uHeightBend hf ha ⟨x.1, h⟩ else horizBend x.1).A 1) =
            fun x : {y : ℝ // y ∈ UHeight a f} => ((uHeightBend hf ha ⟨x.1, x.property⟩).A 1) := by
          funext x
          simp [x.property]
        exact hclean.congr (fun x => (congrFun heq x).symm)
      contB1 := by
        have hB : Continuous (fun y : UHeight a f => uHeightB hf ha y) :=
          continuous_uHeightB hf ha
        have hproj : Continuous (fun v : ℝ² => v 1) := by fun_prop
        have hclean : Continuous (fun y : UHeight a f => ((uHeightBend hf ha y).B 1)) := by
          change Continuous (fun y : UHeight a f => (uHeightB hf ha y) 1)
          exact hproj.comp hB
        rw [continuousOn_iff_continuous_domRestrict]
        change Continuous
          ((Set.domRestrict (UHeight a f))
            (fun y : ℝ =>
              (if h : y ∈ UHeight a f then uHeightBend hf ha ⟨y, h⟩ else horizBend y).B 1))
        have heq : (fun x : {y : ℝ // y ∈ UHeight a f} =>
            (if h : x.1 ∈ UHeight a f then uHeightBend hf ha ⟨x.1, h⟩ else horizBend x.1).B 1) =
            fun x : {y : ℝ // y ∈ UHeight a f} => ((uHeightBend hf ha ⟨x.1, x.property⟩).B 1) := by
          funext x
          simp [x.property]
        exact hclean.congr (fun x => (congrFun heq x).symm) }
end Submission
