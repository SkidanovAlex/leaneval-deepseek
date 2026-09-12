import Submission.Work.DegenerateLeafValue
import Submission.Work.SpliceBendData
import Submission.Work.FoliationInterface
import Submission.Work.FlatGlue
import Submission.Work.FlatHeightFacts

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The total band splice: `chord : ℝ → BendData` (Prop main0)

WORK IN PROGRESS.  The final step before `BandFoliation a f hf` (whose
`lemmaT_tpattern` is PROVED) is to splice the leaf families into ONE
continuous, deck-invariant, pre-bend `chord : ℝ → BendData` over every
centreline height.  This file (BandSplice.lean) contains the layers of
that assembly.

**The four height regions (mutually exclusive and exhaustive):**
* U:    `y ∈ UHeight a f`;
* FI:   `IsFlatInterior f (centrePoint y)`;
* Cov:  `CoveredDegenerate a f y` (component FRONTIER heights);
* Unc:  `UncoveredDegenerate a f y` (the brick (B)/(D) region).

The value of `chord` at each height:
* U:   `uHeightBend hf ha ⟨y, hyU⟩`;
* FI:  the component leaf `flatCompBend` at `p := centrePoint y`;
* Cov: the frontier chord of that component at height `y`;
* Unc: `degenerateLeaf hf ha hy₀F hni hunc`.

LAYER 1 (GREEN): the case analysis `height_case` and exclusivity.
LAYER 1.5 (GREEN): deck invariance of every region.
LAYER 2 (GREEN): the total definition `spliceChord` by `height_case`
(`uHeightBend` on U; `flatInteriorLeaf` = the component leaf at
`centrePoint y` on flat-interior heights; `coveredLeaf` = the component
frontier leaf on covered-degenerate heights; `degenerateLeaf` on
uncovered-degenerate heights), plus the branch identities
`spliceChord_eq_uHeightBend` / `spliceChord_eq_flatInteriorLeaf`.
Layer 3 (continuity) STARTED — the endpoint-height functions
`spliceA1 hf ha y := (spliceChord y).A 1` and `spliceB1` are ContinuousOn
the U-heights and continuous at every U-height (`continuousOn/At_spliceA1/
B1_uHeight`, via `uHeightSplice`'s continuity + the branch identity on the
open U-region); Layer 4 (deck) is next.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **Covered degenerate (frontier) height**: flat (not a U-height), not
flat-interior, and a frontier height of some component. -/
def CoveredDegenerate {a : ℝ} {f : ℝ² → ℝ³} (y : ℝ) : Prop :=
  y ∉ UHeight a f ∧ ¬ IsFlatInterior f (centrePoint y) ∧
    CoveredHeight (f := f) y

/-- **Uncovered degenerate height**: flat (not a U-height), not
flat-interior, and not in the closed centre interval of any flat
component (the brick (B)/(D) region). -/
def UncoveredDegenerate {a : ℝ} {f : ℝ² → ℝ³} (y : ℝ) : Prop :=
  y ∉ UHeight a f ∧ ¬ IsFlatInterior f (centrePoint y) ∧
    ¬ CoveredHeight (f := f) y

/-- **Every height is in exactly one of the four regions**: `U`, flat-
interior, covered degenerate, or uncovered degenerate. -/
lemma height_case {a : ℝ} {f : ℝ² → ℝ³} (y : ℝ) :
    y ∈ UHeight a f ∨ IsFlatInterior f (centrePoint y) ∨
      CoveredDegenerate (a := a) (f := f) y ∨ UncoveredDegenerate (a := a) (f := f) y := by
  by_cases hyU : y ∈ UHeight a f
  · exact Or.inl hyU
  · by_cases hfi : IsFlatInterior f (centrePoint y)
    · exact Or.inr (Or.inl hfi)
    · by_cases hcov : CoveredHeight (f := f) y
      · exact Or.inr (Or.inr (Or.inl ⟨hyU, hfi, hcov⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hyU, hfi, hcov⟩))

/-- A U-height is not a flat-interior height (flat points have `dN = 0`). -/
lemma uHeight_not_flatInterior {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ}
    (hyU : y ∈ UHeight a f) : ¬ IsFlatInterior f (centrePoint y) := by
  rintro ⟨U, _hUo, hyc, hflat⟩
  have hd0 : dN f (centrePoint y) = 0 := hflat (centrePoint y) hyc
  exact ((mem_UHeight (a := a) (f := f)).mp hyU) hd0

/-- Flat-interior heights are not U-heights. -/
lemma flatInterior_not_uHeight {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ}
    (hfi : IsFlatInterior f (centrePoint y)) : y ∉ UHeight a f := by
  intro hyU
  exact uHeight_not_flatInterior hyU hfi

/-- A U-height is neither covered- nor uncovered-degenerate (both require
`y ∉ UHeight`). -/
lemma uHeight_not_degenerate {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ} (hyU : y ∈ UHeight a f) :
    ¬ CoveredDegenerate (a := a) (f := f) y ∧ ¬ UncoveredDegenerate (a := a) (f := f) y := by
  constructor <;> intro h <;> exact h.1 hyU

/-- Flat-interior heights are not degenerate. -/
lemma flatInterior_not_degenerate {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ}
    (hfi : IsFlatInterior f (centrePoint y)) :
    ¬ CoveredDegenerate (a := a) (f := f) y ∧ ¬ UncoveredDegenerate (a := a) (f := f) y := by
  constructor <;> intro h <;> exact h.2.1 hfi

/-- Covered- and uncovered-degenerate are disjoint (negation of the last
conjunct). -/
lemma covered_not_uncovered {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ}
    (hc : CoveredDegenerate (a := a) (f := f) y) :
    ¬ UncoveredDegenerate (a := a) (f := f) y := by
  intro hu
  exact hu.2.2 hc.2.2

/-! ## Layer 1.5 — deck invariance of the four regions -/

/-- Interior membership is invariant under the deck (both directions). -/
lemma mem_interior_FlatSet_period_iff {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} : period a p ∈ interior (FlatSet f) ↔ p ∈ interior (FlatSet f) := by
  constructor
  · intro hp
    have hpinv := mem_interior_FlatSet_periodInv hf hp
    simpa [periodInv_period] using hpinv
  · exact mem_interior_FlatSet_period hf

/-- `IsFlatInterior` is invariant under the deck (both directions), for
strip-interior points. -/
lemma IsFlatInterior_period_iff {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hxS : x ∈ stripInterior) :
    IsFlatInterior f (period a x) ↔ IsFlatInterior f x := by
  have hperS : period a x ∈ stripInterior := by
    rw [stripInterior]
    change (period a x) 0 ∈ Set.Ioo (0 : ℝ) 1
    rw [Set.mem_Ioo]
    constructor
    · have hx1 : x 0 < 1 := by rw [stripInterior] at hxS; exact hxS.2
      simp [period]; linarith
    · have hx0 : 0 < x 0 := by rw [stripInterior] at hxS; exact hxS.1
      simp [period]; linarith
  rw [IsFlatInterior_iff_mem_interior_FlatSet hperS, IsFlatInterior_iff_mem_interior_FlatSet hxS]
  exact mem_interior_FlatSet_period_iff hf

/-- The FLAT-INTERIOR region is deck-invariant at the level of centre
heights. -/
lemma flatInterior_height_add_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : IsFlatInterior f (centrePoint (y + a)) ↔ IsFlatInterior f (centrePoint y) := by
  rw [centrePoint_period a y]
  exact IsFlatInterior_period_iff hf (centrePoint_mem_stripInterior y)

/-- U-height membership flips negation under the deck. -/
lemma not_mem_UHeight_add_period_iff {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : y + a ∉ UHeight a f ↔ y ∉ UHeight a f := by
  constructor
  · intro h hu
    exact h ((mem_UHeight_add_period hf y).2 hu)
  · intro h hu
    exact h ((mem_UHeight_add_period hf y).1 hu)

/-- The COVERED-DEGENERATE region is deck-invariant. -/
lemma coveredDegenerate_add_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : CoveredDegenerate (a := a) (f := f) (y + a) ↔ CoveredDegenerate (a := a) (f := f) y := by
  constructor
  · intro h
    exact ⟨(by intro hyU; exact h.1 ((mem_UHeight_add_period hf y).2 hyU)),
      (by intro hIy; exact h.2.1 ((flatInterior_height_add_period hf y).2 hIy)),
      (CoveredHeight_period_iff hf y).1 h.2.2⟩
  · intro h
    exact ⟨(by intro hyU; exact h.1 ((mem_UHeight_add_period hf y).1 hyU)),
      (by intro hIy; exact h.2.1 ((flatInterior_height_add_period hf y).1 hIy)),
      (CoveredHeight_period_iff hf y).2 h.2.2⟩

/-- The UNCOVERED-DEGENERATE region is deck-invariant. -/
lemma uncoveredDegenerate_add_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : UncoveredDegenerate (a := a) (f := f) (y + a) ↔ UncoveredDegenerate (a := a) (f := f) y := by
  constructor
  · intro h
    exact ⟨(by intro hyU; exact h.1 ((mem_UHeight_add_period hf y).2 hyU)),
      (by intro hIy; exact h.2.1 ((flatInterior_height_add_period hf y).2 hIy)),
      (by intro hcy; exact h.2.2 ((CoveredHeight_period_iff hf y).2 hcy))⟩
  · intro h
    exact ⟨(by intro hyU; exact h.1 ((mem_UHeight_add_period hf y).1 hyU)),
      (by intro hIy; exact h.2.1 ((flatInterior_height_add_period hf y).1 hIy)),
      (by intro hcy; exact h.2.2 ((CoveredHeight_period_iff hf y).1 hcy))⟩

/-! ## Layer 2 — the spliced chord (GREEN: total definition) -/

noncomputable def bw₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : ℝ :=
  Classical.choose (flatComponent_between_with_data hf ha hp)

noncomputable def bw₂ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : ℝ :=
  Classical.choose (Classical.choose_spec (flatComponent_between_with_data hf ha hp))

noncomputable def bwhh₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    bw₁ hf ha hp ∈ frHeights f p :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (flatComponent_between_with_data hf ha hp)))

noncomputable def bwhh₂ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    bw₂ hf ha hp ∈ frHeights f p :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (flatComponent_between_with_data hf ha hp))))

noncomputable def compLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) (y : ℝ) : BendData :=
  flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)

noncomputable def flatInteriorLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hfi : IsFlatInterior f (centrePoint y)) : BendData :=
  compLeaf hf ha (p := centrePoint y)
    ((IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)).mp hfi) y

noncomputable def coveredLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hcov : CoveredHeight (f := f) y) : BendData :=
  compLeaf hf ha (p := Classical.choose hcov) (Classical.choose_spec hcov).1 y

noncomputable def uncoveredLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy₀F : y ∈ FlatHeight a f)
    (hni : ¬ IsFlatInterior f (centrePoint y)) (hunc : ¬ CoveredHeight (f := f) y) : BendData :=
  degenerateLeaf hf ha hy₀F hni hunc

noncomputable def spliceChord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) : BendData := by
  classical
  if hyU : y ∈ UHeight a f then
    exact uHeightBend hf ha ⟨y, hyU⟩
  else if hfi : IsFlatInterior f (centrePoint y) then
    exact flatInteriorLeaf hf ha hfi
  else if hcov : CoveredHeight (f := f) y then
    exact coveredLeaf hf ha hcov
  else
    have hy₀F : y ∈ FlatHeight a f := by
      rw [mem_FlatHeight]
      have hd : dN f (centrePoint y) = 0 := by
        by_contra hne
        exact hyU ((mem_UHeight (a := a) (f := f)).mpr hne)
      exact hd
    exact uncoveredLeaf hf ha hy₀F hfi hcov
lemma spliceChord_eq_uHeightBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∈ UHeight a f) :
    spliceChord hf ha y = uHeightBend hf ha ⟨y, hyU⟩ := by
  simp [spliceChord, hyU]

lemma spliceChord_eq_flatInteriorLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∉ UHeight a f)
    (hfi : IsFlatInterior f (centrePoint y)) :
    spliceChord hf ha y = flatInteriorLeaf hf ha hfi := by
  simp [spliceChord, hyU, hfi]




/-! ## Layer 3 — continuity of the endpoint heights at U-heights (GREEN) -/

/-- Left endpoint height of the spliced chord. -/
def spliceA1 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    (y : ℝ) : ℝ :=
  (spliceChord hf ha y).A 1

/-- Right endpoint height of the spliced chord. -/
def spliceB1 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    (y : ℝ) : ℝ :=
  (spliceChord hf ha y).B 1

/-- At a U-height the spliced left endpoint height equals the `uHeightBend`
value. -/
lemma spliceA1_eq_uHeightBend_A1 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∈ UHeight a f) :
    spliceA1 hf ha y = (uHeightBend hf ha ⟨y, hyU⟩).A 1 := by
  unfold spliceA1
  rw [spliceChord_eq_uHeightBend hf ha hyU]

/-- At a U-height the spliced right endpoint height equals the `uHeightBend`
value. -/
lemma spliceB1_eq_uHeightBend_B1 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∈ UHeight a f) :
    spliceB1 hf ha y = (uHeightBend hf ha ⟨y, hyU⟩).B 1 := by
  unfold spliceB1
  rw [spliceChord_eq_uHeightBend hf ha hyU]

/-- On the U-heights the spliced chord agrees with the `uHeightSplice` chord
(which is continuous there). -/
lemma spliceChord_eq_uHeightSplice_on_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∈ UHeight a f) :
    spliceChord hf ha y = (uHeightSplice hf ha).chord y := by
  rw [spliceChord_eq_uHeightBend hf ha hyU]
  simp [uHeightSplice, hyU]

/-- `spliceA1` is continuous on the (open) U-height region. -/
lemma continuousOn_spliceA1_uHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) : ContinuousOn (fun y : ℝ => spliceA1 hf ha y) (UHeight a f) := by
  have hc : ContinuousOn (fun y : ℝ => ((uHeightSplice hf ha).chord y).A 1) (UHeight a f) :=
    (uHeightSplice hf ha).contA1
  refine ContinuousOn.congr hc ?_
  intro y hy
  simp [spliceA1, spliceChord_eq_uHeightSplice_on_U hf ha hy]

/-- `spliceB1` is continuous on the (open) U-height region. -/
lemma continuousOn_spliceB1_uHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) : ContinuousOn (fun y : ℝ => spliceB1 hf ha y) (UHeight a f) := by
  have hc : ContinuousOn (fun y : ℝ => ((uHeightSplice hf ha).chord y).B 1) (UHeight a f) :=
    (uHeightSplice hf ha).contB1
  refine ContinuousOn.congr hc ?_
  intro y hy
  simp [spliceB1, spliceChord_eq_uHeightSplice_on_U hf ha hy]

/-- `spliceA1` is continuous at every U-height. -/
lemma continuousAt_spliceA1_uHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀ : y₀ ∈ UHeight a f) :
    ContinuousAt (fun y : ℝ => spliceA1 hf ha y) y₀ := by
  exact (continuousOn_spliceA1_uHeight hf ha).continuousAt ((isOpen_UHeight hf).mem_nhds hy₀)

/-- `spliceB1` is continuous at every U-height. -/
lemma continuousAt_spliceB1_uHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀ : y₀ ∈ UHeight a f) :
    ContinuousAt (fun y : ℝ => spliceB1 hf ha y) y₀ := by
  exact (continuousOn_spliceB1_uHeight hf ha).continuousAt ((isOpen_UHeight hf).mem_nhds hy₀)


end Submission
