import Submission.Work.BandSpliceFI
import Submission.Work.DegenerateLeafValue
import Submission.Work.FlatLeafBendData
import Submission.Work.FlatDeck
import Submission.Work.FrontierDeck
import Submission.Work.FlatNeighbour
import Submission.Work.CentrelineUBends

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Layer 4 — the deck of the spliced chord (GREEN target: zero sorry)

`spliceChord_deck : ∀ y, (spliceChord hf ha (y+a)).A = period a
((spliceChord hf ha y).B) ∧ (spliceChord hf ha (y+a)).B = period a
((spliceChord hf ha y).A)` — the `BandFoliation.deck` axiom — by
`height_case` split:

* U: `spliceChord_eq_uHeightBend` + `uHeightBend_deck` via `uHeightShift`;
* FI: `spliceChord_eq_flatInteriorLeaf` + `flatInteriorLeaf_deck`
  (from `compLeaf_deck` = `flatCompBend_deck` instantiated at the `bw`
  data; the centreline deck `centrePoint (y+a) = period a (centrePoint y)`
  connects the two component expressions via
  `flatCompBend_of_component_eq`);
* Cov: `spliceChord_eq_coveredLeaf` + `coveredLeaf_deck` (the deck image
  of the covering component via `frHeights_deck_mem`,
  `frontier_centre_unique_component`, `flatCompBend_of_component_eq`);
* Unc: `spliceChord_eq_uncoveredLeaf` + `degenerateLeaf_deck_A/B` with
  `flatHeight_add`/`not_flatInterior_add`/`not_covered_add`.

Then `Submission.BandFoliation` = { chord := spliceChord hf ha,
centre := spliceChord_centre, deck := spliceChord_deck,
cont_left := continuous_spliceA1 hf ha, cont_right := continuous_spliceB1
hf ha, preBend := spliceChord_preBend } (all ingredients GREEN).

Build: `lake build Submission.Work.SpliceDeck` (rc=0 target).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **Deck of the canonical component leaf**: the component leaf of the
deck-image component at `y + a` is the period image of the leaf of the
original component at `y`. -/
lemma compLeaf_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) (y : ℝ)
    (hp' : period a p ∈ interior (FlatSet f)) :
    (compLeaf hf ha (p := period a p) hp' (y + a)).A =
        period a (compLeaf hf ha (p := p) hp y).B ∧
    (compLeaf hf ha (p := period a p) hp' (y + a)).B =
        period a (compLeaf hf ha (p := p) hp y).A := by
  unfold compLeaf
  exact flatCompBend_deck hf ha p hp
    (hh₁ := bwhh₁ hf ha hp) (hh₂ := bwhh₂ hf ha hp) (hlt := bwlt hf ha hp)
    (hC := bwC hf ha hp) (hp' := hp')
    (hh₁' := bwhh₁ hf ha hp') (hh₂' := bwhh₂ hf ha hp') (hlt' := bwlt hf ha hp')

/-- **Deck of the flat-interior leaf**: the leaf at `y + a` is the period
image of the leaf at `y`. -/
lemma flatInteriorLeaf_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hfi : IsFlatInterior f (centrePoint y)) :
    (flatInteriorLeaf hf ha ((flatInterior_height_add_period hf y).2 hfi)).A =
        period a (flatInteriorLeaf hf ha hfi).B ∧
    (flatInteriorLeaf hf ha ((flatInterior_height_add_period hf y).2 hfi)).B =
        period a (flatInteriorLeaf hf ha hfi).A := by
  let p : ℝ² := centrePoint y
  have hp : p ∈ interior (FlatSet f) := by
    dsimp [p]
    exact (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)).mp hfi
  let hfi' : IsFlatInterior f (centrePoint (y + a)) := (flatInterior_height_add_period hf y).2 hfi
  have hcp : centrePoint (y + a) = period a p := by dsimp [p]; exact centrePoint_period a y
  have hp' : period a p ∈ interior (FlatSet f) := mem_interior_FlatSet_period hf hp
  have hdeck := compLeaf_deck hf ha hp y hp'
  have hL : flatInteriorLeaf hf ha hfi' = compLeaf hf ha (p := period a p) hp' (y + a) := by
    unfold flatInteriorLeaf
    apply flatCompBend_of_component_eq hf ha
      ((IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior (y + a))).mp hfi')
      hp' (y + a)
    rw [hcp]
  have hR : flatInteriorLeaf hf ha hfi = compLeaf hf ha (p := p) hp y := by
    unfold flatInteriorLeaf
    rfl
  constructor
  · have h1 := hdeck.1
    rwa [← hL, ← hR] at h1
  · have h2 := hdeck.2
    rwa [← hL, ← hR] at h2

/-- The centreline point over a frontier height lies in the frontier of
the component (from slice membership). -/
lemma centrePoint_mem_frontier_of_frHeights {f : ℝ² → ℝ³} {p : ℝ²} {h : ℝ}
    (hh : h ∈ frHeights f p) : centrePoint h ∈ frontier (flatComponent f p) := by
  exact (mem_frontierStrip_of_frSlice (frSlicePoint_mem hh).1).1

/-- **Deck of the covered leaf**: the covered leaf at `y + a` is the
period image of the covered leaf at `y`. -/
lemma coveredLeaf_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hcov : CoveredHeight (f := f) y) :
    (coveredLeaf hf ha ((CoveredHeight_period_iff hf y).2 hcov)).A =
        period a (coveredLeaf hf ha hcov).B ∧
    (coveredLeaf hf ha ((CoveredHeight_period_iff hf y).2 hcov)).B =
        period a (coveredLeaf hf ha hcov).A := by
  classical
  let p : ℝ² := Classical.choose hcov
  have hp : p ∈ interior (FlatSet f) := (Classical.choose_spec hcov).1
  have hh : y ∈ frHeights f p := (Classical.choose_spec hcov).2
  have hp' : period a p ∈ interior (FlatSet f) := mem_interior_FlatSet_period hf hp
  have hh' : y + a ∈ frHeights f (period a p) := (frHeights_deck_mem hf hp).mpr hh
  have hdeck := compLeaf_deck hf ha hp y hp'
  let hcov' : CoveredHeight (f := f) (y + a) := (CoveredHeight_period_iff hf y).2 hcov
  let p' : ℝ² := Classical.choose hcov'
  have hp'' : p' ∈ interior (FlatSet f) := (Classical.choose_spec hcov').1
  have hh'' : y + a ∈ frHeights f p' := (Classical.choose_spec hcov').2
  have hcomp : flatComponent f p' = flatComponent f (period a p) :=
    frontier_centre_unique_component hf ha hp'' hp'
      (centrePoint_mem_frontier_of_frHeights hh'')
      (centrePoint_mem_frontier_of_frHeights hh')
  have hL : coveredLeaf hf ha hcov' = compLeaf hf ha (p := period a p) hp' (y + a) := by
    unfold coveredLeaf
    -- compLeaf (p := p') hp'' (y+a) = compLeaf (p := period p) hp' (y+a)
    apply flatCompBend_of_component_eq hf ha hp'' hp' (y + a) hcomp
  have hR : coveredLeaf hf ha hcov = compLeaf hf ha (p := p) hp y := by
    unfold coveredLeaf
    rfl
  constructor
  · have h1 := hdeck.1
    rwa [← hL, ← hR] at h1
  · have h2 := hdeck.2
    rwa [← hL, ← hR] at h2

/-- **THE LAYER-4 DECK**: the spliced chord family satisfies the
`BandFoliation.deck` deck relation at every height. -/
theorem spliceChord_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) :
    (spliceChord hf ha (y + a)).A = period a (spliceChord hf ha y).B ∧
    (spliceChord hf ha (y + a)).B = period a (spliceChord hf ha y).A := by
  rcases height_case (a := a) (f := f) y with hyU | hfi | hcov | hunc
  · -- U branch
    have hyU' : y + a ∈ UHeight a f := (mem_UHeight_add_period hf y).2 hyU
    rw [spliceChord_eq_uHeightBend hf ha hyU, spliceChord_eq_uHeightBend hf ha hyU']
    have hshift : (⟨y + a, hyU'⟩ : UHeight a f) = uHeightShift hf ⟨y, hyU⟩ := by
      dsimp [uHeightShift]
    have hd := uHeightBend_deck hf ha ⟨y, hyU⟩
    simpa [hshift] using hd
  · -- FI branch
    have hfi' : IsFlatInterior f (centrePoint (y + a)) := (flatInterior_height_add_period hf y).2 hfi
    have hyU : y ∉ UHeight a f := flatInterior_not_uHeight hfi
    have hyU' : y + a ∉ UHeight a f := flatInterior_not_uHeight hfi'
    rw [spliceChord_eq_flatInteriorLeaf hf ha hyU hfi, spliceChord_eq_flatInteriorLeaf hf ha hyU' hfi']
    exact flatInteriorLeaf_deck hf ha hfi
  · -- Cov branch
    have hyU : y ∉ UHeight a f := hcov.1
    have hfi₀ : ¬ IsFlatInterior f (centrePoint y) := hcov.2.1
    rw [spliceChord_eq_coveredLeaf hf ha hyU hfi₀ hcov.2.2]
    have hyU' : y + a ∉ UHeight a f := (not_mem_UHeight_add_period_iff hf y).2 hyU
    have hfi₀' : ¬ IsFlatInterior f (centrePoint (y + a)) :=
      fun hA => hfi₀ ((flatInterior_height_add_period hf y).1 hA)
    rw [spliceChord_eq_coveredLeaf hf ha hyU' hfi₀' ((CoveredHeight_period_iff hf y).2 hcov.2.2)]
    exact coveredLeaf_deck hf ha hcov.2.2
  · -- Unc branch
    have hy₀F : y ∈ FlatHeight a f := by
      rw [mem_FlatHeight]
      have hd : dN f (centrePoint y) = 0 := by
        by_contra hne
        exact hunc.1 ((mem_UHeight (a := a) (f := f)).mpr hne)
      exact hd
    rw [spliceChord_eq_uncoveredLeaf hf ha hy₀F hunc.1 hunc.2.1 hunc.2.2]
    have hy₀F' : y + a ∈ FlatHeight a f := flatHeight_add hf hy₀F
    have hyU' : y + a ∉ UHeight a f := (not_mem_UHeight_add_period_iff hf y).2 hunc.1
    have hni' : ¬ IsFlatInterior f (centrePoint (y + a)) := not_flatInterior_add hf hunc.2.1
    have hunc' : ¬ CoveredHeight (f := f) (y + a) := not_covered_add hf hunc.2.2
    rw [spliceChord_eq_uncoveredLeaf hf ha hy₀F' hyU' hni' hunc']
    exact ⟨degenerateLeaf_deck_A hf ha hy₀F hunc.2.1 hunc.2.2,
      degenerateLeaf_deck_B hf ha hy₀F hunc.2.1 hunc.2.2⟩

end Submission
