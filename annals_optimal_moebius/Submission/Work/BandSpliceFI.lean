import Submission.Work.BandSplice

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Flat-interior consistency of the spliced chord (Layer 3, part 2)

The `spliceChord` FI-branch computes the component leaf through the
component of `centrePoint y`.  This file proves that this value depends
only on the COMPONENT (not on the representing point): for every height
`y` whose centreline point lies in the component `flatComponent f p`,
`spliceChord hf ha y = compLeaf hf ha hp y` (the canonical data of `p`).
Consequences: `spliceA1`/`spliceB1` are continuous on every component's
centre-height set and hence continuous at every flat-interior height.

* `bwlt`/`bwC` — the `<` and between-representation from the chosen data;
* `bw₁_of_component_eq`/`bw₂_of_component_eq` — equal components give
  equal chosen heights (`frHeights_eq_extremes` + the order);
* `frCompData_irrel` — `frCompData` is independent of its membership
  witness (proof irrelevance);
* `flatCompBend_of_component_eq` — the component leaf is a function of
  the component alone;
* `spliceChord_eq_compLeaf_of_centre_mem` — THE consistency lemma
  (`spliceChord`'s FI branch at `y` with `centrePoint y ∈ flatComponent
  f p` equals the canonical component leaf of `p`);
* `continuousOn_spliceA1_comp`/`_B` and `continuousAt_spliceA1_flatInterior`/
  `_B` — continuity of the endpoint heights on components / at
  flat-interior heights (via `flatCompBend_A_cont`/`B_cont`).

Build: `lake build Submission.Work.BandSpliceFI` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The chosen lower height is strictly below the chosen upper height. -/
noncomputable def bwlt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    bw₁ hf ha hp < bw₂ hf ha hp :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (flatComponent_between_with_data hf ha hp))))).1

/-- The between-representation of the component by the chosen data. -/
noncomputable def bwC {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    flatComponent f p = betweenChord
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (flatComponent_between_with_data hf ha hp))))).2

/-- `frHeights` of two equal components are equal. -/
lemma frHeights_of_component_eq {f : ℝ² → ℝ³} {p₁ p₂ : ℝ²}
    (hcomp : flatComponent f p₁ = flatComponent f p₂) :
    frHeights f p₁ = frHeights f p₂ := by
  unfold frHeights frSlice
  rw [hcomp]

/-- The chosen LOWER height depends only on the component. -/
lemma bw₁_of_component_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₁ p₂ : ℝ²} (hp₁ : p₁ ∈ interior (FlatSet f))
    (hp₂ : p₂ ∈ interior (FlatSet f))
    (hcomp : flatComponent f p₁ = flatComponent f p₂) :
    bw₁ hf ha hp₁ = bw₁ hf ha hp₂ := by
  have hext : frHeights f p₂ = {x : ℝ | x = bw₁ hf ha hp₂ ∨ x = bw₂ hf ha hp₂} :=
    frHeights_eq_extremes hf ha hp₂ (bwhh₁ hf ha hp₂) (bwhh₂ hf ha hp₂)
      (bwlt hf ha hp₂) (bwC hf ha hp₂)
  have hfr : frHeights f p₁ = frHeights f p₂ := frHeights_of_component_eq hcomp
  have hmem1 : bw₁ hf ha hp₁ ∈ {x : ℝ | x = bw₁ hf ha hp₂ ∨ x = bw₂ hf ha hp₂} := by
    have hm : bw₁ hf ha hp₁ ∈ frHeights f p₂ := by
      rw [← hfr]
      exact bwhh₁ hf ha hp₁
    rwa [hext] at hm
  have hmem2 : bw₂ hf ha hp₁ ∈ {x : ℝ | x = bw₁ hf ha hp₂ ∨ x = bw₂ hf ha hp₂} := by
    have hm : bw₂ hf ha hp₁ ∈ frHeights f p₂ := by
      rw [← hfr]
      exact bwhh₂ hf ha hp₁
    rwa [hext] at hm
  rcases hmem1 with haL | haR
  · exact haL
  · rcases hmem2 with hbL | hbR
    · exfalso
      have hlt₁ := bwlt hf ha hp₁
      have hlt₂ := bwlt hf ha hp₂
      linarith
    · exfalso
      have hlt₁ := bwlt hf ha hp₁
      linarith

/-- The chosen UPPER height depends only on the component. -/
lemma bw₂_of_component_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₁ p₂ : ℝ²} (hp₁ : p₁ ∈ interior (FlatSet f))
    (hp₂ : p₂ ∈ interior (FlatSet f))
    (hcomp : flatComponent f p₁ = flatComponent f p₂) :
    bw₂ hf ha hp₁ = bw₂ hf ha hp₂ := by
  have hb₁ := bw₁_of_component_eq hf ha hp₁ hp₂ hcomp
  have hext : frHeights f p₂ = {x : ℝ | x = bw₁ hf ha hp₂ ∨ x = bw₂ hf ha hp₂} :=
    frHeights_eq_extremes hf ha hp₂ (bwhh₁ hf ha hp₂) (bwhh₂ hf ha hp₂)
      (bwlt hf ha hp₂) (bwC hf ha hp₂)
  have hfr : frHeights f p₁ = frHeights f p₂ := frHeights_of_component_eq hcomp
  have hmem2 : bw₂ hf ha hp₁ ∈ {x : ℝ | x = bw₁ hf ha hp₂ ∨ x = bw₂ hf ha hp₂} := by
    have hm : bw₂ hf ha hp₁ ∈ frHeights f p₂ := by
      rw [← hfr]
      exact bwhh₂ hf ha hp₁
    rwa [hext] at hm
  rcases hmem2 with hbL | hbR
  · exfalso
    have hlt₁ := bwlt hf ha hp₁
    linarith
  · exact hbR

/-- `frCompData` is independent of the membership witness. -/
lemma frCompData_irrel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hh₁ hh₂ : h ∈ frHeights f p) :
    frCompData hf ha p hp h hh₁ = frCompData hf ha p hp h hh₂ := by
  exact congrArg (fun hh : h ∈ frHeights f p => frCompData hf ha p hp h hh)
    (Subsingleton.elim hh₁ hh₂)

/-- Same-component points have equal flat components. -/
lemma flatComponent_eq_of_mem {f : ℝ² → ℝ³} {p z : ℝ²}
    (hz : z ∈ flatComponent f p) : flatComponent f z = flatComponent f p := by
  unfold flatComponent
  exact (connectedComponentIn_eq (F := interior (FlatSet f)) (x := p) (y := z) hz).symm

lemma frCompData_congr_height {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (h : h₁ = h₂) (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) :
    frCompData hf ha p hp h₁ hh₁ = frCompData hf ha p hp h₂ hh₂ := by
  subst h
  exact frCompData_irrel hf ha p hp hh₁ hh₂

/-- The component leaf computed from two equal components is the same. -/
lemma flatCompBend_of_component_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₁ p₂ : ℝ²} (hp₁ : p₁ ∈ interior (FlatSet f))
    (hp₂ : p₂ ∈ interior (FlatSet f)) (y : ℝ)
    (hcomp : flatComponent f p₁ = flatComponent f p₂) :
    flatCompBend hf ha p₁ hp₁ (bw₁ hf ha hp₁) (bw₂ hf ha hp₁) y
        (bwhh₁ hf ha hp₁) (bwhh₂ hf ha hp₁) =
      flatCompBend hf ha p₂ hp₂ (bw₁ hf ha hp₂) (bw₂ hf ha hp₂) y
        (bwhh₁ hf ha hp₂) (bwhh₂ hf ha hp₂) := by
  have hb₁ := bw₁_of_component_eq hf ha hp₁ hp₂ hcomp
  have hb₂ := bw₂_of_component_eq hf ha hp₁ hp₂ hcomp
  unfold flatCompBend
  -- data transfer at the two chosen heights
  have hd₁ : frCompData hf ha p₁ hp₁ (bw₁ hf ha hp₁) (bwhh₁ hf ha hp₁) =
      frCompData hf ha p₂ hp₂ (bw₁ hf ha hp₂) (bwhh₁ hf ha hp₂) := by
    have hb₁₂ : bw₁ hf ha hp₁ ∈ frHeights f p₂ := by
      rw [hb₁]
      exact bwhh₁ hf ha hp₂
    have step₁ : frCompData hf ha p₁ hp₁ (bw₁ hf ha hp₁) (bwhh₁ hf ha hp₁) =
        frCompData hf ha p₂ hp₂ (bw₁ hf ha hp₁) hb₁₂ :=
      frCompData_of_equal_components hf ha hp₁ hp₂ (h := bw₁ hf ha hp₁) hcomp
        (bwhh₁ hf ha hp₁) hb₁₂
    exact step₁.trans (frCompData_congr_height hf ha p₂ hp₂ hb₁ hb₁₂ (bwhh₁ hf ha hp₂))
  have hd₂ : frCompData hf ha p₁ hp₁ (bw₂ hf ha hp₁) (bwhh₂ hf ha hp₁) =
      frCompData hf ha p₂ hp₂ (bw₂ hf ha hp₂) (bwhh₂ hf ha hp₂) := by
    have hb₂₁ : bw₂ hf ha hp₁ ∈ frHeights f p₂ := by
      rw [hb₂]
      exact bwhh₂ hf ha hp₂
    have step₁ : frCompData hf ha p₁ hp₁ (bw₂ hf ha hp₁) (bwhh₂ hf ha hp₁) =
        frCompData hf ha p₂ hp₂ (bw₂ hf ha hp₁) hb₂₁ :=
      frCompData_of_equal_components hf ha hp₁ hp₂ (h := bw₂ hf ha hp₁) hcomp
        (bwhh₂ hf ha hp₁) hb₂₁
    exact step₁.trans (frCompData_congr_height hf ha p₂ hp₂ hb₂ hb₂₁ (bwhh₂ hf ha hp₂))
  rw [hd₁, hd₂]

/-- **Consistency of the FI branch**: at every height `y` whose centreline
point lies in the component of `p`, the spliced chord equals the canonical
component leaf of `p`. -/
lemma spliceChord_eq_compLeaf_of_centre_mem {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) {y : ℝ}
    (hyC : centrePoint y ∈ flatComponent f p) :
    spliceChord hf ha y = compLeaf hf ha (p := p) hp y := by
  have hmem : centrePoint y ∈ interior (FlatSet f) :=
    flatComponent_subset_flatInterior f p hyC
  have hfi : IsFlatInterior f (centrePoint y) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)).mpr hmem
  have hneq : y ∉ UHeight a f := flatInterior_not_uHeight hfi
  rw [spliceChord_eq_flatInteriorLeaf hf ha hneq hfi]
  unfold flatInteriorLeaf compLeaf
  have hcomp : flatComponent f (centrePoint y) = flatComponent f p :=
    flatComponent_eq_of_mem (p := p) (z := centrePoint y) hyC
  exact flatCompBend_of_component_eq hf ha
    ((IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)).mp hfi)
    hp y hcomp

/-- The centreline map is continuous. -/
lemma continuous_centrePoint : Continuous (fun y : ℝ => centrePoint y) := by
  unfold centrePoint
  fun_prop

/-- The set of heights over a component's centre is open. -/
lemma isOpen_centreHeights {f : ℝ² → ℝ³} {p : ℝ²} :
    IsOpen {y : ℝ | centrePoint y ∈ flatComponent f p} := by
  have h : {y : ℝ | centrePoint y ∈ flatComponent f p} =
      (fun y : ℝ => centrePoint y) ⁻¹' flatComponent f p := rfl
  rw [h]
  exact (isOpen_flatComponent f p).preimage continuous_centrePoint

/-- `spliceA1` is continuous on the centre-height set of a component. -/
lemma continuousOn_spliceA1_comp {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    ContinuousOn (fun y : ℝ => spliceA1 hf ha y)
      {y : ℝ | centrePoint y ∈ flatComponent f p} := by
  have hA : Continuous (fun y : ℝ =>
      (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).A) :=
    flatCompBend_A_cont hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
  have hproj : Continuous (fun v : ℝ² => v 1) := by fun_prop
  refine ContinuousOn.congr (hproj.comp hA).continuousOn ?_
  intro y hy
  change spliceA1 hf ha y = (compLeaf hf ha (p := p) hp y).A 1
  rw [spliceA1]
  rw [spliceChord_eq_compLeaf_of_centre_mem hf ha (p := p) hp (y := y) hy]

/-- `spliceB1` is continuous on the centre-height set of a component. -/
lemma continuousOn_spliceB1_comp {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    ContinuousOn (fun y : ℝ => spliceB1 hf ha y)
      {y : ℝ | centrePoint y ∈ flatComponent f p} := by
  have hB : Continuous (fun y : ℝ =>
      (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).B) :=
    flatCompBend_B_cont hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
  have hproj : Continuous (fun v : ℝ² => v 1) := by fun_prop
  refine ContinuousOn.congr (hproj.comp hB).continuousOn ?_
  intro y hy
  change spliceB1 hf ha y = (compLeaf hf ha (p := p) hp y).B 1
  rw [spliceB1]
  rw [spliceChord_eq_compLeaf_of_centre_mem hf ha (p := p) hp (y := y) hy]

/-- `spliceA1` is continuous at every flat-interior height. -/
lemma continuousAt_spliceA1_flatInterior {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ}
    (hfi : IsFlatInterior f (centrePoint y₀)) :
    ContinuousAt (fun y : ℝ => spliceA1 hf ha y) y₀ := by
  let p : ℝ² := centrePoint y₀
  have hp : p ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y₀)).mp hfi
  have hmem₀ : y₀ ∈ {y : ℝ | centrePoint y ∈ flatComponent f p} := by
    dsimp [p]
    exact mem_flatComponent hp
  exact (continuousOn_spliceA1_comp hf ha (p := p) hp).continuousAt
    ((isOpen_centreHeights (f := f) (p := p)).mem_nhds hmem₀)

/-- `spliceB1` is continuous at every flat-interior height. -/
lemma continuousAt_spliceB1_flatInterior {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ}
    (hfi : IsFlatInterior f (centrePoint y₀)) :
    ContinuousAt (fun y : ℝ => spliceB1 hf ha y) y₀ := by
  let p : ℝ² := centrePoint y₀
  have hp : p ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y₀)).mp hfi
  have hmem₀ : y₀ ∈ {y : ℝ | centrePoint y ∈ flatComponent f p} := by
    dsimp [p]
    exact mem_flatComponent hp
  exact (continuousOn_spliceB1_comp hf ha (p := p) hp).continuousAt
    ((isOpen_centreHeights (f := f) (p := p)).mem_nhds hmem₀)

/-! ## Branch identities, centre and preBend of the spliced chord -/

/-- Branch identity at a covered-degenerate height. -/
lemma spliceChord_eq_coveredLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∉ UHeight a f)
    (hfi : ¬ IsFlatInterior f (centrePoint y)) (hcov : CoveredHeight (f := f) y) :
    spliceChord hf ha y = coveredLeaf hf ha hcov := by
  simp [spliceChord, hyU, hfi, hcov]

/-- Branch identity at an uncovered-degenerate height. -/
lemma spliceChord_eq_uncoveredLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy₀F : y ∈ FlatHeight a f)
    (hyU : y ∉ UHeight a f) (hfi : ¬ IsFlatInterior f (centrePoint y))
    (hunc : ¬ CoveredHeight (f := f) y) :
    spliceChord hf ha y = uncoveredLeaf hf ha hy₀F hfi hunc := by
  simp [spliceChord, uncoveredLeaf, hyU, hfi, hunc]

/-- Any frontier height of a component lies in the closed centre interval
of its chosen data. -/
lemma mem_Icc_of_mem_frHeights {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {y : ℝ}
    (hy : y ∈ frHeights f p) :
    y ∈ Set.Icc (bw₁ hf ha hp) (bw₂ hf ha hp) := by
  have hext : frHeights f p = {x : ℝ | x = bw₁ hf ha hp ∨ x = bw₂ hf ha hp} :=
    frHeights_eq_extremes hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
      (bwlt hf ha hp) (bwC hf ha hp)
  rw [hext] at hy
  rcases hy with hy₁ | hy₂
  · rw [hy₁]
    exact (Set.mem_Icc).2 ⟨le_rfl, le_of_lt (bwlt hf ha hp)⟩
  · rw [hy₂]
    exact (Set.mem_Icc).2 ⟨le_of_lt (bwlt hf ha hp), le_rfl⟩

/-- Every spliced leaf crosses the centreline at its own height. -/
theorem spliceChord_centre {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) : (spliceChord hf ha y).centreHeight = y := by
  rcases height_case (a := a) (f := f) y with hyU | hfi | hcov | hunc
  · rw [spliceChord_eq_uHeightBend hf ha hyU]
    exact uHeightBend_centre hf ha ⟨y, hyU⟩
  · rw [spliceChord_eq_flatInteriorLeaf hf ha (flatInterior_not_uHeight hfi) hfi]
    let hp : centrePoint y ∈ interior (FlatSet f) :=
      (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)).mp hfi
    change (flatCompBend hf ha (centrePoint y) hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).centreHeight = y
    exact flatCompBend_centre hf ha (centrePoint y) hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
      (bwlt hf ha hp)
  · rw [spliceChord_eq_coveredLeaf hf ha hcov.1 hcov.2.1 hcov.2.2]
    let p : ℝ² := Classical.choose hcov.2.2
    let hp : p ∈ interior (FlatSet f) := by
      dsimp [p]
      exact (Classical.choose_spec hcov.2.2).1
    change (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).centreHeight = y
    exact flatCompBend_centre hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
      (bwlt hf ha hp)
  · have hy₀F : y ∈ FlatHeight a f := by
      rw [mem_FlatHeight]
      by_contra hd
      exact hunc.1 ((mem_UHeight (a := a) (f := f)).mpr hd)
    rw [spliceChord_eq_uncoveredLeaf hf ha hy₀F hunc.1 hunc.2.1 hunc.2.2]
    change (degenerateLeaf hf ha hy₀F hunc.2.1 hunc.2.2).centreHeight = y
    exact degenerateLeaf_centre hf ha hy₀F hunc.2.1 hunc.2.2

/-- Every spliced leaf is a pre-bend of the embedded band. -/
theorem spliceChord_preBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) :
    ‖f ((spliceChord hf ha y).B) - f ((spliceChord hf ha y).A)‖ =
    ‖(spliceChord hf ha y).B - (spliceChord hf ha y).A‖ := by
  rcases height_case (a := a) (f := f) y with hyU | hfi | hcov | hunc
  · rw [spliceChord_eq_uHeightBend hf ha hyU]
    exact uHeightBend_preBend hf ha ⟨y, hyU⟩
  · rw [spliceChord_eq_flatInteriorLeaf hf ha (flatInterior_not_uHeight hfi) hfi]
    let hp : centrePoint y ∈ interior (FlatSet f) :=
      (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)).mp hfi
    have hyC : centrePoint y ∈ flatComponent f (centrePoint y) := mem_flatComponent hp
    have hyIoo : y ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp) :=
      (section_iff_of_between hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
        (bwlt hf ha hp) (bwC hf ha hp) y).mp hyC
    have hyIcc : y ∈ Set.Icc (bw₁ hf ha hp) (bw₂ hf ha hp) := by
      rw [Set.mem_Ioo] at hyIoo
      exact (Set.mem_Icc).2 ⟨le_of_lt hyIoo.1, le_of_lt hyIoo.2⟩
    change ‖f ((flatCompBend hf ha (centrePoint y) hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).B) -
        f ((flatCompBend hf ha (centrePoint y) hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).A)‖ =
      ‖(flatCompBend hf ha (centrePoint y) hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).B -
        (flatCompBend hf ha (centrePoint y) hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).A‖
    exact flatCompBend_preBend_closed hf ha (centrePoint y) hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
      (bwlt hf ha hp) (bwC hf ha hp) y hyIcc
  · rw [spliceChord_eq_coveredLeaf hf ha hcov.1 hcov.2.1 hcov.2.2]
    let p : ℝ² := Classical.choose hcov.2.2
    let hp : p ∈ interior (FlatSet f) := by
      dsimp [p]
      exact (Classical.choose_spec hcov.2.2).1
    have hyFr : y ∈ frHeights f p := by
      dsimp [p]
      exact (Classical.choose_spec hcov.2.2).2
    have hyIcc : y ∈ Set.Icc (bw₁ hf ha hp) (bw₂ hf ha hp) :=
      mem_Icc_of_mem_frHeights hf ha hp hyFr
    change ‖f ((flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).B) -
        f ((flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).A)‖ =
      ‖(flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).B -
        (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y
        (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).A‖
    exact flatCompBend_preBend_closed hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
      (bwlt hf ha hp) (bwC hf ha hp) y hyIcc
  · have hy₀F : y ∈ FlatHeight a f := by
      rw [mem_FlatHeight]
      by_contra hd
      exact hunc.1 ((mem_UHeight (a := a) (f := f)).mpr hd)
    rw [spliceChord_eq_uncoveredLeaf hf ha hy₀F hunc.1 hunc.2.1 hunc.2.2]
    change ‖f (degenerateLeaf hf ha hy₀F hunc.2.1 hunc.2.2).B -
        f (degenerateLeaf hf ha hy₀F hunc.2.1 hunc.2.2).A‖ =
      ‖(degenerateLeaf hf ha hy₀F hunc.2.1 hunc.2.2).B -
        (degenerateLeaf hf ha hy₀F hunc.2.1 hunc.2.2).A‖
    exact degenerateLeaf_preBend hf ha hy₀F hunc.2.1 hunc.2.2

end Submission
