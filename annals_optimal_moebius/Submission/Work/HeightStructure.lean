import Submission.Work.BandSpliceFI
import Submission.Work.ComponentSeparation

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Height-line structure: the four regions of the centreline (GREEN layer 1)

This file collects the purely structural facts about the centreline-height
line that the uniform slope-continuity layer (the degenerate-height
continuity of the spliced `BandFoliation` chord) needs.  All facts are
provable from the green frontier/component library without any
finiteness/isolation hypothesis (the F1-type accumulation of flat
components at a frontier chord is NOT excluded and must NOT be assumed
away; the uniform route of `session_status115` handles it).

Contents (namespace `Submission`):
* the covering-component API: `covPoint`/`covPoint_hp`/`covPoint_hh`;
* covered heights are flat and not flat-interior:
  `covered_mem_FlatHeight`, `covered_not_flatInterior`;
* the flat-interior heights form an OPEN set: `isOpen_flatInteriorHeights`;
* the centreline section of a component's centre interval:
  `mem_centreInterval_iff` (via the canonical `bw` data), and interior
  interval heights are flat-interior / neither U nor covered:
  `flatInterior_of_mem_centreInterval`,
  `mem_centreInterval_not_uHeight_not_covered`;
* a covered height lies at an END of its covering component's centre
  interval: `covered_eq_bw` (`c = bw₁ p ∨ c = bw₂ p`);
* **`flat_mem_of_tendsto_covered`** — the limit of converging covered
  heights is FLAT (`y₀ ∈ FlatHeight a f`); covered heights can never
  converge to a U-height or to the exterior of the flat set
  (`FlatHeight` is closed: `isClosed_FlatHeight`);
* degenerate trichotomy helpers: `uncovered_of_flat_not_fi_not_cov`,
  `coveredDegenerate_of_covered`.

IMPORTANT (mathematical caveat, see `session_status116`): covered heights
are NOT locally finite in general — flat components may ACCUMULATE at a
frontier chord (F1-type thin trapezoids); `flat_mem_of_tendsto_covered`
is the only convergence statement available and is the correct one.

Build: `lake build Submission.Work.HeightStructure` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-! ## 0. The covering component of a covered height -/

/-- The covering component basepoint of a covered height (a point of the
flat interior whose component has `y` as a frontier height). -/
noncomputable def covPoint {f : ℝ² → ℝ³} (y : ℝ) (hc : CoveredHeight (f := f) y) : ℝ² :=
  Classical.choose hc

/-- The covering point is in the flat interior. -/
lemma covPoint_hp {f : ℝ² → ℝ³} {y : ℝ} (hc : CoveredHeight (f := f) y) :
    covPoint y hc ∈ interior (FlatSet f) :=
  (Classical.choose_spec hc).1

/-- The covered height is a frontier height of the covering component. -/
lemma covPoint_hh {f : ℝ² → ℝ³} {y : ℝ} (hc : CoveredHeight (f := f) y) :
    y ∈ frHeights f (covPoint y hc) :=
  (Classical.choose_spec hc).2

/-! ## 1. Covered heights are flat, non-flat-interior -/

/-- A covered height is flat (`dN = 0` at its centreline point): the
frontier of the covering component lies in `FlatSet`. -/
lemma covered_mem_FlatHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {y : ℝ} (hc : CoveredHeight (f := f) y) : y ∈ FlatHeight a f := by
  rcases hc with ⟨p, hp, hh⟩
  have hzF : centrePoint y ∈ frontier (flatComponent f p) := by
    have hzF' := (frSlicePoint_mem (p := p) (h := y) hh).1
    have hzF'' : frSlicePoint f p y ∈ frontier (flatComponent f p) := (mem_frSlice_iff.mp hzF').1
    simpa [frSlicePoint, centrePoint] using hzF''
  exact (mem_FlatHeight_iff_FlatSet).mpr
    (flatComponent_frontier_subset_FlatSet hf (centrePoint_mem_stripInterior y) hzF)

/-- A covered height is not flat-interior: its centreline point is a
frontier point of the covering component. -/
lemma covered_not_flatInterior {f : ℝ² → ℝ³} {y : ℝ} (hc : CoveredHeight (f := f) y) :
    ¬ IsFlatInterior f (centrePoint y) := by
  rcases hc with ⟨p, hp, hh⟩
  have hzF : centrePoint y ∈ frontier (flatComponent f p) := by
    have hzF' := (frSlicePoint_mem (p := p) (h := y) hh).1
    have hzF'' : frSlicePoint f p y ∈ frontier (flatComponent f p) := (mem_frSlice_iff.mp hzF').1
    simpa [frSlicePoint, centrePoint] using hzF''
  exact flatComponent_frontier_not_flat_interior (centrePoint_mem_stripInterior y) hzF

/-! ## 2. The flat-interior heights are open -/

/-- The set of flat-INTERIOR heights is open (the centreline preimage of
the open flat interior). -/
lemma isOpen_flatInteriorHeights (f : ℝ² → ℝ³) :
    IsOpen {y : ℝ | IsFlatInterior f (centrePoint y)} := by
  have h : ({y : ℝ | IsFlatInterior f (centrePoint y)} : Set ℝ) =
      (fun y : ℝ => centrePoint y) ⁻¹' (interior (FlatSet f)) := by
    ext y
    exact IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)
  rw [h]
  exact (isOpen_interior).preimage continuous_centrePoint

/-! ## 3. The centreline section of a component's centre interval -/

/-- A centreline point lies in a flat component iff its height lies in
the component's canonical centre interval `(bw₁, bw₂)`. -/
lemma mem_centreInterval_iff {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) (y : ℝ) :
    centrePoint y ∈ flatComponent f p ↔ y ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp) := by
  exact section_iff_of_between hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
    (bwlt hf ha hp) (bwC hf ha hp) y

/-- The canonical `bw₁` height lies in the component's centre interval. -/
lemma bw₁_lt_of_bw₂ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    bw₁ hf ha hp < bw₂ hf ha hp :=
  bwlt hf ha hp

/-- A height in the centre interval is a flat-interior height (the
centreline point lies in the component, hence in the flat interior). -/
lemma flatInterior_of_mem_centreInterval {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {y : ℝ}
    (hy : y ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp)) :
    IsFlatInterior f (centrePoint y) := by
  have hyC : centrePoint y ∈ flatComponent f p := (mem_centreInterval_iff hf ha hp y).mpr hy
  have hyInt : centrePoint y ∈ interior (FlatSet f) := flatComponent_subset_flatInterior f p hyC
  exact (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)).mpr hyInt

/-- Interior heights of a component are neither U-heights nor covered. -/
lemma mem_centreInterval_not_uHeight_not_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f))
    {y : ℝ} (hy : y ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp)) :
    y ∉ UHeight a f ∧ ¬ CoveredHeight (f := f) y := by
  have hfi := flatInterior_of_mem_centreInterval hf ha hp hy
  constructor
  · intro hyU
    exact uHeight_not_flatInterior hyU hfi
  · intro hcov
    exact covered_not_flatInterior hcov hfi

/-! ## 4. Covered heights are the endpoints of their covering intervals -/

/-- A covered height equals one of the two canonical heights of its
covering component (the component of the `CoveredHeight` witness). -/
lemma covered_eq_bw {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hc : CoveredHeight (f := f) y) :
    y = bw₁ hf ha (covPoint_hp (y := y) hc) ∨ y = bw₂ hf ha (covPoint_hp (y := y) hc) := by
  have hh : y ∈ frHeights f (covPoint y hc) := covPoint_hh (y := y) hc
  let hp : covPoint y hc ∈ interior (FlatSet f) := covPoint_hp (y := y) hc
  have hext : frHeights f (covPoint y hc) = {x : ℝ | x = bw₁ hf ha hp ∨ x = bw₂ hf ha hp} :=
    frHeights_eq_extremes hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
      (bwlt hf ha hp) (bwC hf ha hp)
  rw [hext] at hh
  rcases hh with hh₁ | hh₂
  · left
    calc
      y = bw₁ hf ha hp := hh₁
      _ = bw₁ hf ha (covPoint_hp (y := y) hc) := by rfl
  · right
    calc
      y = bw₂ hf ha hp := hh₂
      _ = bw₂ hf ha (covPoint_hp (y := y) hc) := by rfl

/-! ## 5. Convergent covered heights have a flat limit -/

/-- The `FlatHeight` set is closed: the centreline map is continuous and
`dN f` is continuous. -/
lemma isClosed_FlatHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    IsClosed (FlatHeight a f) := by
  have hg : Continuous (fun y : ℝ => dN f (centrePoint y)) := by
    exact (ContDiffOn.continuousOn (contDiffOn_dN hf)).comp_continuous continuous_centrePoint
      (fun y => centrePoint_mem_stripInterior y)
  have h : (FlatHeight a f : Set ℝ) = {y : ℝ | dN f (centrePoint y) = 0} := by
    rfl
  rw [h]
  exact isClosed_eq hg continuous_const

/-- A convergent sequence of covered heights has a FLAT limit: covered
heights never converge to a U-height (nor to any non-flat point). -/
theorem flat_mem_of_tendsto_covered {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {y₀ : ℝ} {c : ℕ → ℝ} (hcov : ∀ n : ℕ, CoveredHeight (f := f) (c n))
    (hc : Tendsto c atTop (𝓝 y₀)) : y₀ ∈ FlatHeight a f := by
  have hS : ∀ n : ℕ, c n ∈ FlatHeight a f := fun n => covered_mem_FlatHeight hf (hcov n)
  have hclosed : IsClosed (FlatHeight a f) := isClosed_FlatHeight hf
  exact hclosed.mem_of_tendsto hc (Filter.Eventually.of_forall hS)

/-! ## 6. Degenerate trichotomy restated -/

/-- A flat height which is neither flat-interior nor covered is an
UNCOVERED degenerate height: it is not a U-height (flatness), not
flat-interior and not covered. -/
lemma uncovered_of_flat_not_fi_not_cov {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) {y : ℝ} (hyF : y ∈ FlatHeight a f)
    (hni : ¬ IsFlatInterior f (centrePoint y)) (hunc : ¬ CoveredHeight (f := f) y) :
    UncoveredDegenerate (a := a) (f := f) y := by
  have hyU : y ∉ UHeight a f := by
    intro hyU
    exact ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mp hyU) hyF
  exact ⟨hyU, hni, hunc⟩

/-- A covered degenerate height (frontier height) is flat non-interior. -/
lemma coveredDegenerate_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) {y : ℝ} (hyF : y ∈ FlatHeight a f)
    (hni : ¬ IsFlatInterior f (centrePoint y)) (hc : CoveredHeight (f := f) y) :
    CoveredDegenerate (a := a) (f := f) y := by
  have hyU : y ∉ UHeight a f := by
    intro hyU
    exact ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mp hyU) hyF
  exact ⟨hyU, hni, hc⟩

end Submission
