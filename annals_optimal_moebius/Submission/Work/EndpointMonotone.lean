import Submission.Work.BandSpliceFI
import Submission.Work.UFoliation

/-!
# PORT of the commons lemma `Commons.Geometry.Moebius.spliceChord_endpoint_monotone`

The commons file `Submission/Commons/Geometry/Moebius/spliceChord_endpoint_monotone.lean`
proves that the endpoint heights of the spliced chord family are monotone.  It
imports the commons COPY of this project (`Submission.Commons.OptimalMoebiusLib.*`),
which is unusable from inside the project (its `ChallengeDeps` copy clashes with the
project's).  This file is therefore a verbatim port of that (fully proven, zero
`sorry`) commons file with the imports redirected to the project modules, so that the
monotonicity is available to the project's Lemma-G endgame.

Original author: the fleet (shared commons), lemma `spliceChord_endpoint_monotone`.
-/
open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Commons.Geometry.Moebius

open Submission Submission.PaperBand

noncomputable section

variable {a : ℝ} {f : ℝ² → ℝ³}

/-! ## Notation for the spliced chord family -/

/-- The left endpoint height of the spliced chord at centreline height `y`. -/
def leafA1 (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) : ℝ :=
  (spliceChord hf ha y).A 1

/-- The right endpoint height of the spliced chord at centreline height `y`. -/
def leafB1 (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) : ℝ :=
  (spliceChord hf ha y).B 1

/-- The slope of the spliced chord at centreline height `y`. -/
def leafM (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) : ℝ :=
  (spliceChord hf ha y).slope

/-- The height of the spliced leaf at horizontal coordinate `x`. -/
def leafG (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y x : ℝ) : ℝ :=
  (1 - x) * leafA1 hf ha y + x * leafB1 hf ha y

/-- The point of the spliced leaf over horizontal coordinate `x`. -/
def leafPt (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y x : ℝ) : ℝ² :=
  (1 - x) • (spliceChord hf ha y).A + x • (spliceChord hf ha y).B

/-- The leaf chords at `y` and `z` cross inside the strip. -/
def Crosses (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y z : ℝ) : Prop :=
  ∃ x : ℝ, x ∈ Set.Ioo 0 1 ∧ leafG hf ha y x = leafG hf ha z x

/-- The centre condition: the spliced leaf through the centreline height `y`
meets the centreline at height `y`. -/
lemma leafA1_add_leafB1 (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) :
    leafA1 hf ha y + leafB1 hf ha y = 2 * y := by
  have h := spliceChord_centre hf ha y
  simp only [BendData.centreHeight] at h
  have h' : ((spliceChord hf ha y).A 1 + (spliceChord hf ha y).B 1) = 2 * y := by linarith
  simpa [leafA1, leafB1] using h'

lemma leafM_eq (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) :
    leafM hf ha y = leafB1 hf ha y - leafA1 hf ha y := rfl

lemma leafA1_eq (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) :
    leafA1 hf ha y = y - leafM hf ha y / 2 := by
  have h := leafA1_add_leafB1 hf ha y
  rw [leafM_eq]
  linarith

lemma leafB1_eq (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) :
    leafB1 hf ha y = y + leafM hf ha y / 2 := by
  have h := leafA1_add_leafB1 hf ha y
  rw [leafM_eq]
  linarith

lemma leafG_zero (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) :
    leafG hf ha y 0 = leafA1 hf ha y := by
  simp [leafG]

lemma leafG_one (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) :
    leafG hf ha y 1 = leafB1 hf ha y := by
  simp [leafG]

/-- The leaf is affine in the horizontal coordinate. -/
lemma leafG_affine (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y x : ℝ) :
    leafG hf ha y x = (1 - x) * leafG hf ha y 0 + x * leafG hf ha y 1 := by
  simp [leafG]

lemma leafG_centre (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y : ℝ) :
    leafG hf ha y (1 / 2) = y := by
  have h := leafA1_add_leafB1 hf ha y
  simp only [leafG]
  linarith

/-- The difference of two leaf heights is affine in `x`, with value `y - z`
at `x = 1/2`. -/
lemma leafG_sub (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y z x : ℝ) :
    leafG hf ha y x - leafG hf ha z x
      = (y - z) + (x - 1 / 2) * (leafM hf ha y - leafM hf ha z) := by
  rw [leafG, leafG, leafA1_eq hf ha y, leafB1_eq hf ha y, leafA1_eq hf ha z, leafB1_eq hf ha z]
  ring

lemma leafPt_coord0 (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y x : ℝ) :
    (leafPt hf ha y x) 0 = x := by
  simp only [leafPt]
  rw [show ((1 - x) • (spliceChord hf ha y).A + x • (spliceChord hf ha y).B) 0
        = (1 - x) * ((spliceChord hf ha y).A) 0 + x * ((spliceChord hf ha y).B) 0 by simp]
  rw [(spliceChord hf ha y).left_coord, (spliceChord hf ha y).right_coord]
  ring

lemma leafPt_coord1 (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y x : ℝ) :
    (leafPt hf ha y x) 1 = leafG hf ha y x := by
  simp only [leafPt, leafG, leafA1, leafB1]
  rw [show ((1 - x) • (spliceChord hf ha y).A + x • (spliceChord hf ha y).B) 1
        = (1 - x) * ((spliceChord hf ha y).A) 1 + x * ((spliceChord hf ha y).B) 1 by simp]


/-! ## Crossings and the Lipschitz inequality for the leaf slope -/

/-- Two leaf chords cross strictly inside the strip iff the centre heights are
closer than half the difference of the leaf slopes. -/
lemma crosses_iff (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z : ℝ} (hyz : y ≠ z) :
    Crosses hf ha y z ↔ 2 * |y - z| < |leafM hf ha y - leafM hf ha z| := by
  constructor
  · rintro ⟨x, hx, hEq⟩
    rcases Set.mem_Ioo.mp hx with ⟨hx0, hx1⟩
    have hsub := leafG_sub hf ha y z x
    rw [hEq, sub_self] at hsub
    have hM : leafM hf ha y - leafM hf ha z ≠ 0 := by
      intro h0
      rw [h0, mul_zero, add_zero] at hsub
      exact hyz (by linarith)
    have hval : y - z = -(x - 1 / 2) * (leafM hf ha y - leafM hf ha z) := by
      linarith
    have habs : |y - z| = |x - 1 / 2| * |leafM hf ha y - leafM hf ha z| := by
      rw [hval, abs_mul, abs_neg]
    have hxabs : |x - 1 / 2| < 1 / 2 := by
      rw [abs_lt]
      constructor <;> linarith
    rw [habs]
    have hpos : 0 < |leafM hf ha y - leafM hf ha z| := abs_pos.mpr hM
    nlinarith
  · intro hlt
    have hMpos : 0 < |leafM hf ha y - leafM hf ha z| := by
      have h1 : (0 : ℝ) ≤ |y - z| := abs_nonneg _
      linarith
    have hM : leafM hf ha y - leafM hf ha z ≠ 0 := abs_pos.mp hMpos
    refine ⟨1 / 2 - (y - z) / (leafM hf ha y - leafM hf ha z), ?_, ?_⟩
    · rw [Set.mem_Ioo]
      have hlt' : |y - z| / |leafM hf ha y - leafM hf ha z| < 1 / 2 := by
        rw [div_lt_iff₀ hMpos]
        linarith
      have hxabs : |(1 / 2 - (y - z) / (leafM hf ha y - leafM hf ha z)) - 1 / 2| < 1 / 2 := by
        have habs : |(1 / 2 - (y - z) / (leafM hf ha y - leafM hf ha z)) - 1 / 2|
            = |y - z| / |leafM hf ha y - leafM hf ha z| := by
          rw [show (1 / 2 - (y - z) / (leafM hf ha y - leafM hf ha z)) - 1 / 2
                = -((y - z) / (leafM hf ha y - leafM hf ha z)) by ring]
          rw [abs_neg, abs_div]
        rw [habs]
        exact hlt'
      rw [abs_lt] at hxabs
      constructor <;> linarith [hxabs.1, hxabs.2]
    · have hsub := leafG_sub hf ha y z (1 / 2 - (y - z) / (leafM hf ha y - leafM hf ha z))
      have hzero : leafG hf ha y (1 / 2 - (y - z) / (leafM hf ha y - leafM hf ha z))
          - leafG hf ha z (1 / 2 - (y - z) / (leafM hf ha y - leafM hf ha z)) = 0 := by
        rw [hsub]
        field_simp
        ring
      linarith

/-- If two leaf chords do not cross then the Lipschitz bound holds. -/
lemma two_mul_abs_le_of_not_crosses (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    {y z : ℝ} (hyz : y ≠ z) (h : ¬ Crosses hf ha y z) :
    2 * |y - z| ≥ |leafM hf ha y - leafM hf ha z| :=
  le_of_not_gt fun hcon => h ((crosses_iff hf ha hyz).mpr hcon)

/-! ## The `U`-leaf through a `U`-height is the canonical kernel segment -/

/-- The left endpoint of the spliced leaf at a `U`-height is the left
endpoint `uBendA` of the canonical kernel segment. -/
lemma uHeightBend_A_eq (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y : ℝ}
    (hyU : y ∈ UHeight a f) :
    (spliceChord hf ha y).A = centrePoint y
      + leftParam (centrePoint y) (uBendDirPos hf ha (centrePoint_mem_stripInterior y)
          ((mem_UHeight (a := a) (f := f)).mp hyU))
        • uBendDirPos hf ha (centrePoint_mem_stripInterior y)
          ((mem_UHeight (a := a) (f := f)).mp hyU) := by
  rw [spliceChord_eq_uHeightBend hf ha hyU]
  simp only [uHeightBend, uHeightA, uBendA]

/-- The right endpoint of the spliced leaf at a `U`-height is the right
endpoint `uBendB` of the canonical kernel segment. -/
lemma uHeightBend_B_eq (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y : ℝ}
    (hyU : y ∈ UHeight a f) :
    (spliceChord hf ha y).B = centrePoint y
      + rightParam (centrePoint y) (uBendDirPos hf ha (centrePoint_mem_stripInterior y)
          ((mem_UHeight (a := a) (f := f)).mp hyU))
        • uBendDirPos hf ha (centrePoint_mem_stripInterior y)
          ((mem_UHeight (a := a) (f := f)).mp hyU) := by
  rw [spliceChord_eq_uHeightBend hf ha hyU]
  simp only [uHeightBend, uHeightB, uBendB]

/-- The point of the spliced leaf at a `U`-height over the coordinate `x` lies
in the canonical kernel segment `uBendSet` through the centreline point. -/
lemma leafPt_mem_uBendSet (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y : ℝ}
    (hyU : y ∈ UHeight a f) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    leafPt hf ha y x ∈ uBendSet hf ha (centrePoint_mem_stripInterior y)
      ((mem_UHeight (a := a) (f := f)).mp hyU) := by
  set q : ℝ² := centrePoint y with hq
  set hdN : dN f q ≠ 0 := (mem_UHeight (a := a) (f := f)).mp hyU with hdNh
  set hqS : q ∈ stripInterior := centrePoint_mem_stripInterior y with hqSh
  set w : ℝ² := uBendDirPos hf ha hqS hdN with hw
  have hA : (spliceChord hf ha y).A = q + leftParam q w • w := by
    rw [uHeightBend_A_eq hf ha hyU]
  have hB : (spliceChord hf ha y).B = q + rightParam q w • w := by
    rw [uHeightBend_B_eq hf ha hyU]
  have hpt : leafPt hf ha y x = q + ((1 - x) * leftParam q w + x * rightParam q w) • w := by
    rw [leafPt, hA, hB]
    ext i <;> fin_cases i <;> simp <;> ring
  have hww : 0 < w 0 := (uBendDirPos_spec hf ha hqS hdN).2.2
  have hl : leftParam q w < 0 := (zero_between_params hf ha hqS hdN).1
  have hr : 0 < rightParam q w := (zero_between_params hf ha hqS hdN).2
  have hs : (1 - x) * leftParam q w + x * rightParam q w ∈ Set.Ioo (leftParam q w) (rightParam q w) := by
    rcases Set.mem_Ioo.mp hx with ⟨hx0, hx1⟩
    rw [Set.mem_Ioo]
    constructor
    · nlinarith
    · nlinarith
  rw [uBendSet_eq_param hf ha hqS hdN]
  exact ⟨(1 - x) * leftParam q w + x * rightParam q w, hs, hpt⟩


/-! ## The flat-interior leaves -/

/-- The canonical boundary data of a flat component. -/
def bwD1 (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) : ℝ × ℝ :=
  frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)

/-- The canonical upper boundary data of a flat component. -/
def bwD2 (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) : ℝ × ℝ :=
  frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)

lemma compLeaf_eq_blend (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (p : ℝ²)
    (hp : p ∈ interior (FlatSet f)) (y : ℝ) :
    compLeaf hf ha (p := p) hp y =
      blendBend (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 y := rfl

/-- The order of the two boundary chords of a flat component. -/
lemma bwD_order (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 u
      < sideH₁ (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 u := by
  intro u hu
  have h := sideH₁_lt_of_heights hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp) u hu
  simpa [bwD1, bwD2] using h

/-- The centre height of the leaf at a flat-interior height lies in the
component's centre interval. -/
lemma flatInterior_mem_interval (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {z : ℝ}
    (hfi : IsFlatInterior f (centrePoint z)) :
    z ∈ Set.Ioo (bw₁ hf ha ((IsFlatInterior_iff_mem_interior_FlatSet
      (centrePoint_mem_stripInterior z)).mp hfi))
      (bw₂ hf ha ((IsFlatInterior_iff_mem_interior_FlatSet
        (centrePoint_mem_stripInterior z)).mp hfi)) := by
  let hp : centrePoint z ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior z)).mp hfi
  have hzC : centrePoint z ∈ flatComponent f (centrePoint z) := mem_flatComponent hp
  have := (section_iff_of_between hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp)
    (bwC hf ha hp) z).mp hzC
  simpa [hp, centrePoint] using this

/-- The leaf through a flat-interior height agrees with the component leaf. -/
lemma spliceChord_eq_compLeaf_self (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {z : ℝ}
    (hfi : IsFlatInterior f (centrePoint z)) :
    spliceChord hf ha z = compLeaf hf ha (p := centrePoint z)
      ((IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior z)).mp hfi) z := by
  rw [spliceChord_eq_flatInteriorLeaf hf ha (flatInterior_not_uHeight hfi) hfi]
  rfl

/-- `genP` is affine in its segment parameter. -/
lemma genP_affine (α₁ β₁ α₂ β₂ t u : ℝ) :
    (1 - u) • genP α₁ β₁ α₂ β₂ t 0 + u • genP α₁ β₁ α₂ β₂ t 1 =
      genP α₁ β₁ α₂ β₂ t u := by
  ext i <;> fin_cases i <;> simp [genP, sideH₁, sideH₂] <;> ring

/-- The point of a flat-interior leaf over the coordinate `x`, in terms of the
component's blend family. -/
lemma leafPt_eq_blendP (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) {y : ℝ}
    (h : spliceChord hf ha y = compLeaf hf ha (p := p) hp y) (x : ℝ) :
    leafPt hf ha y x =
      blendP (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 y x := by
  rw [leafPt, h, compLeaf_eq_blend, blendBend_A_eq, blendBend_B_eq]
  simp only [genA, genB, blendP, blendT]
  rw [← genP_affine (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2
    (flatLeafT (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 y) x]

/-- The height of a flat-interior leaf over the coordinate `x`, in terms of the
component's blend family. -/
lemma leafG_eq_genP (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) {y : ℝ}
    (h : spliceChord hf ha y = compLeaf hf ha (p := p) hp y) (x : ℝ) :
    leafG hf ha y x =
      (1 - blendT (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 y)
          * sideH₁ (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 x
        + blendT (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 y
          * sideH₂ (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 x := by
  rw [leafG, leafA1, leafB1, h, compLeaf_eq_blend, blendBend_A_eq, blendBend_B_eq]
  rw [blendA1_formula', blendB1_formula', sideH₁, sideH₂]
  ring

/-- The blend point of a flat component at an interior centre height and
interior coordinate lies in the component. -/
lemma blendP_mem_component (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) {y u : ℝ}
    (hy : y ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp)) (hu : u ∈ Set.Ioo 0 1) :
    blendP (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 y u
      ∈ flatComponent f p := by
  have hord : ∀ u' : ℝ, u' ∈ Set.Ioo 0 1 →
      sideH₁ (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 u' <
        sideH₂ (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 u' := bwD_order hf ha hp
  have hy' : y ∈ Set.Ioo (sideH₁ (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (1 / 2))
      (sideH₂ (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 (1 / 2)) := by
    rw [Set.mem_Ioo] at hy ⊢
    rw [show sideH₁ (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (1 / 2) = bw₁ hf ha hp from
      sideH₁_data_half hf ha p hp (bwhh₁ hf ha hp)]
    rw [sideH₂_eq_sideH₁, show sideH₁ (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 (1 / 2) = bw₂ hf ha hp from
      sideH₁_data_half hf ha p hp (bwhh₂ hf ha hp)]
    exact hy
  have hmem := blend_inside (hord := hord) hy' hu
  have hmem' : blendP (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 y u ∈ flatComponent f p := by
    rw [bwC hf ha hp]
    exact hmem
  simpa [bwD1, bwD2] using hmem'

/-- **Flat-interior tag**: the leaf through a flat-interior height lies in its
flat component. -/
lemma leafPt_mem_flatComponent (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {z : ℝ}
    (hfi : IsFlatInterior f (centrePoint z)) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    leafPt hf ha z x ∈ flatComponent f (centrePoint z) := by
  let hp : centrePoint z ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior z)).mp hfi
  have hzI : z ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp) :=
    flatInterior_mem_interval hf ha hfi
  have hleaf : spliceChord hf ha z = compLeaf hf ha (p := centrePoint z) hp z :=
    spliceChord_eq_compLeaf_self hf ha hfi
  have hmem : blendP (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 z x
      ∈ flatComponent f (centrePoint z) := blendP_mem_component hf ha hp hzI hx
  rwa [← leafPt_eq_blendP hf ha hp hleaf x] at hmem


/-- A crossing in heights is a crossing in points. -/
lemma leafPt_eq_of_leafG_eq (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z x : ℝ}
    (h : leafG hf ha y x = leafG hf ha z x) :
    leafPt hf ha y x = leafPt hf ha z x := by
  ext i
  fin_cases i <;> simp [leafPt_coord0, leafPt_coord1, h]

/-- The canonical kernel-segment set at a `U`-height, expressed with the
positively oriented direction. -/
lemma uBendSet_eq_lineInteriorSet_pos (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y : ℝ}
    (hyU : y ∈ UHeight a f) :
    uBendSet hf ha (centrePoint_mem_stripInterior y) ((mem_UHeight (a := a) (f := f)).mp hyU)
      = lineInteriorSet (centrePoint y)
          (uBendDirPos hf ha (centrePoint_mem_stripInterior y)
            ((mem_UHeight (a := a) (f := f)).mp hyU)) := by
  unfold uBendSet
  have h1 := uBendDir_spec hf ha (centrePoint_mem_stripInterior y)
    ((mem_UHeight (a := a) (f := f)).mp hyU)
  have h2 := uBendDirPos_spec hf ha (centrePoint_mem_stripInterior y)
    ((mem_UHeight (a := a) (f := f)).mp hyU)
  exact ubend_unique_through_point hf (centrePoint_mem_stripInterior y)
    ((mem_UHeight (a := a) (f := f)).mp hyU) h1.1 h1.2.1 h1.2.2 h2.1 h2.2.1 (ne_of_gt h2.2.2)

/-- **Distinct `U`-leaves do not cross.** -/
lemma not_crosses_uHeight_uHeight (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z : ℝ}
    (hyU : y ∈ UHeight a f) (hzU : z ∈ UHeight a f) (hyz : y ≠ z) :
    ¬ Crosses hf ha y z := by
  rintro ⟨x, hx, hEq⟩
  have hpt : leafPt hf ha y x = leafPt hf ha z x := leafPt_eq_of_leafG_eq hf ha hEq
  have hwY := uBendDirPos_spec hf ha (centrePoint_mem_stripInterior y)
    ((mem_UHeight (a := a) (f := f)).mp hyU)
  have hwZ := uBendDirPos_spec hf ha (centrePoint_mem_stripInterior z)
    ((mem_UHeight (a := a) (f := f)).mp hzU)
  have hmemY : leafPt hf ha y x ∈ lineInteriorSet (centrePoint y)
      (uBendDirPos hf ha (centrePoint_mem_stripInterior y) ((mem_UHeight (a := a) (f := f)).mp hyU)) := by
    rw [← uBendSet_eq_lineInteriorSet_pos hf ha hyU]
    exact leafPt_mem_uBendSet hf ha hyU hx
  have hmemZ : leafPt hf ha z x ∈ lineInteriorSet (centrePoint z)
      (uBendDirPos hf ha (centrePoint_mem_stripInterior z) ((mem_UHeight (a := a) (f := f)).mp hzU)) := by
    rw [← uBendSet_eq_lineInteriorSet_pos hf ha hzU]
    exact leafPt_mem_uBendSet hf ha hzU hx
  have hmemZ' : leafPt hf ha y x ∈ lineInteriorSet (centrePoint z)
      (uBendDirPos hf ha (centrePoint_mem_stripInterior z) ((mem_UHeight (a := a) (f := f)).mp hzU)) := by
    rw [hpt]
    exact hmemZ
  have hEqLin : lineInteriorSet (centrePoint y)
      (uBendDirPos hf ha (centrePoint_mem_stripInterior y) ((mem_UHeight (a := a) (f := f)).mp hyU))
      = lineInteriorSet (centrePoint z)
        (uBendDirPos hf ha (centrePoint_mem_stripInterior z) ((mem_UHeight (a := a) (f := f)).mp hzU)) :=
    ubend_disjoint_or_equal hf (centrePoint_mem_stripInterior y)
      ((mem_UHeight (a := a) (f := f)).mp hyU) hwY.1 hwY.2.1 (ne_of_gt hwY.2.2)
      (centrePoint_mem_stripInterior z) ((mem_UHeight (a := a) (f := f)).mp hzU)
      hwZ.1 hwZ.2.1 (ne_of_gt hwZ.2.2) ⟨leafPt hf ha y x, hmemY, hmemZ'⟩
  -- the centreline point of `z` lies on the line of the leaf through `y`
  have hzmem : centrePoint z ∈ lineInteriorSet (centrePoint y)
      (uBendDirPos hf ha (centrePoint_mem_stripInterior y) ((mem_UHeight (a := a) (f := f)).mp hyU)) := by
    rw [hEqLin]
    rw [← uBendSet_eq_lineInteriorSet_pos hf ha hzU]
    exact uBendSet_mem hf ha (centrePoint_mem_stripInterior z) _
  rcases hzmem with ⟨-, s, hs⟩
  have hcoord : s * ((uBendDirPos hf ha (centrePoint_mem_stripInterior y)
      ((mem_UHeight (a := a) (f := f)).mp hyU)) 0) = 0 := by
    have h0 := congrArg (fun p : ℝ² => p 0) hs
    rw [show (centrePoint z) 0 = 1 / 2 by simp [centrePoint]] at h0
    have hcy : (centrePoint y + s • (uBendDirPos hf ha (centrePoint_mem_stripInterior y)
        ((mem_UHeight (a := a) (f := f)).mp hyU))) 0
        = 1 / 2 + s * ((uBendDirPos hf ha (centrePoint_mem_stripInterior y)
          ((mem_UHeight (a := a) (f := f)).mp hyU)) 0) := by simp [centrePoint]
    rw [hcy] at h0
    linarith
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hcoord with h | h
    · exact h
    · exact absurd h (ne_of_gt hwY.2.2)
  have hzz : centrePoint z = centrePoint y := by simpa [hs0] using hs
  have h1 := congrArg (fun p : ℝ² => p 1) hzz
  have : z = y := by simpa [centrePoint] using h1
  exact hyz this.symm


/-- **A `U`-leaf and a flat-interior leaf do not cross.** -/
lemma not_crosses_uHeight_flatInterior (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z : ℝ}
    (hyU : y ∈ UHeight a f) (hfi : IsFlatInterior f (centrePoint z)) (hyz : y ≠ z) :
    ¬ Crosses hf ha y z := by
  rintro ⟨x, hx, hEq⟩
  have hpt : leafPt hf ha y x = leafPt hf ha z x := leafPt_eq_of_leafG_eq hf ha hEq
  have hne : dN f (leafPt hf ha y x) ≠ 0 :=
    (uBendSet_subset_U_and_kernel hf ha (centrePoint_mem_stripInterior y)
      ((mem_UHeight (a := a) (f := f)).mp hyU)).1 _
      (leafPt_mem_uBendSet hf ha hyU hx)
  have hzero : dN f (leafPt hf ha z x) = 0 := by
    have hmem : leafPt hf ha z x ∈ flatComponent f (centrePoint z) :=
      leafPt_mem_flatComponent hf ha hfi hx
    have hinter : leafPt hf ha z x ∈ interior (FlatSet f) :=
      flatComponent_subset_flatInterior f (centrePoint z) hmem
    exact (mem_FlatSet.mp (interior_subset hinter)).2
  rw [← hpt] at hzero
  exact hne hzero

/-- The blend heights of two distinct parameters differ. -/
lemma blend_height_ne {h₁ h₂ t₁ t₂ : ℝ} (hx : h₁ < h₂) (ht : t₁ ≠ t₂) :
    (1 - t₁) * h₁ + t₁ * h₂ ≠ (1 - t₂) * h₁ + t₂ * h₂ := by
  intro hEq
  have h : (t₁ - t₂) * (h₂ - h₁) = 0 := by linarith
  rcases mul_eq_zero.mp h with h' | h'
  · exact ht (by linarith)
  · linarith

/-- The blend parameter is injective at fixed boundary data with distinct
centre heights. -/
lemma blendT_ne {α₁ β₁ α₂ β₂ y z : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) (hyz : y ≠ z) :
    blendT α₁ β₁ α₂ β₂ y ≠ blendT α₁ β₁ α₂ β₂ z := by
  rw [blendT_eq, blendT_eq]
  intro hcon
  rw [div_eq_div_iff hden hden] at hcon
  have h : (y - z) * (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2)) = 0 := by linarith
  rcases mul_eq_zero.mp h with h' | h'
  · exact hyz (by linarith)
  · exact hden h'

/-- **Two flat-interior leaves do not cross.** -/
lemma not_crosses_flatInterior_flatInterior (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    {y z : ℝ} (hfy : IsFlatInterior f (centrePoint y)) (hfz : IsFlatInterior f (centrePoint z))
    (hyz : y ≠ z) : ¬ Crosses hf ha y z := by
  rintro ⟨x, hx, hEq⟩
  have hpt : leafPt hf ha y x = leafPt hf ha z x := leafPt_eq_of_leafG_eq hf ha hEq
  have hmemY : leafPt hf ha y x ∈ flatComponent f (centrePoint y) :=
    leafPt_mem_flatComponent hf ha hfy hx
  have hmemZ : leafPt hf ha y x ∈ flatComponent f (centrePoint z) := by
    rw [hpt]
    exact leafPt_mem_flatComponent hf ha hfz hx
  have hcomp : flatComponent f (centrePoint y) = flatComponent f (centrePoint z) :=
    (flatComponent_eq_of_mem hmemY).symm.trans (flatComponent_eq_of_mem hmemZ)
  let hpY : centrePoint y ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)).mp hfy
  let hpZ : centrePoint z ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior z)).mp hfz
  have hleafY : spliceChord hf ha y = compLeaf hf ha (p := centrePoint y) hpY y :=
    spliceChord_eq_compLeaf_self hf ha hfy
  have hleafZ : spliceChord hf ha z = compLeaf hf ha (p := centrePoint y) hpY z := by
    rw [spliceChord_eq_compLeaf_self hf ha hfz]
    simpa [compLeaf] using
      (flatCompBend_of_component_eq hf ha hpZ hpY z hcomp.symm)
  have hGY := leafG_eq_genP hf ha hpY hleafY x
  have hGZ := leafG_eq_genP hf ha hpY hleafZ x
  rw [hGY, hGZ] at hEq
  have hden : sideH₂ (bwD2 hf ha hpY).1 (bwD2 hf ha hpY).2 (1 / 2)
      - sideH₁ (bwD1 hf ha hpY).1 (bwD1 hf ha hpY).2 (1 / 2) ≠ 0 := by
    have h₂ : sideH₂ (bwD2 hf ha hpY).1 (bwD2 hf ha hpY).2 (1 / 2) = bw₂ hf ha hpY := by
      rw [sideH₂_eq_sideH₁]
      exact sideH₁_data_half hf ha (centrePoint y) hpY (bwhh₂ hf ha hpY)
    have h₁ : sideH₁ (bwD1 hf ha hpY).1 (bwD1 hf ha hpY).2 (1 / 2) = bw₁ hf ha hpY :=
      sideH₁_data_half hf ha (centrePoint y) hpY (bwhh₁ hf ha hpY)
    rw [h₂, h₁]
    exact ne_of_gt (sub_pos.mpr (bwlt hf ha hpY))
  have htne : blendT (bwD1 hf ha hpY).1 (bwD1 hf ha hpY).2
        (bwD2 hf ha hpY).1 (bwD2 hf ha hpY).2 y
      ≠ blendT (bwD1 hf ha hpY).1 (bwD1 hf ha hpY).2
        (bwD2 hf ha hpY).1 (bwD2 hf ha hpY).2 z :=
    blendT_ne hden hyz
  have hxord : sideH₁ (bwD1 hf ha hpY).1 (bwD1 hf ha hpY).2 x
      < sideH₂ (bwD2 hf ha hpY).1 (bwD2 hf ha hpY).2 x := by
    rw [sideH₂_eq_sideH₁]
    exact bwD_order hf ha hpY x hx
  exact blend_height_ne hxord htne hEq

/-- Two leaf chords cross symmetrically. -/
lemma crosses_comm (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (y z : ℝ) :
    Crosses hf ha y z ↔ Crosses hf ha z y := by
  constructor <;> rintro ⟨x, hx, hEq⟩ <;> exact ⟨x, hx, hEq.symm⟩


/-! ## No crossings on the `U`/flat-interior height set -/

/-- No two leaves at `U`- or flat-interior heights cross. -/
lemma not_crosses_of_D (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z : ℝ}
    (hy : y ∈ UHeight a f ∨ IsFlatInterior f (centrePoint y))
    (hz : z ∈ UHeight a f ∨ IsFlatInterior f (centrePoint z)) (hyz : y ≠ z) :
    ¬ Crosses hf ha y z := by
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact not_crosses_uHeight_uHeight hf ha hy hz hyz
  · exact not_crosses_uHeight_flatInterior hf ha hy hz hyz
  · intro hc
    exact not_crosses_uHeight_flatInterior hf ha hz hy (Ne.symm hyz) ((crosses_comm hf ha y z).mp hc)
  · exact not_crosses_flatInterior_flatInterior hf ha hy hz hyz

/-- The Lipschitz bound for leaves at `U`- or flat-interior heights. -/
lemma two_mul_abs_le_of_D (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z : ℝ}
    (hy : y ∈ UHeight a f ∨ IsFlatInterior f (centrePoint y))
    (hz : z ∈ UHeight a f ∨ IsFlatInterior f (centrePoint z)) (hyz : y ≠ z) :
    2 * |y - z| ≥ |leafM hf ha y - leafM hf ha z| :=
  two_mul_abs_le_of_not_crosses hf ha hyz (not_crosses_of_D hf ha hy hz hyz)

/-! ## The flat-interior heights are exactly the complement of `closure UHeight` -/

/-- The set of flat-interior heights is open. -/
lemma isOpen_flatInteriorHeights :
    IsOpen {y : ℝ | IsFlatInterior f (centrePoint y)} := by
  have h : {y : ℝ | IsFlatInterior f (centrePoint y)}
      = (fun y : ℝ => centrePoint y) ⁻¹' (interior (FlatSet f)) := by
    ext y
    exact IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y)
  rw [h]
  exact isOpen_interior.preimage continuous_centrePoint

/-- **The closure of the `U`-heights is the complement of the flat-interior
heights.** -/
lemma mem_closure_UHeight_iff (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y : ℝ} :
    y ∈ closure (UHeight a f) ↔ ¬ IsFlatInterior f (centrePoint y) := by
  constructor
  · intro hy hfi
    have hsub : UHeight a f ⊆ {z : ℝ | ¬ IsFlatInterior f (centrePoint z)} := by
      intro z hz hzfi
      exact (uHeight_not_flatInterior hz) hzfi
    have hclosed : IsClosed {z : ℝ | ¬ IsFlatInterior f (centrePoint z)} :=
      (isOpen_flatInteriorHeights (f := f)).isClosed_compl
    exact (closure_minimal hsub hclosed) hy hfi
  · intro hy
    by_cases hyU : y ∈ UHeight a f
    · exact subset_closure hyU
    · have hyF : y ∈ FlatHeight a f := by
        by_contra h
        exact hyU ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mpr h)
      rw [Metric.mem_closure_iff]
      intro ε hε
      rcases exists_uHeight_near_degenerate_flat hf ha hyF hy ε hε with ⟨u, huU, hu⟩
      exact ⟨u, huU, by simpa [Real.dist_eq, abs_sub_comm] using hu⟩


/-! ## Value identities at the four height types -/

/-- **At a `U`-height** the spliced leaf is the canonical `U`-leaf. -/
lemma leafM_eq_slopeAtHeight (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y : ℝ}
    (hyU : y ∈ UHeight a f) : leafM hf ha y = slopeAtHeight hf ha hyU := by
  have hA : (uHeightBend hf ha ⟨y, hyU⟩).A = !₂[(0 : ℝ), y - slopeAtHeight hf ha hyU / 2] := by
    simp only [uHeightBend, uHeightA]
    exact uBendA_atHeight_eq hf ha hyU
  have hB : (uHeightBend hf ha ⟨y, hyU⟩).B = !₂[(1 : ℝ), y + slopeAtHeight hf ha hyU / 2] := by
    simp only [uHeightBend, uHeightB]
    exact uBendB_atHeight_eq hf ha hyU
  rw [leafM, spliceChord_eq_uHeightBend hf ha hyU, BendData.slope, hA, hB]
  simp

/-- The lower frontier chord of a flat component is flat. -/
theorem frontier_chord_flat_lower {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) :
    ∀ z : ℝ², z ∈ stripChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 →
      dN f z = 0 := by
  intro z hz
  have hzS : z ∈ stripInterior := stripChord_subset_stripInterior hz
  have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 u
        < sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 u :=
    sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt
  have hEq := frontier_betweenChord hord
  have hin : z ∈ frontier (betweenChord
      (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
      (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) ∩ stripInterior := by
    rw [hEq]
    exact Or.inl hz
  have hzfront : z ∈ frontier (flatComponent f p) := by
    rw [hC]
    exact hin.1
  have hzF := flatComponent_frontier_subset_FlatSet hf hzS hzfront
  exact (mem_FlatSet.mp hzF).2

/-- **At a frontier height** the spliced leaf is the frontier chord: the chord
data at a frontier height is flat. -/
lemma frontier_chord_flat_at (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) {h : ℝ} (hh : h ∈ frHeights f p) :
    ∀ z : ℝ², z ∈ stripChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 →
      dN f z = 0 := by
  have hfr : frHeights f p = {x : ℝ | x = bw₁ hf ha hp ∨ x = bw₂ hf ha hp} :=
    frHeights_eq_extremes hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp)
      (bwC hf ha hp)
  have hmem : h = bw₁ hf ha hp ∨ h = bw₂ hf ha hp := by
    have h' := hh
    rw [hfr] at h'
    simpa using h'
  rcases hmem with h₁ | h₂
  · subst h₁
    intro z hz
    have hz' : z ∈ stripChord (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
        (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 := by
      rwa [frCompData_irrel hf ha p hp hh (bwhh₁ hf ha hp)] at hz
    exact frontier_chord_flat_lower hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp)
      (bwC hf ha hp) z hz'
  · subst h₂
    intro z hz
    have hz' : z ∈ stripChord (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
        (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 := by
      rwa [frCompData_irrel hf ha p hp hh (bwhh₂ hf ha hp)] at hz
    exact frontier_chord_flat hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp)
      (bwC hf ha hp) z hz'

/-- **The slope of the component leaf at a frontier height** is the slope of
the frontier chord. -/
lemma compLeaf_slope_of_mem_frHeights (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²}
    (hp : p ∈ interior (FlatSet f)) {h : ℝ} (hh : h ∈ frHeights f p) :
    (compLeaf hf ha (p := p) hp h).slope
      = (frCompData hf ha p hp h hh).2 - (frCompData hf ha p hp h hh).1 := by
  have hfr : frHeights f p = {x : ℝ | x = bw₁ hf ha hp ∨ x = bw₂ hf ha hp} :=
    frHeights_eq_extremes hf ha hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp)
      (bwC hf ha hp)
  have hmem : h = bw₁ hf ha hp ∨ h = bw₂ hf ha hp := by
    have h' := hh
    rw [hfr] at h'
    simpa using h'
  rcases hmem with h₁ | h₂
  · subst h₁
    rw [compLeaf_eq_blend, BendData.slope, blendBend_A_eq, blendBend_B_eq]
    simp only [genB, genA, genP_coord1]
    rw [frCompData_irrel hf ha p hp hh (bwhh₁ hf ha hp)]
    have ht : blendT (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2
        (bw₁ hf ha hp) = 0 := by
      rw [blendT_eq]
      rw [show sideH₁ (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (1 / 2) = bw₁ hf ha hp from
        sideH₁_data_half hf ha p hp (bwhh₁ hf ha hp)]
      rw [sideH₂_eq_sideH₁, show sideH₁ (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 (1 / 2) = bw₂ hf ha hp from
        sideH₁_data_half hf ha p hp (bwhh₂ hf ha hp)]
      rw [sub_self]
      exact zero_div _
    rw [ht]
    simp [sideH₁_zero, sideH₂_zero, sideH₁_one, sideH₂_one, bwD1, bwD2]
  · subst h₂
    rw [compLeaf_eq_blend, BendData.slope, blendBend_A_eq, blendBend_B_eq]
    simp only [genB, genA, genP_coord1]
    rw [frCompData_irrel hf ha p hp hh (bwhh₂ hf ha hp)]
    have ht : blendT (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (bwD2 hf ha hp).1 (bwD2 hf ha hp).2
        (bw₂ hf ha hp) = 1 := by
      rw [blendT_eq]
      rw [show sideH₁ (bwD1 hf ha hp).1 (bwD1 hf ha hp).2 (1 / 2) = bw₁ hf ha hp from
        sideH₁_data_half hf ha p hp (bwhh₁ hf ha hp)]
      rw [sideH₂_eq_sideH₁, show sideH₁ (bwD2 hf ha hp).1 (bwD2 hf ha hp).2 (1 / 2) = bw₂ hf ha hp from
        sideH₁_data_half hf ha p hp (bwhh₂ hf ha hp)]
      exact div_self (ne_of_gt (sub_pos.mpr (bwlt hf ha hp)))
    rw [ht]
    simp [sideH₁_zero, sideH₂_zero, sideH₁_one, sideH₂_one, bwD1, bwD2]


/-- The leaf slope in terms of the left endpoint height. -/
lemma leafM_eq_two_mul (hf : IsMoebiusEmbedding a f) (ha : 0 < a) (z : ℝ) :
    leafM hf ha z = 2 * (z - spliceA1 hf ha z) := by
  have h := leafA1_eq hf ha z
  change spliceA1 hf ha z = z - leafM hf ha z / 2 at h
  linarith

/-- **Sequential continuity of the leaf slope along `U`-heights.** -/
lemma leafM_tendsto_of_uHeight (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ}
    {y : ℕ → ℝ} (hyU : ∀ n : ℕ, y n ∈ UHeight a f) (hy : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => leafM hf ha (y n)) atTop (𝓝 (leafM hf ha y₀)) := by
  have hcl : y₀ ∈ closure (UHeight a f) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases (Metric.tendsto_atTop.mp hy) ε hε with ⟨N, hN⟩
    exact ⟨y N, hyU N, by simpa [Real.dist_eq, abs_sub_comm] using hN N le_rfl⟩
  by_cases hy₀U : y₀ ∈ UHeight a f
  · have hcont : ContinuousAt (fun z : ℝ => spliceA1 hf ha z) y₀ :=
      (continuousOn_spliceA1_uHeight hf ha).continuousAt ((isOpen_UHeight hf).mem_nhds hy₀U)
    have heqfun : (fun n : ℕ => leafM hf ha (y n))
        = fun n : ℕ => 2 * (y n - spliceA1 hf ha (y n)) := by
      funext n
      exact leafM_eq_two_mul hf ha (y n)
    rw [heqfun, leafM_eq_two_mul hf ha y₀]
    exact (hy.sub (hcont.tendsto.comp hy)).const_mul 2
  · have hyF : y₀ ∈ FlatHeight a f := by
      by_contra h
      exact hy₀U ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mpr h)
    have hni : ¬ IsFlatInterior f (centrePoint y₀) := (mem_closure_UHeight_iff hf ha).mp hcl
    by_cases hcov : CoveredHeight (f := f) y₀
    · let P : ℝ² := Classical.choose hcov
      have hpI : P ∈ interior (FlatSet f) := (Classical.choose_spec hcov).1
      have hh₀ : y₀ ∈ frHeights f P := (Classical.choose_spec hcov).2
      have hylim : Tendsto y atTop (𝓝 (sideH₁ (frCompData hf ha P hpI y₀ hh₀).1
          (frCompData hf ha P hpI y₀ hh₀).2 (1 / 2))) := by
        rw [sideH₁_data_half hf ha P hpI hh₀]
        exact hy
      have hlim := uBend_slope_limit hf ha (frontier_chord_flat_at hf ha hpI hh₀)
        (fun n : ℕ => (mem_UHeight (a := a) (f := f)).mp (hyU n)) hylim
      have hval : leafM hf ha y₀
          = (frCompData hf ha P hpI y₀ hh₀).2 - (frCompData hf ha P hpI y₀ hh₀).1 := by
        rw [leafM, spliceChord_eq_coveredLeaf hf ha hy₀U hni hcov]
        exact compLeaf_slope_of_mem_frHeights hf ha hpI hh₀
      rw [hval]
      have hseq : (fun n : ℕ => leafM hf ha (y n)) = fun n : ℕ => uBendSlope hf ha
          (centrePoint_mem_stripInterior (y n)) ((mem_UHeight (a := a) (f := f)).mp (hyU n)) := by
        funext n
        exact leafM_eq_slopeAtHeight hf ha (hyU n)
      rw [hseq]
      exact hlim
    · have hval : leafM hf ha y₀ = degenerateSlope hf ha hyF hni hcov := by
        have hA := degenerateLeaf_A hf ha hyF hni hcov
        have hB := degenerateLeaf_B hf ha hyF hni hcov
        rw [leafM, spliceChord_eq_uncoveredLeaf hf ha hyF hy₀U hni hcov, BendData.slope]
        simp only [uncoveredLeaf]
        rw [hA, hB]
        simp
      rw [hval]
      have hseq : (fun n : ℕ => leafM hf ha (y n)) = fun n : ℕ => slopeAtHeight hf ha (hyU n) := by
        funext n
        exact leafM_eq_slopeAtHeight hf ha (hyU n)
      rw [hseq]
      have ht := slopeLimitOfSeq_tendsto hf ha hyU hy
      have heq := slopeLimit_eq_degenerateSlope hf ha hyF hni hcov hyU hy
      rw [heq] at ht
      exact ht


/-! ## Passing to the limit along `U`-height sequences -/

/-- Every point of `closure UHeight` is the limit of a sequence of
`U`-heights. -/
lemma seq_of_mem_closure {y : ℝ} (hy : y ∈ closure (UHeight a f)) :
    ∃ Y : ℕ → ℝ, (∀ n : ℕ, Y n ∈ UHeight a f) ∧ Tendsto Y atTop (𝓝 y) := by
  have h : ∀ n : ℕ, ∃ w : ℝ, w ∈ UHeight a f ∧ dist y w < 1 / (n + 1) := by
    intro n
    exact Metric.mem_closure_iff.mp hy (1 / (n + 1)) (by positivity)
  choose Y hYU hYd using h
  refine ⟨Y, hYU, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist : ∀ n : ℕ, dist (Y n) y < 1 / (n + 1) := by
    intro n
    rw [dist_comm]
    exact hYd n
  have hg : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hdist n)) hg

/-- The Lipschitz bound passes to limits of sequences in `UHeight ∪ FI`. -/
lemma L_of_limit_D (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z : ℝ} {Y Z : ℕ → ℝ}
    (hYD : ∀ n : ℕ, Y n ∈ UHeight a f ∨ IsFlatInterior f (centrePoint (Y n)))
    (hZD : ∀ n : ℕ, Z n ∈ UHeight a f ∨ IsFlatInterior f (centrePoint (Z n)))
    (hYt : Tendsto Y atTop (𝓝 y)) (hZt : Tendsto Z atTop (𝓝 z))
    (hYc : Tendsto (fun n : ℕ => leafM hf ha (Y n)) atTop (𝓝 (leafM hf ha y)))
    (hZc : Tendsto (fun n : ℕ => leafM hf ha (Z n)) atTop (𝓝 (leafM hf ha z)))
    (hyz : y ≠ z) :
    2 * |y - z| ≥ |leafM hf ha y - leafM hf ha z| := by
  have hev : ∀ᶠ n in atTop, Y n ≠ Z n := by
    rcases lt_or_gt_of_ne hyz with h | h
    · exact (hYt.eventually_lt hZt h).mono (fun n hn => ne_of_lt hn)
    · exact (hZt.eventually_lt hYt h).mono (fun n hn => ne_of_gt hn)
  have hineq : ∀ᶠ n in atTop, |leafM hf ha (Y n) - leafM hf ha (Z n)| ≤ 2 * |Y n - Z n| := by
    filter_upwards [hev] with n hn
    exact two_mul_abs_le_of_D hf ha (hYD n) (hZD n) hn
  have hlim1 : Tendsto (fun n : ℕ => |leafM hf ha (Y n) - leafM hf ha (Z n)|) atTop
      (𝓝 |leafM hf ha y - leafM hf ha z|) := (hYc.sub hZc).abs
  have hlim2 : Tendsto (fun n : ℕ => 2 * |Y n - Z n|) atTop (𝓝 (2 * |y - z|)) :=
    ((hYt.sub hZt).abs).const_mul 2
  exact le_of_tendsto_of_tendsto hlim1 hlim2 hineq

/-- **The Lipschitz bound for the leaf slope holds for all heights.** -/
lemma two_mul_abs_le_leafM (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z : ℝ}
    (hyz : y ≠ z) : 2 * |y - z| ≥ |leafM hf ha y - leafM hf ha z| := by
  by_cases hyA : y ∈ closure (UHeight a f)
  · by_cases hzA : z ∈ closure (UHeight a f)
    · rcases seq_of_mem_closure (f := f) hyA with ⟨Y, hYU, hYt⟩
      rcases seq_of_mem_closure (f := f) hzA with ⟨Z, hZU, hZt⟩
      exact L_of_limit_D hf ha (fun n => Or.inl (hYU n)) (fun n => Or.inl (hZU n)) hYt hZt
        (leafM_tendsto_of_uHeight hf ha hYU hYt) (leafM_tendsto_of_uHeight hf ha hZU hZt) hyz
    · have hzFI : IsFlatInterior f (centrePoint z) := by
        by_contra h
        exact hzA ((mem_closure_UHeight_iff hf ha).mpr h)
      rcases seq_of_mem_closure (f := f) hyA with ⟨Y, hYU, hYt⟩
      exact L_of_limit_D hf ha (fun n => Or.inl (hYU n)) (fun _ => Or.inr hzFI) hYt
        tendsto_const_nhds (leafM_tendsto_of_uHeight hf ha hYU hYt) tendsto_const_nhds hyz
  · have hyFI : IsFlatInterior f (centrePoint y) := by
      by_contra h
      exact hyA ((mem_closure_UHeight_iff hf ha).mpr h)
    by_cases hzA : z ∈ closure (UHeight a f)
    · rcases seq_of_mem_closure (f := f) hzA with ⟨Z, hZU, hZt⟩
      exact L_of_limit_D hf ha (fun _ => Or.inr hyFI) (fun n => Or.inl (hZU n))
        tendsto_const_nhds hZt tendsto_const_nhds (leafM_tendsto_of_uHeight hf ha hZU hZt) hyz
    · have hzFI : IsFlatInterior f (centrePoint z) := by
        by_contra h
        exact hzA ((mem_closure_UHeight_iff hf ha).mpr h)
      exact two_mul_abs_le_of_D hf ha (Or.inr hyFI) (Or.inr hzFI) hyz

/-- `leafPt` is injective in the horizontal coordinate. -/
lemma leafPt_eq_iff (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y z x x' : ℝ}
    (h : leafPt hf ha y x = leafPt hf ha z x') : x = x' := by
  have h0 := congrArg (fun p : ℝ² => p 0) h
  simpa [leafPt_coord0 hf ha y x, leafPt_coord0 hf ha z x'] using h0

/-- The signed endpoint heights of the spliced chord family of the band
foliation are non-decreasing in the centreline height (the leaves foliate
the strip: they are ordered and do not cross; on wedge/fan flat components
the height is locally constant). -/
theorem spliceChord_endpoint_monotone {a : ℝ} {f : ℝ² → ℝ³}
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (ha : 0 < a) :
    Monotone (fun y : ℝ => (Submission.spliceChord hf ha y).A 1) ∧
    Monotone (fun y : ℝ => (Submission.spliceChord hf ha y).B 1) := by
  constructor
  · intro y z hyz
    rcases lt_or_eq_of_le hyz with hlt | heq
    · have h := two_mul_abs_le_leafM hf ha (ne_of_lt hlt)
      rw [abs_of_nonpos (by linarith : y - z ≤ 0)] at h
      have h1 : leafM hf ha z - leafM hf ha y ≤ |leafM hf ha y - leafM hf ha z| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      change leafA1 hf ha y ≤ leafA1 hf ha z
      rw [leafA1_eq hf ha y, leafA1_eq hf ha z]
      linarith
    · rw [heq]
  · intro y z hyz
    rcases lt_or_eq_of_le hyz with hlt | heq
    · have h := two_mul_abs_le_leafM hf ha (ne_of_lt hlt)
      rw [abs_of_nonpos (by linarith : y - z ≤ 0)] at h
      have h1 : leafM hf ha y - leafM hf ha z ≤ |leafM hf ha y - leafM hf ha z| :=
        le_abs_self _
      change leafB1 hf ha y ≤ leafB1 hf ha z
      rw [leafB1_eq hf ha y, leafB1_eq hf ha z]
      linarith
    · rw [heq]


end

end Commons.Geometry.Moebius
