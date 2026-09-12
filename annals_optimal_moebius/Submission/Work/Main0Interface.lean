import Submission.PaperBand.Band
import Submission.Work.TrapezoidLemma

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open Filter
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# main0 interface + Lemma T statement (WORK IN PROGRESS — target only)

Design of the band-foliation interface that Lemma T consumes.  The data is
kept in the FLAT PREIMAGE model (unit strip with the period identification),
where every bend is a straight chord from the left boundary line to the
right boundary line and all arc lengths are Euclidean:

* `BendData`: a straight chord `[A,B]` with `A` on `x0 = 0`, `B` on
  `x0 = 1`; its `slope = B1 − A1` is the horizontal displacement `Δ` of the
  bend, so its preimage length is `√(1 + Δ²)`.
* `FoliationData a`: a family `bend : ℝ → BendData` parametrized by the
  centreline height `y` (each leaf meets the centreline point `(1/2, y)`
  once, i.e. `y = (A1+B1)/2`), with the two deck symmetries of the band:
  * period: `bend (y + a)` is the period-image of `bend y` (the Möbius
    flip), forcing the ORIENTATION FLIP used by Lemma T;
  * continuity of the leaf endpoints in `y`.
  (These are exactly the properties the U-bend/flat-chord machinery of
  `FlatComponents`/`LeafContinuity` is expected to provide; instantiation is
  future work, not claimed here.)

**Lemma T (target)**: from a foliation with the two deck symmetries,
orthogonal/coplanar pairs of leaves exist (`F = (g,h)` of the paper has a
zero by the odd-map/winding argument on the S² of pairs).  For the
preimage-side reduction established in `TrapezoidLemma`, the needed OUTPUT
is one leaf whose `t = |Δ|` satisfies the two aspect inequalities
`√(1+t²) ≤ a−t` and `√(5+t²) < a+t` — which then feeds
`lemmaG_of_aspect_inequalities` and closes the theorem.

This file states the interface and the target theorem; the proof is the
remaining load-bearing construction (it is NOT yet proven).
-/

noncomputable section
namespace Submission

/-- A straight bend (pre-bend chord) in the strip: `A ∈ {x0=0}`,
`B ∈ {x0=1}`. -/
structure BendData where
  A : ℝ²
  B : ℝ²
  left_coord : A 0 = 0
  right_coord : B 0 = 1

namespace BendData

/-- The horizontal displacement of the bend: `Δ = B1 − A1`. -/
def slope (b : BendData) : ℝ := b.B 1 - b.A 1

/-- The preimage length of the bend: `√(1 + Δ²)`. -/
def length (b : BendData) : ℝ := Real.sqrt (1 + b.slope ^ 2)

/-- The bend meets the centreline point `(1/2, y)` iff
`y = (A1 + B1)/2`. -/
def centreHeight (b : BendData) : ℝ := (b.A 1 + b.B 1) / 2

end BendData

/-- The band-foliation interface: a continuous family of bends through the
centreline points, invariant under the band's deck symmetries.  The period
condition `bend (y + a) = period(bend y)` encodes the Möbius orientation
flip that Lemma T's odd-map argument needs. -/
structure FoliationData (a : ℝ) where
  bend : ℝ → BendData
  centre : ∀ y : ℝ, (bend y).centreHeight = y
  period : ∀ y : ℝ, (bend (y + a)).A = period a (bend y).B ∧
    (bend (y + a)).B = period a (bend y).A
  continuous_left : Continuous (fun y : ℝ => ((bend y).A 1 : ℝ))
  continuous_right : Continuous (fun y : ℝ => ((bend y).B 1 : ℝ))

namespace FoliationData

/-- The signed displacement of the leaf through centreline height `y`. -/
def delta {a : ℝ} (F : FoliationData a) (y : ℝ) : ℝ := (F.bend y).slope

/-- The `x1`-coordinate of the period image shifts by `a`. -/
lemma period_apply1 (a : ℝ) (p : ℝ²) : (OptimalMoebius.period a p) 1 = p 1 + a := by
  simp [OptimalMoebius.period]

/-- **The Möbius flip reverses the displacement**: `Δ(y+a) = −Δ(y)` —
going once around the band flips the orientation of the ruling.  This is
the deck-symmetry input of Lemma T's odd-map argument. -/
lemma delta_flip {a : ℝ} (F : FoliationData a) (y : ℝ) :
    F.delta (y + a) = -F.delta y := by
  unfold delta BendData.slope
  have hA : ((F.bend (y + a)).A) 1 = ((F.bend y).B) 1 + a := by
    rcases (F.period y) with ⟨hA, hB⟩
    rw [hA]
    exact period_apply1 a (F.bend y).B
  have hB : ((F.bend (y + a)).B) 1 = ((F.bend y).A) 1 + a := by
    rcases (F.period y) with ⟨hA, hB⟩
    rw [hB]
    exact period_apply1 a (F.bend y).A
  rw [hA, hB]
  ring

/-- The displacement is continuous in the centreline height (the leaf
endpoints are continuous). -/
theorem continuous_delta {a : ℝ} (F : FoliationData a) : Continuous (F.delta) := by
  unfold delta BendData.slope
  exact F.continuous_right.sub F.continuous_left

end FoliationData


/-- **Δ has a zero on the centreline**: a continuous odd displacement
(`Δ(y+a) = −Δ(y)`) over one period must vanish somewhere (intermediate
value between the opposite-sign endpoint values). -/
theorem delta_zero_exists {a : ℝ} (ha : 0 < a) (F : FoliationData a) :
    ∃ y : ℝ, F.delta y = 0 := by
  by_cases h0 : F.delta 0 = 0
  · exact ⟨0, h0⟩
  have hcont : ContinuousOn (F.delta) (Set.Icc (0 : ℝ) (0 + a)) :=
    F.continuous_delta.continuousOn
  have hconn : IsPreconnected (Set.Icc (0 : ℝ) (0 + a)) := isPreconnected_Icc
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (0 + a) := by
    rw [Set.mem_Icc]
    constructor <;> linarith [ha]
  have hmema : (0 + a) ∈ Set.Icc (0 : ℝ) (0 + a) := by
    rw [Set.mem_Icc]
    constructor <;> linarith [ha]
  have hflip : F.delta (0 + a) = -F.delta 0 := by
    simpa using (F.delta_flip 0)
  by_cases hneg : F.delta 0 < 0
  · -- Δ0 < 0 < Δa
    have hpos : 0 < F.delta (0 + a) := by linarith
    have hIVT : Set.Icc (F.delta 0) (F.delta (0 + a)) ⊆ F.delta '' Set.Icc (0 : ℝ) (0 + a) :=
      IsPreconnected.intermediate_value hconn hmem0 hmema hcont
    have hz : (0 : ℝ) ∈ Set.Icc (F.delta 0) (F.delta (0 + a)) := by
      rw [Set.mem_Icc]
      exact ⟨le_of_lt hneg, le_of_lt hpos⟩
    rcases hIVT hz with ⟨c, hcI, hfc⟩
    exact ⟨c, hfc⟩
  · -- Δ0 > 0 > Δa
    have hpos : 0 < F.delta 0 := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm h0)
    have hneg' : F.delta (0 + a) < 0 := by linarith
    have hIVT : Set.Icc (F.delta (0 + a)) (F.delta 0) ⊆ F.delta '' Set.Icc (0 : ℝ) (0 + a) :=
      IsPreconnected.intermediate_value hconn hmema hmem0 hcont
    have hz : (0 : ℝ) ∈ Set.Icc (F.delta (0 + a)) (F.delta 0) := by
      rw [Set.mem_Icc]
      exact ⟨le_of_lt hneg', le_of_lt hpos⟩
    rcases hIVT hz with ⟨c, hcI, hfc⟩
    exact ⟨c, hfc⟩

/-! ## Sublemmas and a necessary interface check -/

/-- The horizontal foliation: every leaf is the horizontal chord through the
centreline point `(1/2, y)` (slope `Δ ≡ 0`).  Exists for every `a > 0`,
showing that `FoliationData a` alone carries NO information about the band's
aspect. -/
noncomputable def horizBend (y : ℝ) : BendData where
  A := !₂[(0 : ℝ), y]
  B := !₂[(1 : ℝ), y]
  left_coord := by simp
  right_coord := by simp

/-- The horizontal family satisfies the foliation interface (any `a > 0`). -/
noncomputable def horizontalFoliation (a : ℝ) (_ha : 0 < a) : FoliationData a where
  bend := horizBend
  centre := by
    intro y
    unfold horizBend BendData.centreHeight
    norm_num
  period := by
    intro y
    constructor <;> (ext i; fin_cases i <;> simp [horizBend, period])
  continuous_left := by
    change Continuous (fun y : ℝ => y)
    exact continuous_id
  continuous_right := by
    change Continuous (fun y : ℝ => y)
    exact continuous_id

/-- The horizontal family has identically zero displacement. -/
lemma horizontal_delta_zero {a : ℝ} (ha : 0 < a) (y : ℝ) :
    (horizontalFoliation a ha).delta y = 0 := by
  simp [horizontalFoliation, horizBend, BendData.slope, FoliationData.delta]

/-- **The earlier `lemmaT` target is FALSE as stated**: the horizontal
foliation at aspect `a = 2` (`0 < 2`, `√5 ≈ 2.24 > 2`) has every leaf with
`t = 0`, yet the conclusion would require `√5 < 2`.  Hence the preimage-only
interface does NOT capture the geometry that forces the aspect
inequalities: `FoliationData` must be tied to an actual embedded band
(leaves with straight images, the F-map over image directions) before such
a target can be true. -/
theorem lemmaT_target_false_for_horizontal :
    ∃ a : ℝ, 0 < a ∧ ∃ F : FoliationData a,
      ¬ ∃ y : ℝ,
        |(F.bend y).slope| ≤ a ∧
          Real.sqrt (1 + |(F.bend y).slope| ^ 2) ≤ a - |(F.bend y).slope| ∧
            Real.sqrt (5 + |(F.bend y).slope| ^ 2) < a + |(F.bend y).slope| := by
  let h2' : (0 : ℝ) < 2 := by norm_num
  refine ⟨2, h2', horizontalFoliation 2 h2', ?_⟩
  intro hy
  rcases hy with ⟨y, h1, h2, h3⟩
  have hd : (horizontalFoliation 2 h2').delta y = 0 :=
    horizontal_delta_zero (a := 2) h2' y
  have hd0 : ((horizontalFoliation 2 h2').bend y).slope = 0 := by
    simpa [FoliationData.delta] using hd
  have ht : |((horizontalFoliation 2 h2').bend y).slope| = 0 := by
    rw [hd0]
    norm_num
  have h3' : Real.sqrt (5 + 0 ^ 2) < 2 + (0 : ℝ) := by
    simpa [ht] using h3
  have hsimpl : Real.sqrt 5 < (2 : ℝ) := by simpa using h3'
  have hsq : 5 < (2 : ℝ) ^ 2 := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mp hsimpl
  norm_num at hsq

/-!
## Lemma T — REVISED TARGET (interface must be extended)

The earlier target `lemmaT_main0 : ∀ F : FoliationData a, ∃ leaf with the
aspect inequalities` is FALSE (see `lemmaT_target_false_for_horizontal`:
the horizontal foliation at `a = 2` is a counterexample).  The
preimage-slope interface drops the image geometry that carries the content.

REVISED DESIGN: `FoliationData` must be parameterized by the actual
embedded band `f : ℝ² → ℝ³` (`IsMoebiusEmbedding a f`); each leaf must be
a genuine pre-bend of `f` (straight image under the isometry); and Lemma
T's statement must quantify over the foliation of a GIVEN embedded band
and assert the paper's F=(g,h) zero — producing a T-pattern leaf whose
`t = |Δ|` satisfies the aspect inequalities.  Writing that true statement
is the next step of the interface design (image-side bend directions and
midpoints over the foliation family), deferred until the extension is
spelled out.
-/

end Submission