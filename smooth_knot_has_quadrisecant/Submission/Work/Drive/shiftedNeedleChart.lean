import Mathlib
import Submission.Work.Drive.needleShift
import Submission.Work.Drive.needleShiftCore
import Submission.Work.Drive.normalFrame
import Submission.Work.Drive.needleProfileDefs

/-!
# The chart of the shifted needle: height, chord coordinate, and the chart pin

`Work.Drive.needleShiftCore` reduces the needle's flattening pin to `Work.Drive.FlatteningCore`:
a frame `(u, v)`, a centre `c'`, the planar identity, the ray condition and the positivity of the
angular velocity.  This module fixes the *chart* in which those clauses are to be checked for the
**shifted** needle `N' t = needleFam r D lam δ₁ δ₂ ε (t + period/4)` (whose base point is the middle
of the retained arc, see `Submission/Work/Drive/NOTES_lowEnd_SHIFT.md`):

* `Work.Drive.nHeight … e t = ⟪N' t - chordEndA, e⟫` — the `e`-height of the needle above the
  *line* of its chord (`e` is the unit "up" direction, perpendicular to the chord);
* `Work.Drive.nCoord … v t = ⟪N' t - chordEndA, v⟫` — the chord coordinate (along the unit chord
  direction `v`).

With `h₀ = nHeight … e 0` (the height of the base point) and a level `0 < y₀ < h₀`, the centre is
`c' = N' 0 - y₀ e`, and the core clauses read, in the chart:

* the base point is `(nCoord … v 0, h₀)` and `polarDir (… ) c' e v 0 = (1, 0)`;
* the ray condition (`hsingle`): a point with `nCoord = nCoord … v 0` and `0 < t < period` lies at
  height strictly below `h₀ - y₀` (so it is *not* on the ray from `c'` through `N' 0`, and it also
  cannot be `c'` itself);
* the angular velocity: `(nHeight t - h₀ + y₀) * (deriv nCoord t) - (nCoord t - nCoord 0) *
  (deriv nHeight t) > 0`.

`Work.Drive.ShiftedNeedleChartData` is that conjunction and `Work.Drive.NeedleShiftedChartPin` its
uniform-in-the-box form.  The passage *chart datum ⟹ `FlatteningCore`* (a linear-algebra assembly,
delegated as `Work.Drive.flatteningCore_of_chartData`) and the passage *chart pin ⟹ needle end* are
the content of the next module; this one only fixes the vocabulary.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The needle with its parameter shifted by `period/4`**, so that its base point `t = 0` is the
middle of the retained arc (`arcFrac = 1/2`). -/
def shiftedNeedle (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) :
    ℝ → Space :=
  fun t => needleFam r D lam δ₁ δ₂ ε (t + period / 4)

/-- **The `e`-height of the shifted needle above the line of its chord.** -/
def nHeight (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) (e : Space)
    (t : ℝ) : ℝ :=
  inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - chordEndA r D δ₂ ε) e

/-- **The chord coordinate of the shifted needle** (its coordinate along the unit direction `v`). -/
def nCoord (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) (v : Space)
    (t : ℝ) : ℝ :=
  inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε t - chordEndA r D δ₂ ε) v

/-- **The canonical "up" direction of the chart**: the offset of the base point from the *line* of
the chord, taken in the plane perpendicular to the chord direction `v`.  It is nonzero exactly when
the base point is off the chord's line, and then `Work.Drive.nHeight` in its direction is its norm:

    nHeight r D lam δ₁ δ₂ ε (‖chartUp‖⁻¹ • chartUp) 0 = ‖chartUp‖ .

Every unit `e ⊥ v` with `0 < nHeight … e 0` is admissible for the *frame* clauses of the pin, but the
single-ray and angular-velocity clauses are to be checked for *this* direction (the `∀ e` form of the
angular-velocity clause is **false**: see `NOTES_needleChartPin_SESSION.md` §6). -/
def chartUp (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) (v : Space) :
    Space :=
  shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε
    - (nCoord r D lam δ₁ δ₂ ε v 0) • v

/-- `chartUp` is perpendicular to `v` (for a unit `v`). -/
lemma inner_chartUp_v (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (chartUp r D lam δ₁ δ₂ ε v) v = 0 := by
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  rw [chartUp, inner_sub_left, real_inner_smul_left, nCoord, hv1]
  ring

/-- If `⟪z, u⟫ = ‖u‖²` then `‖u‖⁻¹ • u` is the unit vector in the direction `u` and
`⟪z, ‖u‖⁻¹ • u⟫ = ‖u‖`. -/
lemma inner_smul_unit_of_inner_eq (z u : Space) (h : inner ℝ z u = ‖u‖ ^ 2) :
    inner ℝ z ((‖u‖)⁻¹ • u) = ‖u‖ := by
  rcases eq_or_ne u 0 with rfl | hne
  · simp
  · rw [real_inner_smul_right, h, pow_two, ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne), one_mul]

/-- **The orthogonal projection identity.**  For a unit `v` and any `z`, the vector
`w = z - ⟪z, v⟫ • v` is the orthogonal projection of `z` onto `v^⊥`, so `⟪z, w⟫ = ‖w‖²`. -/
lemma inner_self_sub_smul (z v : Space) (hv : ‖v‖ = 1) :
    inner ℝ z (z - (inner ℝ z v) • v) = ‖z - (inner ℝ z v) • v‖ ^ 2 := by
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  set n := inner ℝ z v with hn
  set w := z - n • v with hw
  have horth : inner ℝ w v = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, hv1, hn]
    ring
  have horth' : inner ℝ v w = 0 := by rw [real_inner_comm]; exact horth
  have hz : z = w + n • v := by rw [hw]; abel
  rw [hz, inner_add_left, real_inner_smul_left, horth', mul_zero, add_zero,
    real_inner_self_eq_norm_sq]

/-- The base point's height in the direction `chartUp` is `‖chartUp‖` (for a unit `v`). -/
lemma inner_shiftedNeedle_chartUp (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε)
      (chartUp r D lam δ₁ δ₂ ε v) = ‖chartUp r D lam δ₁ δ₂ ε v‖ ^ 2 := by
  rw [chartUp, nCoord]
  exact inner_self_sub_smul _ _ hv

/-- **The chart datum of the shifted needle.**  The frame `(e, v)` (`e` up, `v` along the chord), the
level `y₀` of the centre below the base point, the single-ray condition and the positivity of the
angular velocity — exactly the clauses of `Work.Drive.FlatteningCore` in the chart
`(nCoord, nHeight)`.

Note the two refinements over the `≤` form (`Submission/Work/Drive/NOTES_chart_STRICT.md`): the ray
clause is asked in the **strict** form `nHeight t < h₀ - y₀`, which makes the clause `M t ≠ c'`
(`hne`) *automatic* (`M t = c'` would force `nHeight t = h₀ - y₀`), and consequently the clause "the
needle lies above the chord's line" is *not* part of the datum: it is not needed. -/
def ShiftedNeedleChartData (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε : ℝ) : Prop :=
  ∃ e v : Space, ∃ y₀ : ℝ,
    ‖e‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ e v = 0 ∧
    0 < ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ ∧
    chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
      = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v ∧
    0 < y₀ ∧ y₀ < nHeight r D lam δ₁ δ₂ ε e 0 ∧
    (∀ t : ℝ, 0 < t → t < period → nCoord r D lam δ₁ δ₂ ε v t = nCoord r D lam δ₁ δ₂ ε v 0 →
      nHeight r D lam δ₁ δ₂ ε e t < nHeight r D lam δ₁ δ₂ ε e 0 - y₀) ∧
    (∀ t : ℝ, 0 < (nHeight r D lam δ₁ δ₂ ε e t - nHeight r D lam δ₁ δ₂ ε e 0 + y₀) *
          deriv (nCoord r D lam δ₁ δ₂ ε v) t
        - (nCoord r D lam δ₁ δ₂ ε v t - nCoord r D lam δ₁ δ₂ ε v 0) *
          deriv (nHeight r D lam δ₁ δ₂ ε e) t)

/-- **The needle pin in chart form** — the uniform-in-the-box version of
`Work.Drive.ShiftedNeedleChartData`.

The avoidance hypothesis `havoid` (`O`-avoidance of the band arc) is an *argument* of the pin and
not part of `ShiftedNeedleChartData`: the chart datum is *false* for a wild band arc, and every proof
of it in this lane goes through the O-avoidance.  This mirrors
`Work.Drive.needleStarShapedDataProved`, whose pin is a theorem *with* `havoid`. -/
def NeedleShiftedChartPin (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      LeanEval.KnotTheory.Quadrisecant.mobiusCover
        ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉
        LeanEval.KnotTheory.Quadrisecant.trisecantSet r) : Prop :=
  ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
    ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
      0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
      ShiftedNeedleChartData r D lam δ₁ δ₂ ε

end Work.Drive
