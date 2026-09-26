import Mathlib
import Submission.BandArcCover
import Submission.Work.Drive.cInfKnot

/-!
# The chord sweep: data and the raw loop family

This module sets up the objects of the "sweep through embeddings" proof of
`Work.Drive.unknotted_of_chordSweep`: from an `O`-avoiding non-separating band arc of a
smooth knot `r` we build the family of loops

    K_σ := (the arc of the knot from `a σ` to `b σ`) ∪ (the chord from `r (a σ)` to `r (b σ)`),

which sweeps from the whole knot (`σ = 1`, where the retained arc is everything and the chord
is degenerate) to a small "needle" (`σ → 0`, where both the arc and the chord shrink).  Each
`K_σ` is a simple closed curve: the retained arc is a sub-arc of `K`, and the chord meets `K`
only at its endpoints — that is exactly the `O`-avoidance hypothesis (`IsMiddleOnChord`).

The parameterization used is `t ↦ K_σ` with `t` running over one `period`, split as
`t/(2π) mod 1 ∈ [0,1/2]` for the arc side and `∈ [1/2,1]` for the chord side (traversed back
from `b σ` to `a σ`).  The corners of this piecewise curve are removed by convolution in `t`
with a smooth bump (`Work.Drive.sweepSmooth`), and the parameter `σ` is smoothed similarly.

## Main definitions

* `Work.Drive.SweepData d` — continuous real lifts `ta`, `tb` of the two branches `d.a`, `d.b`
  of a band arc, with `ta 0 = tb 0` and `tb 1 = ta 1 + period` (the non-separating condition).
* `Work.Drive.sweepParam` — the loop parameter `t ↦ (t/(2π) mod 1)`.
* `Work.Drive.sweepArc r ta tb s ξ` / `Work.Drive.sweepChord r ta tb s ξ` — the arc side and the
  chord side of the loop at fraction `ξ`.
* `Work.Drive.sweepLoop r ta tb s t` — the raw (piecewise smooth) loop, `period`-periodic in `t`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-! ## `knotMap` on real parameters -/

/-- For a `period`-periodic curve, `knotMap r` of the class of `x` is `r x`. -/
lemma knotMap_coe' {r : ℝ → Space} (hper : Function.Periodic r period) (x : ℝ) :
    knotMap r (x : AddCircle period) = r x := by
  obtain ⟨t, ht, htx⟩ := AddCircle.eq_coe_Ico (p := period) (x : AddCircle period)
  have hz : ((x - t : ℝ) : AddCircle period) = (0 : AddCircle period) := by
    rw [AddCircle.coe_sub, ← htx, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := period)).mp hz
  have hk' : (k : ℝ) * period = x - t := by simpa using hk
  have hx : x = t + (k : ℝ) * period := by linarith
  have hcls : (x : AddCircle period) = (t : AddCircle period) := htx.symm
  rw [hcls, knotMap_coe r ht, hx]
  have hper' : r (t + (k : ℝ) * period) = r t := by
    have h := hper.sub_int_mul_eq (x := t) (-k)
    simpa using h
  rw [hper']

/-! ## The raw sweep loop -/

/-- Lifts of the two branches of a band arc: continuous `ta`, `tb` with `ta 0 = tb 0` (the
collapsed left end) and `tb 1 = ta 1 + period` (the non-separating condition). -/
structure SweepData (d : BandArcData) where
  ta : I → ℝ
  tb : I → ℝ
  cont_ta : Continuous ta
  cont_tb : Continuous tb
  lift_a : ∀ s : I, (ta s : AddCircle period) = d.a s
  lift_b : ∀ s : I, (tb s : AddCircle period) = d.b s
  left_eq : ta 0 = tb 0
  right_eq : tb 1 = ta 1 + period

/-- The width `w σ = tb σ - ta σ` of the retained arc. -/
def sweepW {d : BandArcData} (D : SweepData d) (s : I) : ℝ := D.tb s - D.ta s

/-- The point at fraction `ξ` along the retained arc from `r (a σ)` to `r (b σ)`. -/
def sweepArc (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) (ξ : ℝ) : Space :=
  r (D.ta s + ξ * sweepW D s)

/-- The point at fraction `ξ` of the chord from `r (a σ)` to `r (b σ)`. -/
def sweepChord (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) (ξ : ℝ) : Space :=
  (1 - ξ) • r (D.ta s) + ξ • r (D.tb s)

/-- The loop parameter: `t ↦ t/(2π) mod 1`, valued in `[0,1)`. -/
def sweepParam (t : ℝ) : ℝ := t / period - ⌊t / period⌋

lemma sweepParam_mem (t : ℝ) : sweepParam t ∈ Set.Ico (0 : ℝ) 1 := by
  have hT : (0 : ℝ) < period := period_pos
  have h1 : ((⌊t / period⌋ : ℤ) : ℝ) ≤ t / period := Int.floor_le _
  have h2 : t / period < ((⌊t / period⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨?_, ?_⟩
  · simp only [sweepParam]; linarith
  · simp only [sweepParam]; linarith

lemma sweepParam_add_period (t : ℝ) : sweepParam (t + period) = sweepParam t := by
  have hT : (0 : ℝ) < period := period_pos
  have : (t + period) / period = t / period + 1 := by field_simp
  rw [sweepParam, sweepParam, this]
  have hfloor : ⌊t / period + 1⌋ = ⌊t / period⌋ + 1 := Int.floor_add_one _
  rw [hfloor]
  push_cast
  ring

lemma sweepParam_periodic : Function.Periodic sweepParam period := sweepParam_add_period

/-- The raw sweep loop: the retained arc for `t/(2π) mod 1 ∈ [0,1/2]` and the chord back for
`t/(2π) mod 1 ∈ [1/2,1]`.  This is `period`-periodic in `t` by construction. -/
def sweepLoop (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) (t : ℝ) : Space :=
  if sweepParam t ≤ 1 / 2 then sweepArc r D s (2 * sweepParam t)
  else sweepChord r D s (2 - 2 * sweepParam t)

lemma sweepArc_zero (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) :
    sweepArc r D s 0 = r (D.ta s) := by
  simp [sweepArc]

lemma sweepArc_one (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) :
    sweepArc r D s 1 = r (D.tb s) := by
  simp [sweepArc, sweepW]

lemma sweepChord_zero (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) :
    sweepChord r D s 0 = r (D.ta s) := by
  simp [sweepChord]

lemma sweepChord_one (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) :
    sweepChord r D s 1 = r (D.tb s) := by
  simp [sweepChord]

lemma sweepLoop_add_period (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) (t : ℝ) :
    sweepLoop r D s (t + period) = sweepLoop r D s t := by
  simp only [sweepLoop, sweepParam_add_period]

/-- The loop is `period`-periodic in `t`. -/
lemma sweepLoop_periodic (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) :
    Function.Periodic (sweepLoop r D s) period := sweepLoop_add_period r D s

/-- The arc side of the loop, as a map of the real parameter `ξ ∈ [0,1]`, is exactly the
restriction of `r` to the retained parameter interval. -/
lemma sweepArc_eq (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) (ξ : ℝ) :
    sweepArc r D s ξ = r (D.ta s + ξ * sweepW D s) := rfl


/-! ## The width of the retained arc -/

lemma sweepW_zero {d : BandArcData} (D : SweepData d) : sweepW D 0 = 0 := by
  simp [sweepW, D.left_eq]

lemma sweepW_one {d : BandArcData} (D : SweepData d) : sweepW D 1 = period := by
  simp [sweepW, D.right_eq]

/-- If the width vanishes, the two branch classes coincide (so `d.offdiag` fails). -/
lemma sweepW_eq_zero_class {d : BandArcData} (D : SweepData d) {t : I}
    (h : sweepW D t = 0) :
    (D.ta t : AddCircle period) = (D.tb t : AddCircle period) := by
  have h' : D.tb t - D.ta t = 0 := by simpa [sweepW] using h
  have hta : D.ta t = D.tb t := by linarith
  rw [hta]

/-- If the width equals a full period, the two branch classes coincide (so `d.offdiag` fails). -/
lemma sweepW_eq_period_class {d : BandArcData} (D : SweepData d) {t : I}
    (h : sweepW D t = period) :
    (D.ta t : AddCircle period) = (D.tb t : AddCircle period) := by
  have h' : D.tb t - D.ta t = period := by simpa [sweepW] using h
  have ht : D.tb t = D.ta t + period := by linarith
  rw [ht, AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- **The retained arc is a proper sub-arc of the knot**: at every interior parameter the width
`w σ = tb σ - ta σ` lies strictly between `0` and `period`.  (`w 0 = 0`, `w 1 = period`, `w` is
continuous, and `d.offdiag` forbids `w ∈ period·ℤ` in the interior; the intermediate value
theorem then forces `0 < w σ < period`.) -/
lemma sweepW_pos_lt {d : BandArcData} (D : SweepData d) :
    ∀ s : I, (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 → 0 < sweepW D s ∧ sweepW D s < period := by
  have hcont : Continuous (sweepW D) := D.cont_tb.sub D.cont_ta
  have h0 : sweepW D 0 = 0 := sweepW_zero D
  have h1 : sweepW D 1 = period := sweepW_one D
  intro s hs
  constructor
  · by_contra hcon
    push_neg at hcon
    have hS : IsPreconnected (Set.Icc s (1 : I)) :=
      isPreconnected_iff_ordConnected.mpr Set.ordConnected_Icc
    have hmem : (0 : ℝ) ∈ Set.Icc (sweepW D s) (sweepW D 1) := by
      rw [h1]; exact ⟨hcon, period_pos.le⟩
    have himg := hS.intermediate_value (Set.mem_Icc.mpr ⟨le_rfl, s.2.2⟩)
      (Set.mem_Icc.mpr ⟨s.2.2, le_rfl⟩) hcont.continuousOn hmem
    obtain ⟨t, ht, htw⟩ := himg
    have htle : (s : ℝ) ≤ (t : ℝ) := ht.1
    have ht0 : (t : ℝ) ≠ 0 := by
      intro h
      have : (0 : ℝ) < (s : ℝ) := hs.1
      rw [h] at htle
      linarith
    have ht1 : (t : ℝ) ≠ 1 := by
      intro h
      have ht' : t = (1 : I) := Subtype.ext (show (t : ℝ) = (1 : ℝ) from h)
      have hwt : sweepW D t = period := by rw [ht']; exact h1
      rw [htw] at hwt
      exact period_ne_zero hwt.symm
    refine d.offdiag t ht0 ht1 ?_
    rw [← D.lift_a t, ← D.lift_b t]
    exact sweepW_eq_zero_class D htw
  · by_contra hcon
    push_neg at hcon
    have hS : IsPreconnected (Set.Icc (0 : I) s) :=
      isPreconnected_iff_ordConnected.mpr Set.ordConnected_Icc
    have hmem : period ∈ Set.Icc (sweepW D 0) (sweepW D s) := by
      rw [h0]; exact ⟨period_pos.le, hcon⟩
    have himg := hS.intermediate_value (Set.mem_Icc.mpr ⟨le_rfl, s.2.1⟩)
      (Set.mem_Icc.mpr ⟨s.2.1, le_rfl⟩) hcont.continuousOn hmem
    obtain ⟨t, ht, htw⟩ := himg
    have htge : (t : ℝ) ≤ (s : ℝ) := ht.2
    have ht0 : (t : ℝ) ≠ 0 := by
      intro h
      have ht' : t = (0 : I) := Subtype.ext (show (t : ℝ) = (0 : ℝ) from h)
      have hwt : sweepW D t = 0 := by rw [ht']; exact h0
      rw [htw] at hwt
      exact period_ne_zero hwt
    have ht1 : (t : ℝ) ≠ 1 := by
      intro h
      have : (s : ℝ) < 1 := hs.2
      rw [h] at htge
      linarith
    refine d.offdiag t ht0 ht1 ?_
    rw [← D.lift_a t, ← D.lift_b t]
    exact sweepW_eq_period_class D htw


/-- **The non-separating condition supplies the sweep lifts.** -/
theorem BandArcNonSeparating.exists_sweepData {d : BandArcData}
    (h : BandArcNonSeparating d) : Nonempty (SweepData d) := by
  obtain ⟨ta, tb, hca, hcb, hma, hmb, h00, h11⟩ := h
  exact ⟨{ ta := ta, tb := tb, cont_ta := hca, cont_tb := hcb, lift_a := hma,
           lift_b := hmb, left_eq := h00, right_eq := h11 }⟩

end Work.Drive
