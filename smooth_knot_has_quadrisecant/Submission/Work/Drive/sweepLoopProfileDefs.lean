import Mathlib
import Submission.Work.Drive.chordSweepSmooth

/-!
# The chamfered sweep loop as a function of its profile

`Work.Drive.sweepLoopChamfer r D lam s t` is written in terms of the *profile*
`u = sweepParam t = t / period - ⌊t / period⌋ ∈ [0,1)`, and is `period`-periodic in `t`.  For the
estimate of the smoothed family against the raw loop it is convenient to have the same loop with
the profile as the *variable*:

* `Work.Drive.sweepLoopProfile r D lam s w` — identical piecewise formula, with the profile `w`
  in place of `sweepParam t`.  No floors appear.
* `Work.Drive.sweepLoopProfile_eq_chamfer` — for `0 < lam < 1` and `w ∈ [0,1]`,
  `sweepLoopChamfer r D lam s (period * w) = sweepLoopProfile r D lam s w`.
* `Work.Drive.sweepLoopChamfer_eq_profile` — for every real `t`,
  `sweepLoopChamfer r D lam s t = sweepLoopProfile r D lam s (sweepParam t)`.

The two ends of the profile interval carry the same point:
`Work.Drive.sweepLoopProfile_zero` and `Work.Drive.sweepLoopProfile_one`.
-/

/-
## Notes for proving uniform-continuity estimates about `sweepLoopProfile`

`r` is only assumed *continuous* (no Lipschitz bound, no differentiability).  Two quantitative
facts about `sweepLoopProfile r D lam s w` are wanted, each *uniform* in `lam ∈ (0,1/4]` and in
the other variable; they are the `Drive/sweepLoopProfile_uniformCont_loop` and
`Drive/sweepLoopProfile_uniformCont_sweep` requests.

### Ingredients

* **Boundedness of the evaluations.**  `taR D`, `tbR D` factor through the compact `I`, so there is
  `A` with `|taR D x| ≤ A` and `|tbR D x| ≤ A` for all `x` (use
  `isCompact_univ.exists_bound_of_continuousOn` on `I`, as in
  `sweepLoopChamfer_locallyIntegrable`).  Hence every real argument at which `r` is evaluated by
  the loop lies in the fixed compact interval `[-3A, 3A]` — arc points are `r (taR + ξ (tbR-taR))`
  with `ξ ∈ [0,1]`, chord points are evaluations at `taR`, `tbR`.  Consequently the estimates only
  ever need the *uniform continuity of `r` on `[-3A,3A]`*
  (`isCompact_Icc.uniformContinuousOn_of_continuous`), with a modulus `ω` that is *independent of
  everything else*.
* **The four branches** (for `0 < lam ≤ 1/4` the breakpoints are ordered
  `1/2 ≤ 1/2 + lam/2 ≤ 1 - lam/2 ≤ 1`):
  1. `w ≤ 1/2`: `sweepArc' r D s (lam + (1-2*lam) * (2*w))`, an arc point at fraction in
     `[lam, 1-lam]`; the fraction is affine in `w` with slope `2*(1-2*lam) ∈ [1,2]`.
  2. `1/2 ≤ w ≤ 1/2 + lam/2`:  `(1-s) • A + s • B` with `s = (2*w-1)/lam ∈ [0,1]` and the *fixed*
     points `A = sweepArc' r D s (1-lam)`, `B = sweepChord' r D s (1-lam)`.
  3. `1/2 + lam/2 ≤ w ≤ 1 - lam/2`: a chord point at fraction
     `(1-lam) - ((w - (1/2+lam/2))/(1/2-lam))*(1-2*lam)`, which runs over `[lam, 1-lam]`; the
     fraction is affine in `w` with slope `(1-2*lam)/(1/2-lam) ∈ [1,2]` for `lam ≤ 1/4`.
  4. `1 - lam/2 ≤ w`: `(1-s) • A' + s • B'` with `s = (w-(1-lam/2))/(lam/2) ∈ [0,1]`,
     `A' = sweepChord' r D s lam`, `B' = sweepArc' r D s lam` (the mirror image of branch 2).
* **Junction agreement** (essential: the loop is continuous although `lam`-dependent breakpoints
  move).  At `w = 1/2` branches 1 and 2 agree (`s = 0` gives `sweepArc' r D s (1-lam)`, which is
  branch 1 at `w = 1/2`); at `w = 1/2+lam/2` branches 2 and 3 agree (both `sweepChord' r D s
  (1-lam)`); at `w = 1-lam/2` branches 3 and 4 agree (both `sweepChord' r D s lam`); at
  `w = 0` and `w = 1` the loop is `sweepArc' r D s lam` (`sweepLoopProfile_zero`,
  `sweepLoopProfile_one`).  In general, *straddling a breakpoint* is handled by the triangle
  inequality through the junction value, both pieces being estimated with the same bound.

### The two requested estimates

* **In the sweep variable `σ`** (easier): `lam` and `w` are the same on both sides, so the branch
  and the weights are the same; only the evaluations `taR D (σ ± h)`, `tbR D (σ ± h)` move, by at
  most the (uniform) continuity modulus of `taR D`, `tbR D` (they are continuous functions of the
  clamped parameter, hence uniformly continuous on `ℝ`).  Every branch difference is then bounded
  by `ω` evaluated at `O(1) · |σ - σ'|` (a convex combination with the same weights of two
  differences, or a single difference).
* **In the loop variable `w`**: on branches 1 and 3 the fractions change by `O(|w-w'|)`, so the
  bound is `ω(O(|w-w'|))`.  On branches 2 and 4 the weights change by
  `|s - s'| ≤ 2|w-w'|/lam`, so the difference is `≤ min(1, 2|w-w'|/lam) · ‖B - A‖`.  The crucial
  bound is
  `‖B - A‖ = ‖sweepChord' r D s (1-lam) - sweepArc' r D s (1-lam)‖
     ≤ lam * ‖r (taR) - r (tbR)‖ + ω(lam * |sweepW'|)`, i.e. `O(lam) + ω(O(lam))`,
  because the chord point at fraction `1-lam` is within `lam * (chord length)` of `r (tbR)` and the
  arc point is `r (tbR - lam * sweepW')`.  Hence the branch-2/4 contribution is
  `min(1, 2d/lam) * B(lam)` with `B(lam) := C * lam + ω(C * lam) → 0` as `lam → 0`.
  Uniformity in `lam` is obtained by a two-stage choice (this is the one place where a little care
  is needed): fix a threshold `d₀` with `B(d₀) ≤ ε/2`, then choose the profile window `θ` so small
  that both `θ ≤ d₀/2` and `(2θ/ (d₀/2)) * (sup of B) ≤ ε/2`.  Concretely: for `lam ≤ d₀` the
  contribution is `≤ B(lam) ≤ B(d₀) ≤ ε/2`; for `lam ≥ d₀` it is
  `≤ (2θ/lam) * B(lam) ≤ (2θ/d₀) * B(1/4)`, which is `≤ ε/2` for `θ` small.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-- **The chamfered sweep loop, as a function of the profile `w`.**  This is `sweepLoopChamfer`
with `sweepParam t` replaced by the variable `w`; for `w ∈ [0,1]` the profile coordinate of
`sweepLoopProfile r D lam s w` in the loop is `w`. -/
def sweepLoopProfile (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam s w : ℝ) : Space :=
  if w ≤ 1 / 2 then sweepArc' r D s (lam + (1 - 2 * lam) * (2 * w))
  else if w ≤ 1 / 2 + lam / 2 then
    (1 - (2 * w - 1) / lam) • sweepArc' r D s (1 - lam)
      + ((2 * w - 1) / lam) • sweepChord' r D s (1 - lam)
  else if w ≤ 1 - lam / 2 then
    sweepChord' r D s ((1 - lam) - ((w - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
  else
    (1 - (w - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
      + ((w - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam

/-- `sweepLoopChamfer` is `period`-periodic in the loop parameter (local copy, to keep this module
light). -/
lemma sweepLoopChamfer_isPeriodic (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : Function.Periodic (fun t : ℝ => sweepLoopChamfer r D lam s t) period :=
  fun t => by simp only [sweepLoopChamfer, sweepParam_add_period]

lemma sweepParam_mul_period (w : ℝ) : sweepParam (period * w) = w - ⌊w⌋ := by
  rw [sweepParam, mul_div_cancel_left₀ w period_ne_zero]

/-- The profile of the loop parameter zero. -/
lemma sweepParam_zero : sweepParam 0 = 0 := by simp [sweepParam]

/-- At the profile `w = 0` the loop sits at the point at fraction `lam` of the retained arc. -/
lemma sweepLoopProfile_zero (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam s : ℝ) :
    sweepLoopProfile r D lam s 0 = sweepArc' r D s lam := by
  rw [sweepLoopProfile, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

/-- At the profile `w = 1` the loop returns to the same point, `sweepArc' r D s lam`: the profile
loop is a closed curve on `[0,1]`. -/
lemma sweepLoopProfile_one {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < 1) (s : ℝ) :
    sweepLoopProfile r D lam s 1 = sweepArc' r D s lam := by
  rw [sweepLoopProfile, if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2)),
    if_neg (by linarith : ¬ ((1 : ℝ) ≤ 1 / 2 + lam / 2)),
    if_neg (by linarith : ¬ ((1 : ℝ) ≤ 1 - lam / 2))]
  have h5 : (1 : ℝ) - (1 - lam / 2) = lam / 2 := by ring
  rw [h5, div_self (by linarith : lam / 2 ≠ 0), one_smul, sub_self, zero_smul, zero_add]

/-- The chamfered loop at the loop parameter zero is the point at fraction `lam` of the retained
arc. -/
lemma sweepLoopChamfer_zero (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam s : ℝ) :
    sweepLoopChamfer r D lam s 0 = sweepArc' r D s lam := by
  rw [sweepLoopChamfer, sweepParam_zero]
  rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

/-- **The profile loop is the chamfered loop.**  For `0 < lam < 1` and profile `w ∈ [0,1]`,
`sweepLoopProfile r D lam s w` is the chamfered loop at the loop parameter `period * w`. -/
lemma sweepLoopProfile_eq_chamfer {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {s w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    sweepLoopChamfer r D lam s (period * w) = sweepLoopProfile r D lam s w := by
  rcases lt_or_eq_of_le hw.2 with hwlt | hweq
  · have hfloor : ⌊w⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hw.1, hwlt⟩
    rw [sweepLoopChamfer, sweepLoopProfile, sweepParam_mul_period, hfloor, Int.cast_zero, sub_zero]
  · subst hweq
    have hper : sweepLoopChamfer r D lam s (period * 1) = sweepLoopChamfer r D lam s 0 := by
      have h := (sweepLoopChamfer_isPeriodic r D lam s) 0
      simp only [zero_add] at h
      rw [mul_one]
      exact h
    rw [hper, sweepLoopChamfer_zero r D lam s, sweepLoopProfile_one D h0 h1 s]

/-- **Every point of the chamfered loop is a point of the profile loop at its profile.** -/
lemma sweepLoopChamfer_eq_profile (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (s t : ℝ) :
    sweepLoopChamfer r D lam s t = sweepLoopProfile r D lam s (sweepParam t) := by
  obtain ⟨hu0, hu1⟩ := sweepParam_mem t
  have hper : sweepLoopChamfer r D lam s (period * sweepParam t) = sweepLoopChamfer r D lam s t := by
    have h := (sweepLoopChamfer_isPeriodic r D lam s).sub_int_mul_eq
      (x := t) ⌊t / period⌋
    have harg : period * sweepParam t = t - (⌊t / period⌋ : ℤ) * period := by
      rw [sweepParam, mul_sub, mul_div_cancel₀ t period_ne_zero]
      ring
    rw [harg]
    exact h
  rw [← hper, sweepLoopProfile_eq_chamfer D h0 h1 ⟨hu0, hu1.le⟩]

end Work.Drive
