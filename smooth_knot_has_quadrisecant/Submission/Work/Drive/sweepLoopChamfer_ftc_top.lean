import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.sweepTopTools
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable
import Submission.Work.Drive.sweepLoop_injective
import Submission.Work.Drive.chordSweepDefs

/-!
# The FTC along the chamfered sweep loop, stated with `topLoopVel` (cycle-free, self-contained)

Restatement of `Submission/Work/Drive/sweepLoopChamfer_ftc.lean` with the loop-parameter velocity
written as `Work.Drive.topLoopVel` (from `sweepTopTools.lean`).  This file imports **neither**
`sweepWindowKnots` (where `sweepLoopChamferDeriv` lives) **nor** `sweepFam_slices_knots` (which
declares `sweepLoopChamfer_continuous_tTop`, clashing with `sweepFam_close_chamfer`, a dependency of
the local/far pins of the assembly).  The four items borrowed from `sweepFam_slices_knots` are
copied here under `…Top` names: `sweepUnwrapTop`, `sweepLoopChamfer_eq_unwrapTop`,
`sweepUnwrap_continuousTop`, `sweepLoopChamfer_continuous_tTop`; all other declarations are
`…Top`-suffixed copies of the original file's, so the two files coexist.
-/


noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

variable {r : ℝ → Space} {d : BandArcData}

/-- Local copy of `Work.Drive.sweepUnwrap`. -/
noncomputable def sweepUnwrapTop (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s u : ℝ) : Space :=
  if u ≤ 1 / 2 then sweepArc' r D s (lam + (1 - 2 * lam) * (2 * u))
  else if u ≤ 1 / 2 + lam / 2 then
    (1 - (2 * u - 1) / lam) • sweepArc' r D s (1 - lam)
      + ((2 * u - 1) / lam) • sweepChord' r D s (1 - lam)
  else if u ≤ 1 - lam / 2 then
    sweepChord' r D s ((1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
  else
    (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
      + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam

/-- `sweepLoopChamfer` is the local unwrapped loop composed with the profile parameter. -/
lemma sweepLoopChamfer_eq_unwrapTop (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s t : ℝ) :
    sweepLoopChamfer r D lam s t = sweepUnwrapTop r D lam s (sweepParam t) := rfl

/-! ## The four branch values of the derivative with respect to the profile

These are the derivatives of the four branches of `sweepUnwrapTop` with respect to the profile
variable `u` (note the extra `1 / period` relating this to the loop parameter `t`). -/

/-- First branch value: the derivative of the arc side. -/
noncomputable def sweepBranch1Top (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s u : ℝ) : Space :=
  (2 * (1 - 2 * lam)) •
    ((sweepW' D s) • deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s))

/-- Second branch value: the derivative of the first chamfer. -/
noncomputable def sweepBranch2Top (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : Space :=
  (2 / lam) • (sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam))

/-- Third branch value: the derivative of the chord side. -/
noncomputable def sweepBranch3Top (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : Space :=
  (-(1 - 2 * lam) / (1 / 2 - lam)) • (r (tbR D s) - r (taR D s))

/-- Fourth branch value: the derivative of the second chamfer. -/
noncomputable def sweepBranch4Top (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : Space :=
  (2 / lam) • (sweepArc' r D s lam - sweepChord' r D s lam)

/-- The right derivative of the unwrapped loop, as a function of the profile `u`. -/
noncomputable def sweepUnwrapDerivTop (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s u : ℝ) : Space :=
  if u < 1 / 2 then sweepBranch1Top r D lam s u
  else if u < 1 / 2 + lam / 2 then sweepBranch2Top r D lam s
  else if u < 1 - lam / 2 then sweepBranch3Top r D lam s
  else sweepBranch4Top r D lam s

/-- The right derivative of the chamfered loop with respect to its loop parameter. -/
noncomputable def sweepLoopChamferDerivRTop (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun t => (1 / period) • sweepUnwrapDerivTop r D lam s (sweepParam t)

/-! ## The four branches of `sweepUnwrapTop`, as explicit functions of the profile -/

noncomputable def sweepphi1Top (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun u => sweepArc' r D s (lam + (1 - 2 * lam) * (2 * u))

noncomputable def sweepphi2Top (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun u => (1 - (2 * u - 1) / lam) • sweepArc' r D s (1 - lam)
    + ((2 * u - 1) / lam) • sweepChord' r D s (1 - lam)

noncomputable def sweepphi3Top (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun u =>
    sweepChord' r D s ((1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))

noncomputable def sweepphi4Top (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun u => (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
    + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam

theorem sweepUnwrap_continuousTop (r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space)
    (hr : Continuous r) {d : LeanEval.KnotTheory.Quadrisecant.BandArcData}
    (D : Work.Drive.SweepData d) {lam s : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    Continuous (fun u : ℝ => Work.Drive.sweepUnwrapTop r D lam s u) := by
  have hA : Continuous (fun u : ℝ => sweepArc' r D s (lam + (1 - 2 * lam) * (2 * u))) := by
    simp only [sweepArc']
    exact hr.comp (by fun_prop)
  have hB : Continuous (fun u : ℝ =>
      (1 - (2 * u - 1) / lam) • sweepArc' r D s (1 - lam)
        + ((2 * u - 1) / lam) • sweepChord' r D s (1 - lam)) := by
    have hconv : Continuous (fun t : ℝ =>
        (1 - t) • sweepArc' r D s (1 - lam) + t • sweepChord' r D s (1 - lam)) := by fun_prop
    exact hconv.comp (by fun_prop)
  have hC : Continuous (fun u : ℝ =>
      sweepChord' r D s ((1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))) := by
    have hcd : Continuous (fun ξ : ℝ => sweepChord' r D s ξ) := by
      simp only [sweepChord']; fun_prop
    exact hcd.comp (by fun_prop)
  have hD : Continuous (fun u : ℝ =>
      (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
        + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam) := by
    have hconv : Continuous (fun t : ℝ =>
        (1 - t) • sweepChord' r D s lam + t • sweepArc' r D s lam) := by fun_prop
    exact hconv.comp (by fun_prop)
  have hCD : Continuous (fun u : ℝ =>
      if u ≤ 1 - lam / 2 then
        sweepChord' r D s ((1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
      else
        (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
          + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam) := by
    refine Continuous.if_le (f := fun u : ℝ => u) (g := fun _ : ℝ => 1 - lam / 2)
      hC hD continuous_id continuous_const ?_
    intro x hx
    have hden : (1 / 2 - lam) ≠ 0 := by linarith
    have hd2 : 1 - lam * 2 ≠ 0 := by linarith
    have hξ : (1 - lam) - ((x - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam) = lam := by
      rw [hx]
      field_simp
      ring
    have hc : x - (1 - lam / 2) = 0 := by subst hx; ring
    rw [hξ, hc]
    simp
  have hBCD : Continuous (fun u : ℝ =>
      if u ≤ 1 / 2 + lam / 2 then
        (1 - (2 * u - 1) / lam) • sweepArc' r D s (1 - lam)
          + ((2 * u - 1) / lam) • sweepChord' r D s (1 - lam)
      else
        if u ≤ 1 - lam / 2 then
          sweepChord' r D s ((1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
        else
          (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
            + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam) := by
    refine Continuous.if_le (f := fun u : ℝ => u) (g := fun _ : ℝ => 1 / 2 + lam / 2)
      hB hCD continuous_id continuous_const ?_
    intro x hx
    have hx1 : 2 * x - 1 = lam := by rw [hx]; ring
    have hx2 : x - (1 / 2 + lam / 2) = 0 := by rw [hx]; ring
    rw [if_pos (by rw [hx]; linarith [hlam1] : x ≤ 1 - lam / 2), hx1, hx2]
    have hl : lam / lam = 1 := div_self (ne_of_gt hlam0)
    rw [hl]
    simp
  have hmain : Continuous (fun u : ℝ =>
      if u ≤ 1 / 2 then sweepArc' r D s (lam + (1 - 2 * lam) * (2 * u))
      else
        if u ≤ 1 / 2 + lam / 2 then
          (1 - (2 * u - 1) / lam) • sweepArc' r D s (1 - lam)
            + ((2 * u - 1) / lam) • sweepChord' r D s (1 - lam)
        else
          if u ≤ 1 - lam / 2 then
            sweepChord' r D s ((1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
          else
            (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
              + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam) := by
    refine Continuous.if_le (f := fun u : ℝ => u) (g := fun _ : ℝ => 1 / 2)
      hA hBCD continuous_id continuous_const ?_
    intro x hx
    have hx1 : lam + (1 - 2 * lam) * (2 * x) = 1 - lam := by rw [hx]; ring
    have hx2 : 2 * x - 1 = 0 := by rw [hx]; ring
    rw [if_pos (by rw [hx]; linarith [hlam0] : x ≤ 1 / 2 + lam / 2), hx1, hx2]
    simp
  exact hmain

theorem sweepLoopChamfer_continuous_tTop {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : Continuous r) {d : LeanEval.KnotTheory.Quadrisecant.BandArcData}
    (D : Work.Drive.SweepData d) {lam s : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    Continuous (fun t : ℝ => Work.Drive.sweepLoopChamfer r D lam s t) := by
  have hG : Continuous (fun u : ℝ => Work.Drive.sweepUnwrapTop r D lam s u) :=
    sweepUnwrap_continuousTop r hr D hlam0 hlam1
  have hper : (0:ℝ) < period := period_pos
  have hhalflam : lam / 2 ≠ 0 := by linarith
  -- the wrap agreement `G 1 = G 0`, both equal to `sweepArc' r D s lam`
  have hG1 : Work.Drive.sweepUnwrapTop r D lam s 1 = sweepArc' r D s lam := by
    have h3 : ¬ (1:ℝ) ≤ 1 / 2 := by norm_num
    have h4 : ¬ (1:ℝ) ≤ 1 / 2 + lam / 2 := by linarith
    have h5 : ¬ (1:ℝ) ≤ 1 - lam / 2 := by linarith
    rw [Work.Drive.sweepUnwrapTop, if_neg h3, if_neg h4, if_neg h5,
      show (1:ℝ) - (1 - lam / 2) = lam / 2 by ring, div_self hhalflam]
    simp
  have hG0 : Work.Drive.sweepUnwrapTop r D lam s 0 = sweepArc' r D s lam := by
    rw [Work.Drive.sweepUnwrapTop, if_pos (by norm_num : (0:ℝ) ≤ 1 / 2),
      show lam + (1 - 2 * lam) * (2 * 0) = lam by ring]
  have hwrap : Work.Drive.sweepUnwrapTop r D lam s 1 = Work.Drive.sweepUnwrapTop r D lam s 0 := by
    rw [hG1, hG0]
  -- `Φ x = G (x/period - k)` on each closed interval `[k·period, k·period + period]`
  have key : ∀ k : ℤ, ContinuousOn (fun t : ℝ => Work.Drive.sweepUnwrapTop r D lam s (sweepParam t))
      (Set.Icc ((k : ℝ) * period) ((k : ℝ) * period + period)) := by
    intro k
    have hFk : Continuous (fun x : ℝ => Work.Drive.sweepUnwrapTop r D lam s (x / period - (k : ℝ))) :=
      hG.comp (by fun_prop)
    refine hFk.continuousOn.congr ?_
    intro x hx
    rw [Set.mem_Icc] at hx
    change Work.Drive.sweepUnwrapTop r D lam s (sweepParam x)
      = Work.Drive.sweepUnwrapTop r D lam s (x / period - (k : ℝ))
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · -- `x` in the half-open period `[k·period, (k+1)·period)`
      have hshift : sweepParam x = sweepParam (x - (k : ℝ) * period) :=
        (sweepParam_periodic.sub_int_mul_eq k).symm
      have hmem : x - (k : ℝ) * period ∈ Set.Ico (0 : ℝ) period := by
        constructor
        · linarith [hx.1]
        · linarith [hlt]
      rw [hshift, sweepParam_eq_div hmem, sub_div, mul_div_assoc, div_self period_ne_zero, mul_one]
    · -- the right endpoint
      have hx2 : x = (k : ℝ) * period + period := heq
      have hshift : sweepParam x = 0 := by
        have h1 : x = ((k + 1 : ℤ) : ℝ) * period := by push_cast; linarith
        rw [h1, sweepParam_periodic.int_mul_eq (k + 1)]
        simp [sweepParam]
      rw [hshift, hx2]
      have hk : ((k : ℝ) * period + period) / period - (k : ℝ) = 1 := by
        rw [add_div, mul_div_assoc, div_self period_ne_zero, mul_one]
        ring
      rw [hk, hwrap]
  -- assemble: at `t` the function agrees with a continuous function on `Icc ((k-1)P) ((k+1)P)`
  rw [show (fun t : ℝ => Work.Drive.sweepLoopChamfer r D lam s t)
      = fun t : ℝ => Work.Drive.sweepUnwrapTop r D lam s (sweepParam t) from
    funext (fun t => sweepLoopChamfer_eq_unwrapTop r D lam s t)]
  rw [continuous_iff_continuousAt]
  intro t
  set k : ℤ := ⌊t / period⌋ with hkdef
  have hk1 : ((k : ℤ) : ℝ) ≤ t / period := by
    rw [hkdef]; exact Int.floor_le _
  have hk2 : t / period < ((k : ℤ) : ℝ) + 1 := by
    rw [hkdef]; exact Int.lt_floor_add_one _
  have hk1' : ((k : ℤ) : ℝ) * period ≤ t := by
    rw [le_div_iff₀ hper] at hk1; exact hk1
  have hk2' : t < (((k : ℤ) : ℝ) + 1) * period := by
    rw [div_lt_iff₀ hper] at hk2; exact hk2
  have hlt1 : ((k - 1 : ℤ) : ℝ) * period < t := by push_cast; nlinarith [hk1', hper]
  have hlt2 : t < ((k + 1 : ℤ) : ℝ) * period := by push_cast; nlinarith [hk2', hper]
  have hc1 : (((k - 1 : ℤ) : ℝ) * period + period) = ((k : ℤ) : ℝ) * period := by push_cast; ring
  have hc2 : (((k : ℤ) : ℝ) * period + period) = ((k + 1 : ℤ) : ℝ) * period := by push_cast; ring
  rcases lt_or_eq_of_le hk1' with hklt | hkeq
  · -- interior of the period: the interval `Icc (k·period) ((k+1)·period)` is a neighbourhood
    have h2 : t ∈ Set.Icc (((k : ℤ) : ℝ) * period) (((k : ℤ) : ℝ) * period + period) := by
      exact ⟨hk1', by rw [hc2]; exact hlt2.le⟩
    exact (key k).continuousAt (Icc_mem_nhds hklt (by rw [hc2]; exact hlt2))
  · -- a period boundary: both adjacent closed intervals are available and cover a neighbourhood
    have hmem1 : t ∈ Set.Icc (((k - 1 : ℤ) : ℝ) * period) (((k - 1 : ℤ) : ℝ) * period + period) := by
      refine ⟨hlt1.le, ?_⟩; rw [hc1]; exact hkeq.ge
    have hmem2 : t ∈ Set.Icc (((k : ℤ) : ℝ) * period) (((k : ℤ) : ℝ) * period + period) := by
      refine ⟨hkeq.le, ?_⟩; rw [hc2]; exact hlt2.le
    have h1 := (key (k - 1)).continuousWithinAt hmem1
    have h2 := (key k).continuousWithinAt hmem2
    have hunion := h1.union h2
    rw [show Set.Icc (((k - 1 : ℤ) : ℝ) * period) (((k - 1 : ℤ) : ℝ) * period + period)
          ∪ Set.Icc (((k : ℤ) : ℝ) * period) ((((k : ℤ) : ℝ) * period) + period)
        = Set.Icc (((k - 1 : ℤ) : ℝ) * period) (((k + 1 : ℤ) : ℝ) * period) by
      rw [hc1, hc2]
      exact Set.Icc_union_Icc_eq_Icc (by push_cast; nlinarith [hper]) (by push_cast; nlinarith [hper])] at hunion
    exact (continuousWithinAt_iff_continuousAt (Icc_mem_nhds hlt1 hlt2)).mp hunion

/-- `sweepUnwrapTop` is the `if`-chain of the four branch functions. -/
lemma sweepUnwrap_eq_iteTop (D : SweepData d) (lam s u : ℝ) :
    sweepUnwrapTop r D lam s u
      = if u ≤ 1 / 2 then sweepphi1Top r D lam s u
        else if u ≤ 1 / 2 + lam / 2 then sweepphi2Top r D lam s u
        else if u ≤ 1 - lam / 2 then sweepphi3Top r D lam s u
        else sweepphi4Top r D lam s u := by
  simp only [sweepUnwrapTop, sweepphi1Top, sweepphi2Top, sweepphi3Top, sweepphi4Top]

/-! ## Derivatives of the four branch functions -/

lemma hasDerivAt_sweepphi1Top {D : SweepData d} (hd : Differentiable ℝ r) (lam s u : ℝ) :
    HasDerivAt (sweepphi1Top r D lam s) (sweepBranch1Top r D lam s u) u := by
  change HasDerivAt (fun u' : ℝ => r (taR D s + (lam + (1 - 2 * lam) * (2 * u')) * sweepW' D s))
    (sweepBranch1Top r D lam s u) u
  have h0 : HasDerivAt
      (fun u' : ℝ => taR D s + (lam + (1 - 2 * lam) * (2 * u')) * sweepW' D s)
      (((1 - 2 * lam) * 2) * sweepW' D s) u := by
    have h1 : HasDerivAt (fun u' : ℝ => (1 - 2 * lam) * (2 * u')) ((1 - 2 * lam) * 2) u :=
      (((hasDerivAt_id u).const_mul 2).const_mul (1 - 2 * lam)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun u' : ℝ => lam + (1 - 2 * lam) * (2 * u')) ((1 - 2 * lam) * 2) u :=
      h1.const_add lam
    have h3 : HasDerivAt (fun u' : ℝ => (lam + (1 - 2 * lam) * (2 * u')) * sweepW' D s)
        (((1 - 2 * lam) * 2) * sweepW' D s) u := h2.mul_const (sweepW' D s)
    exact h3.const_add (taR D s)
  have hr : HasDerivAt r
      (deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s))
      (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s) :=
    (hd _).hasDerivAt
  refine (hr.scomp u h0).congr_deriv ?_
  simp only [sweepBranch1Top, smul_smul]
  congr 1
  ring

lemma hasDerivAt_sweepphi2Top {D : SweepData d} (lam s u : ℝ) :
    HasDerivAt (sweepphi2Top r D lam s) (sweepBranch2Top r D lam s) u := by
  have hw : HasDerivAt (fun u' : ℝ => (2 * u' - 1) / lam) (2 / lam) u := by
    have h : HasDerivAt (fun u' : ℝ => 2 * u' - 1) 2 u :=
      (((hasDerivAt_id u).const_mul 2).sub_const 1).congr_deriv (by ring)
    simpa using h.div_const lam
  have h1 : HasDerivAt (fun u' : ℝ => 1 - (2 * u' - 1) / lam) (0 - 2 / lam) u :=
    (hasDerivAt_const u 1).sub hw
  have h2 : HasDerivAt
      (fun u' : ℝ => (1 - (2 * u' - 1) / lam) • sweepArc' r D s (1 - lam))
      ((0 - 2 / lam) • sweepArc' r D s (1 - lam)) u :=
    h1.smul_const _
  have h3 : HasDerivAt
      (fun u' : ℝ => ((2 * u' - 1) / lam) • sweepChord' r D s (1 - lam))
      ((2 / lam) • sweepChord' r D s (1 - lam)) u :=
    hw.smul_const _
  have h4 := h2.add h3
  refine h4.congr_deriv ?_
  simp only [sweepBranch2Top]
  simp only [zero_sub, neg_smul, smul_sub]
  abel

lemma hasDerivAt_sweepphi3Top {D : SweepData d} (lam s u : ℝ) (hden : (1 / 2 : ℝ) - lam ≠ 0) :
    HasDerivAt (sweepphi3Top r D lam s) (sweepBranch3Top r D lam s) u := by
  have hg : HasDerivAt (fun u' : ℝ => (u' - (1 / 2 + lam / 2)) / (1 / 2 - lam))
      (1 / (1 / 2 - lam)) u := by
    have h : HasDerivAt (fun u' : ℝ => u' - (1 / 2 + lam / 2)) 1 u :=
      (hasDerivAt_id u).sub_const _
    simpa using h.div_const (1 / 2 - lam)
  have hξ : HasDerivAt
      (fun u' : ℝ => (1 - lam) - ((u' - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
      (-((1 / (1 / 2 - lam)) * (1 - 2 * lam))) u := by
    have h := (hg.mul_const (1 - 2 * lam)).const_sub (1 - lam)
    -- h : HasDerivAt (fun u => (1-lam) - (...)*(1-2lam)) (0 - (1/(1/2-lam))*(1-2lam)) u
    refine h.congr_deriv ?_
    ring
  have h1 : HasDerivAt (fun u' : ℝ => 1 -
        ((1 - lam) - ((u' - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)))
      (0 - -((1 / (1 / 2 - lam)) * (1 - 2 * lam))) u :=
    (hasDerivAt_const u 1).sub hξ
  have h2 : HasDerivAt (fun u' : ℝ => (1 -
        ((1 - lam) - ((u' - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))) • r (taR D s))
      ((0 - -((1 / (1 / 2 - lam)) * (1 - 2 * lam))) • r (taR D s)) u := h1.smul_const _
  have h3 : HasDerivAt (fun u' : ℝ =>
        ((1 - lam) - ((u' - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)) • r (tbR D s))
      ((-((1 / (1 / 2 - lam)) * (1 - 2 * lam))) • r (tbR D s)) u := hξ.smul_const _
  have h4 := h2.add h3
  refine h4.congr_deriv ?_
  rw [sweepBranch3Top]
  rw [show -(1 - 2 * lam) / (1 / 2 - lam) = -((1 / (1 / 2 - lam)) * (1 - 2 * lam)) by
    simp only [div_eq_mul_inv]
    ring]
  simp only [zero_sub, neg_neg, neg_smul, smul_sub]
  abel

lemma hasDerivAt_sweepphi4Top {D : SweepData d} (lam s u : ℝ) :
    HasDerivAt (sweepphi4Top r D lam s) (sweepBranch4Top r D lam s) u := by
  have hw : HasDerivAt (fun u' : ℝ => (u' - (1 - lam / 2)) / (lam / 2)) (1 / (lam / 2)) u := by
    have h : HasDerivAt (fun u' : ℝ => u' - (1 - lam / 2)) 1 u := (hasDerivAt_id u).sub_const _
    simpa using h.div_const (lam / 2)
  have h1 : HasDerivAt (fun u' : ℝ => 1 - (u' - (1 - lam / 2)) / (lam / 2))
      (0 - 1 / (lam / 2)) u := (hasDerivAt_const u 1).sub hw
  have h2 : HasDerivAt (fun u' : ℝ => (1 - (u' - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam)
      ((0 - 1 / (lam / 2)) • sweepChord' r D s lam) u := h1.smul_const _
  have h3 : HasDerivAt (fun u' : ℝ => ((u' - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam)
      ((1 / (lam / 2)) • sweepArc' r D s lam) u := hw.smul_const _
  have h4 := h2.add h3
  refine h4.congr_deriv ?_
  simp only [sweepBranch4Top]
  rw [show (2 / lam) = 1 / (lam / 2) by
    simp only [div_eq_mul_inv]
    ring]
  rw [zero_sub, neg_smul, smul_sub]
  abel

/-! ## The junction values of the branches -/

lemma sweepphi1_eq_sweepphi2_halfTop (D : SweepData d) (lam s : ℝ) :
    sweepphi1Top r D lam s (1 / 2) = sweepphi2Top r D lam s (1 / 2) := by
  simp only [sweepphi1Top, sweepphi2Top]
  have h2 : (2 : ℝ) * (1 / 2) - 1 = 0 := by norm_num
  have h3 : lam + (1 - 2 * lam) * (2 * (1 / 2)) = 1 - lam := by ring
  rw [h2, h3, zero_div]
  simp

lemma sweepphi2_eq_sweepphi3Top (D : SweepData d) {lam : ℝ} (_h0 : 0 < lam) (s : ℝ) :
    sweepphi2Top r D lam s (1 / 2 + lam / 2) = sweepphi3Top r D lam s (1 / 2 + lam / 2) := by
  simp only [sweepphi2Top, sweepphi3Top]
  have h2 : (2 * (1 / 2 + lam / 2) - 1) / lam = 1 := by
    field_simp
    ring
  have h3 : (1 - lam) - (((1 / 2 + lam / 2) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
      = 1 - lam := by
    rw [sub_self, zero_div, zero_mul, sub_zero]
  rw [h2, h3]
  simp

lemma sweepphi3_eq_sweepphi4Top (D : SweepData d) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (s : ℝ) :
    sweepphi3Top r D lam s (1 - lam / 2) = sweepphi4Top r D lam s (1 - lam / 2) := by
  simp only [sweepphi3Top, sweepphi4Top]
  have h3 : (1 - lam) - (((1 - lam / 2) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
      = lam := by
    have hd : (1 - lam / 2) - (1 / 2 + lam / 2) = 1 / 2 - lam := by ring
    rw [hd, div_self (by linarith : (1 / 2 : ℝ) - lam ≠ 0), one_mul]
    ring
  have h4 : ((1 - lam / 2) - (1 - lam / 2)) / (lam / 2) = 0 := by
    rw [sub_self, zero_div]
  rw [h3, h4]
  simp

/-! ## The right derivative of the unwrapped loop -/

theorem sweepUnwrap_hasDerivWithinAtTop {D : SweepData d} (hd : Differentiable ℝ r)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (s u : ℝ) :
    HasDerivWithinAt (fun u' => sweepUnwrapTop r D lam s u') (sweepUnwrapDerivTop r D lam s u)
      (Set.Ioi u) u := by
  rcases lt_trichotomy u (1 / 2) with h1 | h1 | h1
  · -- first branch
    have hder : HasDerivAt (sweepphi1Top r D lam s) (sweepBranch1Top r D lam s u) u :=
      hasDerivAt_sweepphi1Top (D := D) hd lam s u
    have hev : (fun u' => sweepUnwrapTop r D lam s u') =ᶠ[𝓝[>] u] sweepphi1Top r D lam s := by
      filter_upwards [Ioo_mem_nhdsGT h1] with u' hu'
      rw [sweepUnwrap_eq_iteTop, if_pos (le_of_lt hu'.2)]
    have hx : sweepUnwrapTop r D lam s u = sweepphi1Top r D lam s u := by
      rw [sweepUnwrap_eq_iteTop, if_pos (le_of_lt h1)]
    rw [show sweepUnwrapDerivTop r D lam s u = sweepBranch1Top r D lam s u by
      simp only [sweepUnwrapDerivTop]; rw [if_pos h1]]
    exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
  · -- junction at 1/2
    subst h1
    have hder : HasDerivAt (sweepphi2Top r D lam s) (sweepBranch2Top r D lam s) (1 / 2) :=
      hasDerivAt_sweepphi2Top (D := D) lam s (1 / 2)
    have hev : (fun u' => sweepUnwrapTop r D lam s u') =ᶠ[𝓝[>] (1 / 2 : ℝ)] sweepphi2Top r D lam s := by
      filter_upwards [Ioo_mem_nhdsGT (by linarith : (1 / 2 : ℝ) < 1 / 2 + lam / 2)] with u' hu'
      rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr hu'.1), if_pos (le_of_lt hu'.2)]
    have hx : sweepUnwrapTop r D lam s (1 / 2) = sweepphi2Top r D lam s (1 / 2) := by
      rw [sweepUnwrap_eq_iteTop, if_pos le_rfl]
      exact sweepphi1_eq_sweepphi2_halfTop D lam s
    rw [show sweepUnwrapDerivTop r D lam s (1 / 2) = sweepBranch2Top r D lam s by
      simp only [sweepUnwrapDerivTop]
      rw [if_neg (lt_irrefl _), if_pos (by linarith : (1 / 2 : ℝ) < 1 / 2 + lam / 2)]]
    exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
  · rcases lt_trichotomy u (1 / 2 + lam / 2) with h2 | h2 | h2
    · -- second branch
      have hder : HasDerivAt (sweepphi2Top r D lam s) (sweepBranch2Top r D lam s) u :=
        hasDerivAt_sweepphi2Top (D := D) lam s u
      have hev : (fun u' => sweepUnwrapTop r D lam s u') =ᶠ[𝓝[>] u] sweepphi2Top r D lam s := by
        filter_upwards [Ioo_mem_nhdsGT h2] with u' hu'
        rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr (lt_trans h1 hu'.1)), if_pos (le_of_lt hu'.2)]
      have hx : sweepUnwrapTop r D lam s u = sweepphi2Top r D lam s u := by
        rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr h1), if_pos (le_of_lt h2)]
      rw [show sweepUnwrapDerivTop r D lam s u = sweepBranch2Top r D lam s by
        simp only [sweepUnwrapDerivTop]
        rw [if_neg (not_lt.mpr h1.le), if_pos h2]]
      exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
    · -- junction at 1/2 + lam/2
      subst h2
      have hlt : (1 / 2 : ℝ) < 1 / 2 + lam / 2 := by linarith
      have hder : HasDerivAt (sweepphi3Top r D lam s) (sweepBranch3Top r D lam s) (1 / 2 + lam / 2) :=
        hasDerivAt_sweepphi3Top (D := D) lam s _ (by linarith)
      have hev : (fun u' => sweepUnwrapTop r D lam s u') =ᶠ[𝓝[>] (1 / 2 + lam / 2 : ℝ)]
          sweepphi3Top r D lam s := by
        filter_upwards [Ioo_mem_nhdsGT (by linarith : (1 / 2 + lam / 2 : ℝ) < 1 - lam / 2)]
          with u' hu'
        rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr (lt_trans hlt hu'.1)),
          if_neg (not_le.mpr hu'.1), if_pos (le_of_lt hu'.2)]
      have hx : sweepUnwrapTop r D lam s (1 / 2 + lam / 2) = sweepphi3Top r D lam s (1 / 2 + lam / 2) := by
        rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr hlt), if_pos le_rfl]
        exact sweepphi2_eq_sweepphi3Top D hlam0 s
      rw [show sweepUnwrapDerivTop r D lam s (1 / 2 + lam / 2) = sweepBranch3Top r D lam s by
        simp only [sweepUnwrapDerivTop]
        rw [if_neg (not_lt.mpr hlt.le), if_neg (lt_irrefl _),
          if_pos (by linarith : (1 / 2 + lam / 2 : ℝ) < 1 - lam / 2)]]
      exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
    · rcases lt_trichotomy u (1 - lam / 2) with h3 | h3 | h3
      · -- third branch
        have hder : HasDerivAt (sweepphi3Top r D lam s) (sweepBranch3Top r D lam s) u :=
          hasDerivAt_sweepphi3Top (D := D) lam s u (by linarith)
        have hev : (fun u' => sweepUnwrapTop r D lam s u') =ᶠ[𝓝[>] u] sweepphi3Top r D lam s := by
          filter_upwards [Ioo_mem_nhdsGT h3] with u' hu'
          rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr (lt_trans h1 hu'.1)),
            if_neg (not_le.mpr (lt_trans h2 hu'.1)), if_pos (le_of_lt hu'.2)]
        have hx : sweepUnwrapTop r D lam s u = sweepphi3Top r D lam s u := by
          rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2),
            if_pos (le_of_lt h3)]
        rw [show sweepUnwrapDerivTop r D lam s u = sweepBranch3Top r D lam s by
          simp only [sweepUnwrapDerivTop]
          rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le), if_pos h3]]
        exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
      · -- junction at 1 - lam/2
        subst h3
        have hlt2 : (1 / 2 + lam / 2 : ℝ) < 1 - lam / 2 := by linarith
        have hder : HasDerivAt (sweepphi4Top r D lam s) (sweepBranch4Top r D lam s) (1 - lam / 2) :=
          hasDerivAt_sweepphi4Top (D := D) lam s (1 - lam / 2)
        have hev : (fun u' => sweepUnwrapTop r D lam s u') =ᶠ[𝓝[>] (1 - lam / 2 : ℝ)]
            sweepphi4Top r D lam s := by
          filter_upwards [Ioo_mem_nhdsGT (by linarith : (1 - lam / 2 : ℝ) < 1)] with u' hu'
          rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr (lt_trans h1 hu'.1)),
            if_neg (not_le.mpr (lt_trans hlt2 hu'.1)), if_neg (not_le.mpr hu'.1)]
        have hx : sweepUnwrapTop r D lam s (1 - lam / 2) = sweepphi4Top r D lam s (1 - lam / 2) := by
          rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr h1), if_neg (not_le.mpr hlt2),
            if_pos le_rfl]
          exact sweepphi3_eq_sweepphi4Top D hlam0 hlam1 s
        rw [show sweepUnwrapDerivTop r D lam s (1 - lam / 2) = sweepBranch4Top r D lam s by
          simp only [sweepUnwrapDerivTop]
          rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr hlt2.le), if_neg (lt_irrefl _)]]
        exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
      · -- fourth branch
        have hder : HasDerivAt (sweepphi4Top r D lam s) (sweepBranch4Top r D lam s) u :=
          hasDerivAt_sweepphi4Top (D := D) lam s u
        have hev : (fun u' => sweepUnwrapTop r D lam s u') =ᶠ[𝓝[>] u] sweepphi4Top r D lam s := by
          filter_upwards [self_mem_nhdsWithin] with u' hu'
          rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr (lt_trans h1 hu')),
            if_neg (not_le.mpr (lt_trans h2 hu')), if_neg (not_le.mpr (lt_trans h3 hu'))]
        have hx : sweepUnwrapTop r D lam s u = sweepphi4Top r D lam s u := by
          rw [sweepUnwrap_eq_iteTop, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2),
            if_neg (not_le.mpr h3)]
        rw [show sweepUnwrapDerivTop r D lam s u = sweepBranch4Top r D lam s by
          simp only [sweepUnwrapDerivTop]
          rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le), if_neg (not_lt.mpr h3.le)]]
        exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx


/-! ## The a.e. identity with `topLoopVel` -/

/-- For `u` different from the three profile breakpoints, the two `if`-chains (`≤` versus `<`)
agree. -/
lemma ite_chain_eqTop {α : Type*} (u c₁ c₂ c₃ : ℝ) (h₁ : u ≠ c₁) (h₂ : u ≠ c₂) (h₃ : u ≠ c₃)
    (a b c e : α) :
    (if u ≤ c₁ then a else if u ≤ c₂ then b else if u ≤ c₃ then c else e)
      = (if u < c₁ then a else if u < c₂ then b else if u < c₃ then c else e) := by
  by_cases hlt₁ : u < c₁
  · rw [if_pos (le_of_lt hlt₁), if_pos hlt₁]
  · rw [if_neg (not_le.mpr (lt_of_le_of_ne (not_lt.mp hlt₁) h₁.symm)), if_neg hlt₁]
    by_cases hlt₂ : u < c₂
    · rw [if_pos (le_of_lt hlt₂), if_pos hlt₂]
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne (not_lt.mp hlt₂) h₂.symm)), if_neg hlt₂]
      by_cases hlt₃ : u < c₃
      · rw [if_pos (le_of_lt hlt₃), if_pos hlt₃]
      · rw [if_neg (not_le.mpr (lt_of_le_of_ne (not_lt.mp hlt₃) h₃.symm)), if_neg hlt₃]

lemma sweepLoopChamferDeriv_eq_derivR_of_neTop {D : SweepData d} (lam s t : ℝ)
    (h₁ : sweepParam t ≠ 1 / 2) (h₂ : sweepParam t ≠ 1 / 2 + lam / 2)
    (h₃ : sweepParam t ≠ 1 - lam / 2) :
    topLoopVel r D lam s t = sweepLoopChamferDerivRTop r D lam s t := by
  simp only [topLoopVel, sweepLoopChamferDerivRTop, sweepUnwrapDerivTop,
    sweepBranch1Top, sweepBranch2Top, sweepBranch3Top, sweepBranch4Top, velocity]
  rw [smul_ite, smul_ite, smul_ite]
  have hb1 : (((1 - 2 * lam) * (2 / period)) * sweepW' D s)
        • deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * sweepParam t)) * sweepW' D s)
      = (1 / period) • ((2 * (1 - 2 * lam))
        • (sweepW' D s • deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * sweepParam t)) * sweepW' D s))) := by
    rw [smul_smul, smul_smul]; congr 1; ring
  have hb2 : ((2 / lam) * (1 / period))
        • (sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam))
      = (1 / period) • ((2 / lam) • (sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam))) := by
    rw [smul_smul]; ring_nf
  have hb3 : (-((1 - 2 * lam) / ((1 / 2 - lam) * period))) • (r (tbR D s) - r (taR D s))
      = (1 / period) • ((-(1 - 2 * lam) / (1 / 2 - lam)) • (r (tbR D s) - r (taR D s))) := by
    by_cases h : (1 / 2 : ℝ) - lam = 0
    · have h0 : (1 - 2 * lam) = 0 := by linarith
      simp [h0]
    · have hp : period ≠ 0 := ne_of_gt period_pos
      rw [smul_smul]
      congr 1
      field_simp
  have hb4 : ((2 / lam) * (1 / period)) • (sweepArc' r D s lam - sweepChord' r D s lam)
      = (1 / period) • ((2 / lam) • (sweepArc' r D s lam - sweepChord' r D s lam)) := by
    rw [smul_smul]; ring_nf
  rw [hb1, hb2, hb3, hb4]
  exact ite_chain_eqTop (sweepParam t) (1 / 2) (1 / 2 + lam / 2) (1 - lam / 2) h₁ h₂ h₃ _ _ _ _

/-- The level set of `sweepParam` at a value `c` is countable. -/
lemma countable_sweepParam_eqTop (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    {t : ℝ | sweepParam t = c}.Countable := by
  have hset : {t : ℝ | sweepParam t = c} = Set.range (fun k : ℤ => ((k : ℝ) + c) * period) := by
    ext t
    constructor
    · intro ht
      have ht' : t / period - ((⌊t / period⌋ : ℤ) : ℝ) = c := ht
      have hdiv : t / period = ((⌊t / period⌋ : ℤ) : ℝ) + c := by linarith
      refine ⟨⌊t / period⌋, ?_⟩
      dsimp only
      rw [← hdiv]
      exact div_mul_cancel₀ t (ne_of_gt period_pos)
    · rintro ⟨k, rfl⟩
      show sweepParam (((k : ℝ) + c) * period) = c
      simp only [sweepParam]
      rw [mul_div_cancel_right₀ _ (ne_of_gt period_pos)]
      have hfloor : ⌊(k : ℝ) + c⌋ = k := by
        rw [Int.floor_eq_iff]
        constructor <;> linarith
      rw [hfloor]
      ring
  rw [hset]
  exact Set.countable_range _

lemma sweepLoopChamferDeriv_ae_eq_derivRTop {D : SweepData d} {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1 / 2) (s : ℝ) :
    topLoopVel r D lam s =ᵐ[MeasureTheory.volume] sweepLoopChamferDerivRTop r D lam s := by
  have hc : ({t : ℝ | sweepParam t = 1 / 2} ∪ {t : ℝ | sweepParam t = 1 / 2 + lam / 2}
      ∪ {t : ℝ | sweepParam t = 1 - lam / 2}).Countable :=
    ((countable_sweepParam_eqTop (1 / 2) (by norm_num) (by norm_num)).union
      (countable_sweepParam_eqTop (1 / 2 + lam / 2) (by linarith) (by linarith))).union
      (countable_sweepParam_eqTop (1 - lam / 2) (by linarith) (by linarith))
  have hbad : MeasureTheory.volume ({t : ℝ | sweepParam t = 1 / 2} ∪ {t : ℝ | sweepParam t = 1 / 2 + lam / 2}
      ∪ {t : ℝ | sweepParam t = 1 - lam / 2}) = 0 := Set.Countable.measure_zero hc MeasureTheory.volume
  show ∀ᵐ x ∂MeasureTheory.volume,
    topLoopVel r D lam s x = sweepLoopChamferDerivRTop r D lam s x
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hbad
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  simp only [Set.mem_union, Set.mem_setOf_eq]
  rcases em (sweepParam t = 1 / 2) with h1 | h1
  · exact Or.inl (Or.inl h1)
  rcases em (sweepParam t = 1 / 2 + lam / 2) with h2 | h2
  · exact Or.inl (Or.inr h2)
  rcases em (sweepParam t = 1 - lam / 2) with h3 | h3
  · exact Or.inr h3
  · exact absurd (sweepLoopChamferDeriv_eq_derivR_of_neTop lam s t h1 h2 h3) ht

/-! ## Measurability and boundedness of the right derivative -/

lemma measurable_sweepBranch1Top {D : SweepData d} (hderiv : Continuous (deriv r))
    (lam s : ℝ) : Measurable (sweepBranch1Top r D lam s) := by
  have h : (fun u : ℝ => (2 * (1 - 2 * lam)) •
      ((sweepW' D s) • deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s)))
      = sweepBranch1Top r D lam s := rfl
  rw [← h]
  refine Continuous.measurable ?_
  have h1 : Continuous (fun u : ℝ => (2 : ℝ) * u) := continuous_const.mul continuous_id
  have h2 : Continuous (fun u : ℝ => (1 - 2 * lam) * (2 * u)) := continuous_const.mul h1
  have h3 : Continuous (fun u : ℝ => lam + (1 - 2 * lam) * (2 * u)) := continuous_const.add h2
  have h4 : Continuous (fun u : ℝ =>
      (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s) := h3.mul continuous_const
  exact (continuous_const : Continuous (fun _ : ℝ => (2 * (1 - 2 * lam)))).smul
    ((continuous_const : Continuous (fun _ : ℝ => (sweepW' D s))).smul
      (hderiv.comp (h4.const_add (taR D s))))

lemma measurable_sweepUnwrapDerivTop {D : SweepData d} (hderiv : Continuous (deriv r))
    (lam s : ℝ) : Measurable (sweepUnwrapDerivTop r D lam s) := by
  have hb1 := measurable_sweepBranch1Top (r := r) (D := D) hderiv lam s
  have h : sweepUnwrapDerivTop r D lam s = (fun u : ℝ =>
      if u < 1 / 2 then sweepBranch1Top r D lam s u
      else if u < 1 / 2 + lam / 2 then sweepBranch2Top r D lam s
      else if u < 1 - lam / 2 then sweepBranch3Top r D lam s
      else sweepBranch4Top r D lam s) := rfl
  rw [h]
  exact Measurable.ite measurableSet_Iio hb1
    (Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const))

lemma measurable_sweepLoopChamferDerivRTop {D : SweepData d} (hderiv : Continuous (deriv r))
    (lam s : ℝ) : Measurable (sweepLoopChamferDerivRTop r D lam s) := by
  have h : sweepLoopChamferDerivRTop r D lam s
      = fun t : ℝ => (1 / period) • sweepUnwrapDerivTop r D lam s (sweepParam t) := rfl
  rw [h]
  exact ((measurable_sweepUnwrapDerivTop (r := r) (D := D) hderiv lam s).comp
    sweepLoopChamfer_sweepParam_measurable).const_smul (1 / period)

/-- A convex combination of two reals lies between them. -/
lemma conv_mem_uIccTop {a b ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) :
    (1 - ξ) * a + ξ * b ∈ Set.uIcc a b := by
  rcases le_total a b with hab | hab
  · rw [Set.uIcc_of_le hab, Set.mem_Icc]
    constructor <;> nlinarith
  · rw [Set.uIcc_of_ge hab, Set.mem_Icc]
    constructor <;> nlinarith

lemma norm_sweepArc'_leTop {D : SweepData d} {s Br : ℝ}
    (hBr : ∀ y ∈ Set.uIcc (taR D s) (tbR D s), ‖r y‖ ≤ Br) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) : ‖sweepArc' r D s ξ‖ ≤ Br := by
  have hmem : taR D s + ξ * sweepW' D s ∈ Set.uIcc (taR D s) (tbR D s) := by
    have h : taR D s + ξ * sweepW' D s = (1 - ξ) * taR D s + ξ * tbR D s := by
      simp only [sweepW']; ring
    rw [h]
    exact conv_mem_uIccTop hξ.1 hξ.2
  simpa only [sweepArc'] using hBr _ hmem

lemma norm_sweepChord'_leTop {D : SweepData d} {s Br : ℝ}
    (hBr : ∀ y ∈ Set.uIcc (taR D s) (tbR D s), ‖r y‖ ≤ Br) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) : ‖sweepChord' r D s ξ‖ ≤ Br := by
  have h : sweepChord' r D s ξ = (1 - ξ) • r (taR D s) + ξ • r (tbR D s) := rfl
  rw [h]
  calc ‖(1 - ξ) • r (taR D s) + ξ • r (tbR D s)‖
      ≤ ‖(1 - ξ) • r (taR D s)‖ + ‖ξ • r (tbR D s)‖ := norm_add_le _ _
    _ = (1 - ξ) * ‖r (taR D s)‖ + ξ * ‖r (tbR D s)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hξ.1, hξ.2]), abs_of_nonneg hξ.1]
    _ ≤ (1 - ξ) * Br + ξ * Br := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (hBr _ Set.left_mem_uIcc) (by linarith [hξ.2])
        · exact mul_le_mul_of_nonneg_left (hBr _ Set.right_mem_uIcc) hξ.1
    _ = Br := by ring

lemma norm_sweepUnwrapDeriv_leTop {D : SweepData d} {s : ℝ} {Bd Br : ℝ}
    (hBd : ∀ y ∈ Set.uIcc (taR D s) (tbR D s), ‖deriv r y‖ ≤ Bd)
    (hBr : ∀ y ∈ Set.uIcc (taR D s) (tbR D s), ‖r y‖ ≤ Br)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖sweepUnwrapDerivTop r D lam s u‖ ≤
      max (2 * |1 - 2 * lam| * |sweepW' D s| * Bd)
        (max (2 / lam * (2 * Br)) (max (|(1 - 2 * lam) / (1 / 2 - lam)| * (2 * Br))
          (2 / lam * (2 * Br)))) := by
  have hξl : (1 - lam) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hξl' : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hlam0, by linarith⟩
  have hmem2 : ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖ ≤ 2 * Br := by
    calc ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖
        ≤ ‖sweepChord' r D s (1 - lam)‖ + ‖sweepArc' r D s (1 - lam)‖ := norm_sub_le _ _
      _ ≤ Br + Br := add_le_add (norm_sweepChord'_leTop (s := s) hBr hξl)
        (norm_sweepArc'_leTop (s := s) hBr hξl)
      _ = 2 * Br := by ring
  have hmem4 : ‖sweepArc' r D s lam - sweepChord' r D s lam‖ ≤ 2 * Br := by
    calc ‖sweepArc' r D s lam - sweepChord' r D s lam‖
        ≤ ‖sweepArc' r D s lam‖ + ‖sweepChord' r D s lam‖ := norm_sub_le _ _
      _ ≤ Br + Br := add_le_add (norm_sweepArc'_leTop (s := s) hBr hξl')
        (norm_sweepChord'_leTop (s := s) hBr hξl')
      _ = 2 * Br := by ring
  rw [sweepUnwrapDerivTop]
  split_ifs with h1 h2 h3
  · have hξ1 : lam + (1 - 2 * lam) * (2 * u) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [h1, hu0]
    have hy : taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s
        ∈ Set.uIcc (taR D s) (tbR D s) := by
      have h : taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s
          = (1 - (lam + (1 - 2 * lam) * (2 * u))) * taR D s
            + (lam + (1 - 2 * lam) * (2 * u)) * tbR D s := by
        simp only [sweepW']; ring
      rw [h]
      exact conv_mem_uIccTop hξ1.1 hξ1.2
    have hb : ‖sweepBranch1Top r D lam s u‖ ≤ 2 * |1 - 2 * lam| * |sweepW' D s| * Bd := by
      simp only [sweepBranch1Top]
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h2' : |2 * (1 - 2 * lam)| = 2 * |1 - 2 * lam| := by
        rw [abs_mul]; norm_num
      rw [h2']
      calc 2 * |1 - 2 * lam| * (|sweepW' D s| * ‖deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s)‖)
          = 2 * |1 - 2 * lam| * |sweepW' D s| * ‖deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s)‖ := by ring
        _ ≤ 2 * |1 - 2 * lam| * |sweepW' D s| * Bd :=
            mul_le_mul_of_nonneg_left (hBd _ hy)
              (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _))
    exact le_trans hb (le_max_left _ _)
  · have hb : ‖sweepBranch2Top r D lam s‖ ≤ 2 / lam * (2 * Br) := by
      simp only [sweepBranch2Top]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos two_pos hlam0)]
      exact mul_le_mul_of_nonneg_left hmem2 (le_of_lt (div_pos two_pos hlam0))
    exact le_trans hb (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hb : ‖sweepBranch3Top r D lam s‖ ≤ |(1 - 2 * lam) / (1 / 2 - lam)| * (2 * Br) := by
      simp only [sweepBranch3Top]
      rw [norm_smul, Real.norm_eq_abs, neg_div, abs_neg]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc ‖r (tbR D s) - r (taR D s)‖
          ≤ ‖r (tbR D s)‖ + ‖r (taR D s)‖ := norm_sub_le _ _
        _ ≤ Br + Br := add_le_add (hBr _ Set.right_mem_uIcc) (hBr _ Set.left_mem_uIcc)
        _ = 2 * Br := by ring
    refine le_trans hb (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _)))
  · have hb : ‖sweepBranch4Top r D lam s‖ ≤ 2 / lam * (2 * Br) := by
      simp only [sweepBranch4Top]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos two_pos hlam0)]
      exact mul_le_mul_of_nonneg_left hmem4 (le_of_lt (div_pos two_pos hlam0))
    exact le_trans hb (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _)))

lemma norm_sweepLoopChamferDerivR_leTop {D : SweepData d} (hr : Continuous r)
    (hderiv : Continuous (deriv r)) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (s : ℝ) : ∃ C, ∀ t, ‖sweepLoopChamferDerivRTop r D lam s t‖ ≤ C := by
  obtain ⟨Bd, hBd⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (s := Set.uIcc (taR D s) (tbR D s)) hderiv.continuousOn
  obtain ⟨Br, hBr⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (s := Set.uIcc (taR D s) (tbR D s)) hr.continuousOn
  refine ⟨1 / period * max (2 * |1 - 2 * lam| * |sweepW' D s| * Bd)
      (max (2 / lam * (2 * Br)) (max (|(1 - 2 * lam) / (1 / 2 - lam)| * (2 * Br))
        (2 / lam * (2 * Br)))), fun t => ?_⟩
  have hu := sweepParam_mem t
  have hbound := norm_sweepUnwrapDeriv_leTop (D := D) (s := s) hBd hBr hlam0 hlam1 hu.1 hu.2.le
  simp only [sweepLoopChamferDerivRTop]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr period_pos)]
  exact mul_le_mul_of_nonneg_left hbound (le_of_lt (one_div_pos.mpr period_pos))

/-! ## The right derivative of the chamfered loop -/

theorem sweepLoopChamfer_hasDerivWithinAtTop {r : ℝ → Space}
    (hr : ContDiff ℝ 1 r) {d : BandArcData} (D : SweepData d)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (s x : ℝ) :
    HasDerivWithinAt (fun t => sweepLoopChamfer r D lam s t)
      (sweepLoopChamferDerivRTop r D lam s x) (Set.Ioi x) x := by
  have hd : Differentiable ℝ r := hr.differentiable (by norm_num)
  set k : ℤ := ⌊x / period⌋ with hk
  have hu : sweepParam x = x / period - (k : ℝ) := by simp only [sweepParam]; rw [← hk]
  have hin : HasDerivWithinAt (fun u' => sweepUnwrapTop r D lam s u')
      (sweepUnwrapDerivTop r D lam s (x / period - (k : ℝ))) (Set.Ioi (x / period - (k : ℝ)))
      (x / period - (k : ℝ)) := by
    have := sweepUnwrap_hasDerivWithinAtTop (D := D) hd hlam0 hlam1 s (sweepParam x)
    simpa [hu] using this
  have hφ : HasDerivWithinAt (fun t : ℝ => t / period - (k : ℝ)) (1 / period) (Set.Ioi x) x :=
    (((hasDerivAt_id x).div_const period).sub_const (k : ℝ)).hasDerivWithinAt
  have hmap : Set.MapsTo (fun t : ℝ => t / period - (k : ℝ)) (Set.Ioi x)
      (Set.Ioi (x / period - (k : ℝ))) := by
    intro t ht
    simp only [Set.mem_Ioi] at ht ⊢
    have h := div_lt_div_of_pos_right ht period_pos
    linarith
  have hcomp := HasDerivWithinAt.scomp x hin hφ hmap
  have hev : (fun t => sweepLoopChamfer r D lam s t)
      =ᶠ[𝓝[>] x] (fun t => sweepUnwrapTop r D lam s (t / period - (k : ℝ))) := by
    have hpos : (0 : ℝ) < period * (1 - sweepParam x) / 2 := by
      have h := (sweepParam_mem x).2
      have hp := period_pos
      nlinarith
    filter_upwards [Ioo_mem_nhdsGT (by linarith : x < x + period * (1 - sweepParam x) / 2)]
      with t ht
    rw [sweepLoopChamfer_eq_unwrapTop]
    congr 1
    rw [sweepParam]
    have hfloor : ⌊t / period⌋ = k := by
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · have hxk : (k : ℝ) ≤ x / period := by
          have := Int.floor_le (x / period)
          simpa [hk] using this
        have := div_lt_div_of_pos_right ht.1 period_pos
        linarith
      · have hlt : t / period < x / period + (1 - sweepParam x) / 2 := by
          rw [div_lt_iff₀ period_pos]
          rw [show (x / period + (1 - sweepParam x) / 2) * period
              = x + period * (1 - sweepParam x) / 2 by
            rw [add_mul, div_mul_cancel₀ x (ne_of_gt period_pos)]
            ring]
          exact ht.2
        have hfloor' : x / period = (k : ℝ) + sweepParam x := by rw [hu]; ring
        rw [hfloor'] at hlt
        have h2 := (sweepParam_mem x).2
        nlinarith
    rw [hfloor]
  have hx : sweepLoopChamfer r D lam s x = sweepUnwrapTop r D lam s (x / period - (k : ℝ)) := by
    rw [sweepLoopChamfer_eq_unwrapTop, hu]
  rw [show sweepLoopChamferDerivRTop r D lam s x
      = (1 / period) • sweepUnwrapDerivTop r D lam s (x / period - (k : ℝ)) by
    simp only [sweepLoopChamferDerivRTop, hu]]
  exact hcomp.congr_of_eventuallyEq hev hx

/-! ## The fundamental theorem of calculus -/

theorem sweepLoopChamfer_ftcTop {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : ContDiff ℝ 1 r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (s τ₁ τ₂ : ℝ) :
    Work.Drive.sweepLoopChamfer r D lam s τ₂ - Work.Drive.sweepLoopChamfer r D lam s τ₁
      = ∫ τ in τ₁..τ₂, Work.Drive.topLoopVel r D lam s τ := by
  have hcont : ContinuousOn (fun t => sweepLoopChamfer r D lam s t) (Set.uIcc τ₁ τ₂) :=
    (sweepLoopChamfer_continuous_tTop hr.continuous D hlam0 hlam1).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (min τ₁ τ₂) (max τ₁ τ₂),
      HasDerivWithinAt (fun t => sweepLoopChamfer r D lam s t)
        (sweepLoopChamferDerivRTop r D lam s x) (Set.Ioi x) x :=
    fun x _ => sweepLoopChamfer_hasDerivWithinAtTop hr D hlam0 hlam1 s x
  have hint : IntervalIntegrable (sweepLoopChamferDerivRTop r D lam s) MeasureTheory.volume τ₁ τ₂ := by
    rw [intervalIntegrable_iff]
    obtain ⟨C, hC⟩ := norm_sweepLoopChamferDerivR_leTop (D := D) hr.continuous
      (hr.continuous_deriv (by norm_num)) hlam0 hlam1 s
    have hfin : MeasureTheory.volume (Set.uIoc τ₁ τ₂) < (⊤ : ENNReal) := by
      show MeasureTheory.volume (Set.Ioc (min τ₁ τ₂) (max τ₁ τ₂)) < (⊤ : ENNReal)
      exact lt_of_le_of_lt (MeasureTheory.measure_mono Set.Ioc_subset_Icc_self)
        isCompact_Icc.measure_lt_top
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ C (Filter.Eventually.of_forall hC)
    exact (measurable_sweepLoopChamferDerivRTop (D := D)
      (hr.continuous_deriv (by norm_num)) lam s).aestronglyMeasurable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint
  have hae : (∫ τ in τ₁..τ₂, topLoopVel r D lam s τ)
      = ∫ τ in τ₁..τ₂, sweepLoopChamferDerivRTop r D lam s τ :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [sweepLoopChamferDeriv_ae_eq_derivRTop (D := D) hlam0 hlam1 s]
        with x hx _
      exact hx)
  rw [hae, hFTC]


end Work.Drive
