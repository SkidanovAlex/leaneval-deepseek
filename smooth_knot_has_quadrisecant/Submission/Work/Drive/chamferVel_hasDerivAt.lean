import Mathlib
import Submission.Work.Drive.sweepWideEndDefs
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepLoopChamfer_ftc
import Submission.Work.Drive.chamferVelBranch

/-!
# The loop derivative of the chamfered sweep is the chamfer velocity

The chamfered sweep loop `Work.Drive.sweepLoopChamfer r D lam sig` is piecewise smooth in the loop
parameter `t`, with corners exactly at the loop parameters listed by
`Work.Drive.chamferCorner lam t` (the profile values `0`, `1/2`, `1/2 + lam/2`, `1 - lam/2`).
This module proves that *off* those corners the loop is genuinely differentiable, with derivative
the `Work.Drive.chamferVel` of the wide-end estimate:

the lemma `chamferVel_hasDerivAt` below: whenever `0 < lam < 1/2` and `lam` and `t` are such that
`t` is not a corner (`¬ chamferCorner lam t`), the loop has derivative `chamferVel r D lam sig t`
at `t`.

## Proof

Write `u = sweepParam t`.  Since `t` is not a corner, `u ≠ 0`, so `t / period` is not an integer
and the floor `⌊y / period⌋` is locally constant near `t`; hence near `t` the profile is the affine
function `y ↦ g y = (y - t)/period + u` (`eventually_sweepParam_eq`).  The unwrapped loop
`Work.Drive.sweepUnwrap` (the same four formulas with the profile as the variable) then agrees near
`t` with the *loop*, and near `u` it agrees with one of the four branch functions
`Work.Drive.sweepphi1 … sweepphi4` (whichever is selected by the open interval containing `u`).
Each branch function has the branch derivative `Work.Drive.sweepBranch1 … sweepBranch4`
(`hasDerivAt_sweepphi1 … hasDerivAt_sweepphi4`), so the chain rule gives the loop derivative
`(1/period) • sweepBranch_j` at `t`, and the four lemmas `smul_sweepBranch1 … smul_sweepBranch4`
identify that vector with `chamferVel r D lam sig t` (both sides being the same constant times the
same evaluation of the knot / its velocity).
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval Filter

variable {r : ℝ → Space} {d : BandArcData} {D : SweepData d}

/-! ## The four branches of `chamferVel` as `(1 / period) •` the branch derivatives -/

/-- On the arc side `u < 1/2` of the profile, `chamferVel` is `(1 / period)` times the derivative
of the arc branch `sweepphi1`. -/
lemma smul_sweepBranch1 {lam sig u t : ℝ} (hu : sweepParam t = u) (hu1 : u < 1/2) :
    (1/period) • sweepBranch1 r D lam sig u = chamferVel r D lam sig t := by
  rw [chamferVel_eq_ite, hu, if_pos (le_of_lt hu1)]
  simp only [chamferVelArc, sweepBranch1, velocity]
  rw [hu, smul_smul, smul_smul]
  congr 1
  ring

/-- On the first chamfer `1/2 < u < 1/2 + lam/2`, `chamferVel` is `(1 / period)` times the
derivative of the chamfer branch `sweepphi2`. -/
lemma smul_sweepBranch2 {lam sig u t : ℝ} (hu : sweepParam t = u) (h1 : 1/2 < u)
    (h2 : u < 1/2 + lam/2) :
    (1/period) • sweepBranch2 r D lam sig = chamferVel r D lam sig t := by
  rw [chamferVel_eq_ite, hu, if_neg (not_le.mpr h1), if_pos (le_of_lt h2)]
  simp only [chamferVelChamfer₁, sweepBranch2]
  rw [smul_smul]
  congr 1
  ring

/-- On the chord side `1/2 + lam/2 < u < 1 - lam/2` of the profile, `chamferVel` is `(1 / period)`
times the derivative of the chord branch `sweepphi3`. -/
lemma smul_sweepBranch3 {lam sig u t : ℝ} (h0 : 0 < lam) (hu : sweepParam t = u)
    (h1 : 1/2 + lam/2 < u) (h2 : u < 1 - lam/2) :
    (1/period) • sweepBranch3 r D lam sig = chamferVel r D lam sig t := by
  have hne : (1/2 : ℝ) - lam ≠ 0 := by linarith
  rw [chamferVel_eq_ite, hu, if_neg (not_le.mpr (by linarith : (1:ℝ)/2 < u)),
    if_neg (not_le.mpr h1), if_pos (le_of_lt h2)]
  simp only [chamferVelChord, sweepBranch3]
  rw [smul_smul]
  congr 1
  field_simp

/-- On the second chamfer `1 - lam/2 < u` of the profile, `chamferVel` is `(1 / period)` times the
derivative of the fourth branch `sweepphi4`. -/
lemma smul_sweepBranch4 {lam sig u t : ℝ} (h0 : 0 < lam) (hu : sweepParam t = u) (h1 : lam < 1/2)
    (h3 : 1 - lam/2 < u) :
    (1/period) • sweepBranch4 r D lam sig = chamferVel r D lam sig t := by
  rw [chamferVel_eq_ite, hu, if_neg (not_le.mpr (by linarith : (1:ℝ)/2 < u)),
    if_neg (not_le.mpr (by linarith : (1:ℝ)/2 + lam/2 < u)), if_neg (not_le.mpr h3)]
  simp only [chamferVelChamfer₂, sweepBranch4]
  rw [smul_smul]
  congr 1
  ring

/-! ## The profile is locally affine away from the multiples of the period -/

/-- **The profile is locally affine near a parameter whose profile is nonzero.**  If
`sweepParam t ≠ 0` then `t / period` is not an integer, so the floor `⌊y / period⌋` is locally
constant near `t`; consequently `sweepParam y = (y - t)/period + sweepParam t` for all `y`
sufficiently close to `t`. -/
lemma eventually_sweepParam_eq {t : ℝ} (ht : sweepParam t ≠ 0) :
    ∀ᶠ y in 𝓝 t, sweepParam y = (y - t) / period + sweepParam t := by
  set k : ℤ := ⌊t / period⌋ with hk
  have hle : (k : ℝ) ≤ t / period := by
    have h := Int.floor_le (t / period); rwa [← hk] at h
  have hlt : t / period < (k : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (t / period); rwa [← hk] at h
  have hne : t / period ≠ (k : ℝ) := by
    intro h
    refine ht ?_
    rw [sweepParam, ← hk, h]
    ring
  have hgt : (k : ℝ) < t / period := lt_of_le_of_ne hle (Ne.symm hne)
  have hpre : (fun y : ℝ => y / period) ⁻¹' Set.Ioo (k : ℝ) ((k : ℝ) + 1) ∈ 𝓝 t :=
    (continuous_id.div_const period).continuousAt.preimage_mem_nhds (Ioo_mem_nhds hgt hlt)
  filter_upwards [hpre] with y hy
  have hfloor : ⌊y / period⌋ = k := by
    rw [Int.floor_eq_iff]
    exact ⟨le_of_lt hy.1, hy.2⟩
  have htk : sweepParam t = t / period - (k : ℝ) := by
    rw [sweepParam, ← hk]
  rw [htk, sweepParam, hfloor]
  ring

/-! ## The main theorem -/

theorem chamferVel_hasDerivAt {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam sig t : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) (hc : ¬ Work.Drive.chamferCorner lam t) :
    HasDerivAt (fun y : ℝ => Work.Drive.sweepLoopChamfer r D lam sig y)
      (Work.Drive.chamferVel r D lam sig t) t := by
  have hd : Differentiable ℝ r := hr.differentiable (by simp)
  simp only [chamferCorner, not_or] at hc
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  -- the affine unwrapping of the profile near `t`
  let g : ℝ → ℝ := fun y => (y - t) / period + sweepParam t
  have hgt : g t = sweepParam t := by
    show (t - t) / period + sweepParam t = sweepParam t
    simp
  have hg : HasDerivAt g (1 / period) t := by
    change HasDerivAt (fun y : ℝ => (y - t) / period + sweepParam t) (1 / period) t
    have hlin : HasDerivAt (fun y : ℝ => (y - t) / period) (1 / period) t := by
      simpa using (((hasDerivAt_id t).sub_const t).div_const period)
    exact hlin.add_const (sweepParam t)
  have hloop : ∀ᶠ y in 𝓝 t, sweepLoopChamfer r D lam sig y = sweepUnwrap r D lam sig (g y) := by
    filter_upwards [eventually_sweepParam_eq hc0] with y hy
    rw [sweepLoopChamfer_eq_unwrap, hy]
  -- the four branches of the unwrapped loop
  rcases lt_trichotomy (sweepParam t) (1 / 2) with hlt | heq | hgt2
  · -- arc branch: `u < 1/2`
    have hset : (fun y : ℝ => g y) ⁻¹' Set.Iio (1 / 2) ∈ 𝓝 t :=
      hg.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hgt]; exact hlt))
    have hbranch : ∀ᶠ y in 𝓝 t,
        sweepUnwrap r D lam sig (g y) = sweepphi1 r D lam sig (g y) := by
      filter_upwards [hset] with y hy
      simp only [Set.mem_preimage, Set.mem_Iio] at hy
      have hA : g y ≤ 1 / 2 := le_of_lt hy
      rw [sweepUnwrap, if_pos hA, sweepphi1]
    have hev : (fun y : ℝ => sweepLoopChamfer r D lam sig y)
        =ᶠ[𝓝 t] (sweepphi1 r D lam sig) ∘ g := by
      filter_upwards [hloop, hbranch] with y h1' h2'
      show sweepLoopChamfer r D lam sig y = sweepphi1 r D lam sig (g y)
      rw [h1', h2']
    have hφ : HasDerivAt (sweepphi1 r D lam sig) (sweepBranch1 r D lam sig (g t)) (g t) :=
      hasDerivAt_sweepphi1 hd lam sig (g t)
    have hcomp : HasDerivAt ((sweepphi1 r D lam sig) ∘ g)
        ((1 / period) • sweepBranch1 r D lam sig (g t)) t := hφ.scomp t hg
    have hder : HasDerivAt (fun y : ℝ => sweepLoopChamfer r D lam sig y)
        ((1 / period) • sweepBranch1 r D lam sig (g t)) t :=
      (hev.hasDerivAt_iff).mpr hcomp
    exact hder.congr_deriv (smul_sweepBranch1 (u := g t) hgt.symm (by rw [hgt]; exact hlt))
  · exact absurd heq hc1
  · rcases lt_trichotomy (sweepParam t) (1 / 2 + lam / 2) with h2lt | h2eq | h2gt
    · -- first chamfer: `1/2 < u < 1/2 + lam/2`
      have hset : (fun y : ℝ => g y) ⁻¹' Set.Ioo (1 / 2) (1 / 2 + lam / 2) ∈ 𝓝 t :=
        hg.continuousAt.preimage_mem_nhds
          (Ioo_mem_nhds (by rw [hgt]; exact hgt2) (by rw [hgt]; exact h2lt))
      have hbranch : ∀ᶠ y in 𝓝 t,
          sweepUnwrap r D lam sig (g y) = sweepphi2 r D lam sig (g y) := by
        filter_upwards [hset] with y hy
        simp only [Set.mem_preimage, Set.mem_Ioo] at hy
        have hA : ¬ (g y ≤ 1 / 2) := not_le.mpr hy.1
        have hB : g y ≤ 1 / 2 + lam / 2 := le_of_lt hy.2
        rw [sweepUnwrap, if_neg hA, if_pos hB, sweepphi2]
      have hev : (fun y : ℝ => sweepLoopChamfer r D lam sig y)
          =ᶠ[𝓝 t] (sweepphi2 r D lam sig) ∘ g := by
        filter_upwards [hloop, hbranch] with y h1' h2'
        show sweepLoopChamfer r D lam sig y = sweepphi2 r D lam sig (g y)
        rw [h1', h2']
      have hφ : HasDerivAt (sweepphi2 r D lam sig) (sweepBranch2 r D lam sig) (g t) :=
        hasDerivAt_sweepphi2 lam sig (g t)
      have hcomp : HasDerivAt ((sweepphi2 r D lam sig) ∘ g)
          ((1 / period) • sweepBranch2 r D lam sig) t := hφ.scomp t hg
      have hder : HasDerivAt (fun y : ℝ => sweepLoopChamfer r D lam sig y)
          ((1 / period) • sweepBranch2 r D lam sig) t := (hev.hasDerivAt_iff).mpr hcomp
      exact hder.congr_deriv (smul_sweepBranch2 (u := g t) hgt.symm (by rw [hgt]; exact hgt2)
        (by rw [hgt]; exact h2lt))
    · exact absurd h2eq hc2
    · rcases lt_trichotomy (sweepParam t) (1 - lam / 2) with h3lt | h3eq | h3gt
      · -- chord side: `1/2 + lam/2 < u < 1 - lam/2`
        have hset : (fun y : ℝ => g y) ⁻¹' Set.Ioo (1 / 2 + lam / 2) (1 - lam / 2) ∈ 𝓝 t :=
          hg.continuousAt.preimage_mem_nhds
            (Ioo_mem_nhds (by rw [hgt]; exact h2gt) (by rw [hgt]; exact h3lt))
        have hbranch : ∀ᶠ y in 𝓝 t,
            sweepUnwrap r D lam sig (g y) = sweepphi3 r D lam sig (g y) := by
          filter_upwards [hset] with y hy
          simp only [Set.mem_preimage, Set.mem_Ioo] at hy
          have hA : ¬ (g y ≤ 1 / 2) := not_le.mpr (by linarith [hy.1, h0])
          have hB : ¬ (g y ≤ 1 / 2 + lam / 2) := not_le.mpr hy.1
          have hC : g y ≤ 1 - lam / 2 := le_of_lt hy.2
          rw [sweepUnwrap, if_neg hA, if_neg hB, if_pos hC, sweepphi3]
        have hev : (fun y : ℝ => sweepLoopChamfer r D lam sig y)
            =ᶠ[𝓝 t] (sweepphi3 r D lam sig) ∘ g := by
          filter_upwards [hloop, hbranch] with y h1' h2'
          show sweepLoopChamfer r D lam sig y = sweepphi3 r D lam sig (g y)
          rw [h1', h2']
        have hφ : HasDerivAt (sweepphi3 r D lam sig) (sweepBranch3 r D lam sig) (g t) :=
          hasDerivAt_sweepphi3 lam sig (g t) (by linarith)
        have hcomp : HasDerivAt ((sweepphi3 r D lam sig) ∘ g)
            ((1 / period) • sweepBranch3 r D lam sig) t := hφ.scomp t hg
        have hder : HasDerivAt (fun y : ℝ => sweepLoopChamfer r D lam sig y)
            ((1 / period) • sweepBranch3 r D lam sig) t := (hev.hasDerivAt_iff).mpr hcomp
        exact hder.congr_deriv (smul_sweepBranch3 h0 (u := g t) hgt.symm (by rw [hgt]; exact h2gt)
          (by rw [hgt]; exact h3lt))
      · exact absurd h3eq hc3
      · -- second chamfer: `1 - lam/2 < u`
        have hset : (fun y : ℝ => g y) ⁻¹' Set.Ioo (1 - lam / 2) 1 ∈ 𝓝 t :=
          hg.continuousAt.preimage_mem_nhds
            (Ioo_mem_nhds (by rw [hgt]; exact h3gt) (by
              rw [hgt]; exact (sweepParam_mem t).2))
        have hbranch : ∀ᶠ y in 𝓝 t,
            sweepUnwrap r D lam sig (g y) = sweepphi4 r D lam sig (g y) := by
          filter_upwards [hset] with y hy
          simp only [Set.mem_preimage, Set.mem_Ioo] at hy
          have hA : ¬ (g y ≤ 1 / 2) := not_le.mpr (by linarith [hy.1, h0])
          have hB : ¬ (g y ≤ 1 / 2 + lam / 2) := not_le.mpr (by linarith [hy.1, h0])
          have hC : ¬ (g y ≤ 1 - lam / 2) := not_le.mpr hy.1
          rw [sweepUnwrap, if_neg hA, if_neg hB, if_neg hC, sweepphi4]
        have hev : (fun y : ℝ => sweepLoopChamfer r D lam sig y)
            =ᶠ[𝓝 t] (sweepphi4 r D lam sig) ∘ g := by
          filter_upwards [hloop, hbranch] with y h1' h2'
          show sweepLoopChamfer r D lam sig y = sweepphi4 r D lam sig (g y)
          rw [h1', h2']
        have hφ : HasDerivAt (sweepphi4 r D lam sig) (sweepBranch4 r D lam sig) (g t) :=
          hasDerivAt_sweepphi4 lam sig (g t)
        have hcomp : HasDerivAt ((sweepphi4 r D lam sig) ∘ g)
            ((1 / period) • sweepBranch4 r D lam sig) t := hφ.scomp t hg
        have hder : HasDerivAt (fun y : ℝ => sweepLoopChamfer r D lam sig y)
            ((1 / period) • sweepBranch4 r D lam sig) t := (hev.hasDerivAt_iff).mpr hcomp
        exact hder.congr_deriv (smul_sweepBranch4 h0 (u := g t) hgt.symm h1
          (by rw [hgt]; exact h3gt))

end Work.Drive
