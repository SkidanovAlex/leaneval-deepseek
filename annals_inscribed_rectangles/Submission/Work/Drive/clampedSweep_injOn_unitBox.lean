import Mathlib
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.clampedSweepChart
import Submission.Work.Drive.CapSmooth.sweepChainSmooth
import Submission.Work.Drive.scaleSweep
import Submission.Work.Drive.Interfaces

/-!
# Injectivity of the clamped radial sweep on the parameter box

`Work.Drive.clampedSweep c ψ P x = scaleCapping (clampScale c ψ P x) (P (x 0, x 1))` is the radial
chain whose `x 2 = 1` face is the plane `P` and whose `x 2 = 0` face is the shadow of `P` on the level
`c`.  Its two structural properties (`Submission/Work/Drive/clampedSweepChart.lean`) are

* the projective class of the sweep at `x` is the class of the plane at `(x 0, x 1)`, *independent of*
  `x 2`, and
* the radial coordinate is `clampScale c ψ P x = exp (ψ (x 2) · (log c - log r))` times the plane's own
  radius `r = levelOf (P (x 0, x 1))`.

The theorem below is the injectivity of the sweep over the parameter box `[0,1]³`, from the two
hypotheses that the plane's presentation `P` is *class-injective* on `[0,1]²` (two box points with the
same projective class coincide) and that the plane never already lies in the truncation level `c`:

* the classes agree, so `(x 0, x 1) = (x' 0, x' 1)`;
* the radial coordinates then read `exp (ψ (x 2) · A) · r = exp (ψ (x' 2) · A) · r` with
  `A = log c - log r ≠ 0` (because `r ≠ c`), so `ψ (x 2) = ψ (x' 2)`, and `ψ` is injective on `[0,1]`.

This is the "the sweep parameterises its image faithfully" input of the (clamped) chain route: it is
what turns a level-and-class description of a point of the sweep into a unique parameter, and it is
the graph condition `hfibV` of the sweep's cut (`Submission/Work/Drive/clampedSweepImage.lean`,
`ncard_cutFibreBox_clampedSweep_eq_one`) in its raw form.
-/

namespace Work.Drive

/-- The two-parameter projection `(x 0, x 1)` of a point of `[0,1]³` lies in `[0,1]²`. -/
private lemma mk2_mem_unitBox_one {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : mk2 a b ∈ Submission.Drive.unitBox 1 := by
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

theorem clampedSweep_injOn_unitBox {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ : Set.InjOn ψ (Set.Icc (0 : ℝ) 1))
    {P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace}
    (hcls : ∀ y ∈ Submission.Drive.unitBox 1, ∀ y' ∈ Submission.Drive.unitBox 1,
      (Work.Drive.cappingSpaceHomeoProj (P y)).2 = (Work.Drive.cappingSpaceHomeoProj (P y')).2
        → y = y')
    (hlev : ∀ y ∈ Submission.Drive.unitBox 1, Work.Drive.levelOf (P y) ≠ c) :
    Set.InjOn (Work.Drive.clampedSweep c ψ P) (Submission.Drive.unitBox 2) := by
  intro x hx x' hx' heq
  -- ## Step 1: the two plane points have the same projective class, hence coincide
  have hy : mk2 (x 0) (x 1) ∈ Submission.Drive.unitBox 1 := mk2_mem_unitBox_one (hx 0) (hx 1)
  have hy' : mk2 (x' 0) (x' 1) ∈ Submission.Drive.unitBox 1 := mk2_mem_unitBox_one (hx' 0) (hx' 1)
  have hclass : (cappingSpaceHomeoProj (P (mk2 (x 0) (x 1)))).2
      = (cappingSpaceHomeoProj (P (mk2 (x' 0) (x' 1)))).2 := by
    rw [← cappingSpaceHomeoProj_clampedSweep_snd c ψ P x, heq,
      cappingSpaceHomeoProj_clampedSweep_snd c ψ P x']
  have hyy : mk2 (x 0) (x 1) = mk2 (x' 0) (x' 1) := hcls _ hy _ hy' hclass
  have hx0 : x 0 = x' 0 := by
    have h := congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) hyy
    simpa using h
  have hx1 : x 1 = x' 1 := by
    have h := congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) hyy
    simpa using h
  -- ## Step 2: the scale factors agree, whence `ψ (x 2) = ψ (x' 2)` and `x 2 = x' 2`
  have hlog : Real.log c - Real.log (levelOf (P (mk2 (x' 0) (x' 1)))) ≠ 0 := by
    intro h0
    have h1 : Real.log c = Real.log (levelOf (P (mk2 (x' 0) (x' 1)))) := sub_eq_zero.mp h0
    have h2 : c = levelOf (P (mk2 (x' 0) (x' 1))) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hc) (Set.mem_Ioi.mpr (levelOf_pos _)) h1
    exact hlev _ hy' h2.symm
  have hscale : clampScale c ψ P x = clampScale c ψ P x' := by
    have h := congrArg levelOf heq
    rw [levelOf_clampedSweep, levelOf_clampedSweep, hyy] at h
    exact mul_right_cancel₀ (ne_of_gt (levelOf_pos (P (mk2 (x' 0) (x' 1))))) h
  have hψeq : ψ (x 2) = ψ (x' 2) := by
    have h := hscale
    rw [clampScale, clampScale, hyy] at h
    exact mul_right_cancel₀ hlog (Real.exp_injective h)
  have hx2 : x 2 = x' 2 := hψ (hx 2) (hx' 2) hψeq
  -- ## Step 3: conclude
  rw [WithLp.ext_iff]
  funext i
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hx2

end Work.Drive
