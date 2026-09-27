import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.contMDiff_rotCapping_family
import Submission.Work.Drive.parityChainSmooth

/-!
# The two-parameter family of the germ count's parity locality

`Work.Drive.sideGerm_parity_local` must show that at a *good* configuration `A` the parity of the
count `Work.Drive.CntAt Ξ Q c w` is locally constant in the configuration parameters.  This file fixes
the two curves along which the counting engine `Work.Drive.evergetually_ncard_meetBox_eq_manifold`
(`Submission/Work/Drive/sideGerm_parity_local.lean`) is applied: with the parameter space
`𝔼^m × 𝔼^m` (the loop's chart perturbation and the sweep's chart perturbation are *independent*),

> `parityLoopFam Ξ Q A u t  = coreLoop (pertChart Ξ Q (A.1 + u.1)) t`,
> `parityChainFam Ξ Q c w A u x = clampedSweep c (1 - ·) (rotPresentation (pertChart Ξ Q (A.2 + u.2)) w) x`,

so that `meetBox (parityLoopFam Ξ Q A u) (parityChainFam Ξ Q c w A u)` is definitionally `coreMeet` of
the perturbed pair at the configuration `A + u`, i.e. the meet set whose cardinality is
`Work.Drive.CntAt Ξ Q c w (A + u)`.

The file also contains the joint smoothness of the two families in the parameter *and* the curve
parameter (`parityLoopFam_contMDiff`, `parityChainFam_contMDiff`), which are the hypotheses `hL`/`hD` of
the engine, and `CntAt_eq_ncard_meetBox`, the identification of the count with the cardinality of the
engine's meet set.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

variable {m : ℕ}

/-! ## The family -/

/-- **The loop family**: the core loop of the chart perturbed by the first parameter. -/
def parityLoopFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) → ℝ → CappingSpace :=
  fun u t => coreLoop (pertChart Ξ Q (A.1 + u.1)) t

/-- **The sweep family**: the clamped sweep of the rotated chart perturbed by the second parameter. -/
def parityChainFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
  fun u x => clampedSweep c (fun s => 1 - s) (rotPresentation (pertChart Ξ Q (A.2 + u.2)) w) x

@[simp] lemma parityLoopFam_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    parityLoopFam Ξ Q A u t = coreLoop (pertChart Ξ Q (A.1 + u.1)) t := rfl

@[simp] lemma parityChainFam_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin 3)) :
    parityChainFam Ξ Q c w A u x
      = clampedSweep c (fun s => 1 - s) (rotPresentation (pertChart Ξ Q (A.2 + u.2)) w) x := rfl

@[simp] lemma parityLoopFam_zero (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    parityLoopFam Ξ Q A 0 = coreLoop (pertChart Ξ Q A.1) := by
  funext t; simp

@[simp] lemma parityChainFam_zero (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    parityChainFam Ξ Q c w A 0
      = clampedSweep c (fun s => 1 - s) (rotPresentation (pertChart Ξ Q A.2) w) := by
  funext x; simp

/-- **The engine's meet set is the design's `coreMeet`** at the perturbed configuration `A + u`:
`meetBox` of the two families is the meet set of the core loop of the perturbed chart with the clamped
sweep of the rotated perturbed chart. -/
theorem meetBox_parityFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    meetBox (parityLoopFam Ξ Q A u) (parityChainFam Ξ Q c w A u)
      = coreMeet (pertChart Ξ Q (A + u).1) c (rotPresentation (pertChart Ξ Q (A + u).2) w) := rfl

/-- **The count is the engine's cardinality**: `CntAt` at the perturbed configuration `A + u` is the
number of points of the engine's meet box. -/
theorem CntAt_eq_ncard_meetBox (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    CntAt Ξ Q c w (A + u)
      = (meetBox (parityLoopFam Ξ Q A u) (parityChainFam Ξ Q c w A u)).ncard := rfl

/-! ## Joint smoothness of the two families -/

/-- **The rotation of the capping space by a fixed angle is smooth** (a local copy of
`Work.Drive.contMDiff_rotCapping_const`, to keep this file's imports light). -/
lemma contMDiff_rotCappingAngle (w : UnitAddCircle) :
    ContMDiff (𝓡 4) (𝓡 4) Ctop (fun p : CappingSpace => rotCapping w p) := by
  obtain ⟨t, ht⟩ := Quotient.mk''_surjective w
  intro p
  have h := contMDiffAt_rotCapping_comp (I := 𝓡 4) (id : CappingSpace → CappingSpace)
    (fun _ : CappingSpace => t) p contMDiffAt_id contMDiffAt_const
  simpa [ht] using h

/-- **The plane-presentation family of the chain side is jointly `C^∞`**: the rotated disk presentation
of the perturbed chart, as a function of the configuration parameter and the plane parameter. -/
lemma contMDiff_rotPresentation_pertChart
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (w : UnitAddCircle)
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2) =>
        rotPresentation (pertChart Ξ Q (A.2 + q.1.2)) w q.2) := by
  have hinner : ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2) =>
        Ξ (A.2 + q.1.2) (diskPlane Q q.2)) := by
    have h1 : ContMDiff
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 m) Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2) =>
          A.2 + q.1.2) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    have hdp : ContMDiff (𝓡 2) (𝓡 4) Ctop (diskPlane Q) := contMDiff_diskPlane hQ.1
    have h2 : ContMDiff
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2) =>
          diskPlane Q q.2) :=
      hdp.comp (contMDiff_iff_contDiff.mpr (by fun_prop))
    exact hΞ.2.1.comp (h1.prodMk h2)
  have hrot := contMDiff_rotCappingAngle w
  refine (hrot.comp hinner).congr fun q => ?_
  simp only [Function.comp_def, rotPresentation, diskPlane, pertChart, Function.comp_apply]

/-- **The loop family is jointly `C^∞`**: the core loop of the perturbed chart, as a function of the
configuration parameter and the loop parameter. -/
theorem parityLoopFam_contMDiff
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ)) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
        parityLoopFam Ξ Q A q.1 q.2) := by
  have hpt : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ))
      (𝓘(ℝ, ℂ)) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
        Complex.exp ((Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I)) := by
    have h2 : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ => ((q.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop)
    have hlin : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
          (Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I) :=
      (contDiff_const.mul h2).mul contDiff_const
    exact contMDiff_iff_contDiff.mpr (Complex.contDiff_exp.comp hlin)
  have hQ5 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
        Q (Complex.exp ((Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I))) :=
    hQ.1.comp hpt
  have hfst : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ))
      (𝓡 m) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ => A.1 + q.1.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hmain := hΞ.2.1.comp (hfst.prodMk hQ5)
  refine hmain.congr fun q => ?_
  simp only [Function.comp_def, coreLoop, pertChart, parityLoopFam]

/-- **The sweep family is jointly `C^∞`**: the clamped sweep of the rotated perturbed chart, as a
function of the configuration parameter and the chain parameter. -/
theorem parityChainFam_contMDiff
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 3) =>
        parityChainFam Ξ Q c w A q.1 q.2) := by
  have hPp := contMDiff_rotPresentation_pertChart Ξ Q w hΞ hQ A
  have hmain := contMDiff_clampedSweep_family_gen
    (P := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    c (fun s : ℝ => 1 - s) (by fun_prop)
    (fun u (y : EuclideanSpace ℝ (Fin 2)) => rotPresentation (pertChart Ξ Q (A.2 + u.2)) w y) hPp
  simpa only [parityChainFam] using hmain

end

end Work.Drive
