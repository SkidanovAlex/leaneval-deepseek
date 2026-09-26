import Submission.Work.SurgeryInvariance.Core
import Submission.Work.InnermostDisk.Defs

/-!
# A loop inside an embedded disc is null-homotopic (the homotopy, explicitly)

`Work.SurgeryInvariance.DiscRegion.not_isEssential` says that a closed curve of the torus lying in
an embedded disc `D` of the surface is inessential.  This module strengthens it to the *homotopy*:

> a loop `γ` whose image lies in `D.carrier` is freely homotopic to the constant loop at any point
> `D.e w` of the disc.

The homotopy is the obvious one: `D.e` is a homeomorphism onto its (compact) image, so `γ` can be
transported to a curve `z` of the closed disc, and the convexity of the disc gives the linear
homotopy `(s, t) ↦ D.e ((1 - clamp s) • z t + clamp s • w)`.  The clamping of `s` to `[0,1]` is what
makes the family defined for all real `s`, as `Work.CoreTopology.Homotopic` requires.

This is the key ingredient for the *disc push-off* (`DiscRoute`): the case of a loop that lies
entirely inside the disc is exactly this null-homotopy, with the constant taken at a *boundary*
point so that the target loop avoids the interior of the disc.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- The clamping of a real number to `[0,1]`. -/
def clamp (s : ℝ) : ℝ := max 0 (min 1 s)

theorem clamp_mem_Icc (s : ℝ) : clamp s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clamp_zero : clamp 0 = 0 := by simp [clamp]

theorem clamp_one : clamp 1 = 1 := by simp [clamp]

theorem clamp_eq_self {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : clamp s = s := by
  rw [clamp, min_eq_right hs.2, max_eq_right hs.1]

theorem continuous_clamp : Continuous clamp := by
  show Continuous (fun s : ℝ => max 0 (min 1 s))
  fun_prop

/-- **A loop inside an embedded disc of the surface is homotopic to the constant loop at any
point of the disc.** -/
theorem homotopic_constCurve_of_range_subset_discRegion
    {P : Work.CoreTopology.ParamTorus} (D : Work.SurgeryInvariance.DiscRegion P)
    (γ : Work.CoreTopology.ClosedCurve P) (hγ : ∀ t : ℝ, γ t ∈ D.carrier)
    (w : Metric.closedBall (0 : ℂ) 1) :
    Work.CoreTopology.Homotopic P γ
      (Work.InnermostDisk.constCurve P (D.e w) (D.mem w)) := by
  -- the bijection of the closed disc onto the carrier of `D`
  let E : Metric.closedBall (0 : ℂ) 1 ≃ D.carrier := Equiv.ofInjective D.e D.inj
  have hEcont : Continuous (fun z : Metric.closedBall (0 : ℂ) 1 => (E z : D.carrier)) := by
    have hfun : (fun z : Metric.closedBall (0 : ℂ) 1 => (E z : D.carrier)) =
        fun z => (⟨D.e z, ⟨z, rfl⟩⟩ : D.carrier) := rfl
    rw [hfun]
    exact Continuous.subtype_mk D.e.continuous (fun z => ⟨z, rfl⟩)
  let φ : Metric.closedBall (0 : ℂ) 1 ≃ₜ D.carrier :=
    Continuous.homeoOfEquivCompactToT2 hEcont
  have hφval : ∀ z : Metric.closedBall (0 : ℂ) 1, ((φ z : D.carrier) : R3) = D.e z := fun z => rfl
  -- transport the loop to the closed disc
  let z : ℝ → Metric.closedBall (0 : ℂ) 1 := fun t => φ.symm ⟨γ t, hγ t⟩
  have hze : ∀ t : ℝ, D.e (z t) = γ t := by
    intro t
    have h := Homeomorph.apply_symm_apply φ (⟨γ t, hγ t⟩ : D.carrier)
    have h2 := congrArg (fun q : D.carrier => (q : R3)) h
    rw [show ((φ (φ.symm ⟨γ t, hγ t⟩) : D.carrier) : R3) = D.e (z t) from hφval (z t)] at h2
    rw [h2]
  have hzcont : Continuous z :=
    φ.symm.continuous.comp (γ.cont.subtype_mk hγ)
  have hzper : ∀ t : ℝ, z (t + 2 * Real.pi) = z t := by
    intro t
    show φ.symm ⟨γ (t + 2 * Real.pi), hγ (t + 2 * Real.pi)⟩ = φ.symm ⟨γ t, hγ t⟩
    exact congrArg φ.symm (Subtype.ext (γ.periodic t))
  -- the convex-combination map, clamped so that it is defined for every real time
  let comb : ℝ → Metric.closedBall (0 : ℂ) 1 → Metric.closedBall (0 : ℂ) 1 := fun c u =>
    ⟨(1 - clamp c) • (u : ℂ) + (clamp c) • (w : ℂ), by
      have hc := clamp_mem_Icc c
      exact (convex_iff_add_mem.mp (convex_closedBall (0 : ℂ) 1)) u.2 w.2
        (sub_nonneg.mpr hc.2) hc.1 (by ring)⟩
  have hcomb0 : ∀ u : Metric.closedBall (0 : ℂ) 1, comb 0 u = u := by
    intro u
    apply Subtype.ext
    simp [comb, clamp]
  have hcomb1 : ∀ u : Metric.closedBall (0 : ℂ) 1, comb 1 u = w := by
    intro u
    apply Subtype.ext
    simp [comb, clamp]
  have hcombcont : Continuous (fun p : ℝ × ℝ => comb p.1 (z p.2)) := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_clamp.comp continuous_fst)).smul
      (continuous_subtype_val.comp (hzcont.comp continuous_snd))).add
      ((continuous_clamp.comp continuous_fst).smul continuous_const)
  have hcompper : ∀ (c : ℝ) (t : ℝ), comb c (z (t + 2 * Real.pi)) = comb c (z t) :=
    fun c t => congrArg (comb c) (hzper t)
  refine ⟨fun s t => D.e (comb s (z t)), ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of the homotopy
    exact D.e.continuous.comp hcombcont
  · -- the homotopy stays on the surface
    intro s t
    exact D.mem _
  · -- at time `0` the loop is `γ`
    intro t
    show D.e (comb 0 (z t)) = γ t
    rw [hcomb0 (z t), hze t]
  · -- at time `1` the loop is the constant loop at `D.e w`
    intro t
    show D.e (comb 1 (z t)) = D.e w
    rw [hcomb1 (z t)]
  · -- `2π`-periodicity in `t`
    intro s t
    show D.e (comb s (z (t + 2 * Real.pi))) = D.e (comb s (z t))
    rw [hcompper s t]

end

end Work.BoxShrink.PinchOff
