import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.sideGerm_parity_local
import Submission.Work.Drive.parityChainSmooth
import Submission.Work.Drive.rotCappingSmooth
import Submission.Work.Drive.sideGermSepDefs

/-!
# The count `CntAt` is locally constant at a good configuration

This file proves `Work.Drive.CntAt_locallyConstant`: the design's count
`CntAt Ξ Q c w t = #(coreMeet (Ξ t.1 ∘ Q) c (rot w ∘ Ξ t.2 ∘ Q))` is constant on a whole
neighbourhood of any configuration `(w, t)` at which the perturbed pair is a `GoodPair` — both in the
two chart-perturbation parameters `t` and in the angle `w`.

The mathematical content is the *local constancy of the number of parameter meets* of a loop against a
`3`-chain in the `4`-manifold `CappingSpace`, along a family in which the loop, the sweep, **and the
angle of the rotation** all move.  The engine of
`Work.Drive.eventually_ncard_meetBox_eq_manifold` (`sideGerm_parity_local.lean`) already does this for
an arbitrary normed parameter space `P`: applied to the parameter space `P := (𝔼^m × 𝔼^m) × ℝ`
(the two chart shifts and the angle *shift*), it gives the constancy in the joint parameter.

So the only work of this file is

* to write down the joint family (`lcLoop`, `lcPlane`, `lcChain` below: the loop is the core loop of
  the shifted chart, the chain is the clamped sweep of the rotated shifted chart, the rotation angle
  being `w₀ + u.2` for a fixed lift `w₀` of the angle `w`),
* to prove its joint smoothness — the two inputs are `Work.Drive.contMDiffAt_rotCapping_comp` (the
  rotation is smooth in a *normed* angle parameter, by the smooth action of `S¹` on the capping
  space) and `Work.Drive.contMDiff_clampedSweep_family_gen` (joint smoothness of a family of clamped
  sweeps),
* and to translate the `∀ᶠ` conclusion of the engine back into the `∃ ρ > 0` form of the statement: for
  `w'` at distance `< ρ` from `w` one picks a lift `w₀ + s` of `w'` with `|s| = dist w' w`
  (`Work.Drive.sep_exists_lift_pair`), and the parameter `((t'.1 - t.1, t'.2 - t.2), s)` has norm
  `max ‖t' - t‖ (dist w' w) < ρ`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

variable {m : ℕ}

/-! ## The joint family -/

/-- The parameter space of the joint family: the two chart perturbations and the angle *shift*. -/
abbrev lcPar (m : ℕ) := (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ

/-- The loop of the joint family: the core loop of the chart perturbed by the first parameter. -/
def lcLoop (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (u : lcPar m) : ℝ → CappingSpace :=
  fun t' => coreLoop (pertChart Ξ Q (t.1 + u.1.1)) t'

/-- The plane presentation of the joint family: the disk presentation of the chart perturbed by the
second parameter, rotated by the angle `w₀ + u.2`. -/
def lcPlane (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w₀ : ℝ)
    (u : lcPar m) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun y => rotCapping (((w₀ + u.2 : ℝ)) : UnitAddCircle)
    (pertChart Ξ Q (t.2 + u.1.2) (sqDisk (foldBox y)))

/-- The chain of the joint family: the clamped sweep of the rotated perturbed chart. -/
def lcChain (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w₀ : ℝ)
    (u : lcPar m) : EuclideanSpace ℝ (Fin 3) → CappingSpace :=
  fun x => clampedSweep c (fun s => 1 - s) (lcPlane Ξ Q t w₀ u) x

/-! ## Joint smoothness of the family -/

/-- **The loop family is jointly `C^∞`.** -/
theorem lcLoop_contMDiff
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, lcPar m × ℝ)) (𝓡 4) Ctop
      (fun q : lcPar m × ℝ => lcLoop Ξ Q t q.1 q.2) := by
  have hpt : ContMDiff (𝓘(ℝ, lcPar m × ℝ)) (𝓘(ℝ, ℂ)) Ctop
      (fun q : lcPar m × ℝ =>
        Complex.exp ((Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I)) := by
    have h2 : ContDiff ℝ Ctop (fun q : lcPar m × ℝ => ((q.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop)
    have hlin : ContDiff ℝ Ctop
        (fun q : lcPar m × ℝ => (Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I) :=
      (contDiff_const.mul h2).mul contDiff_const
    exact contMDiff_iff_contDiff.mpr (Complex.contDiff_exp.comp hlin)
  have hQ5 : ContMDiff (𝓘(ℝ, lcPar m × ℝ)) (𝓡 4) Ctop
      (fun q : lcPar m × ℝ =>
        Q (Complex.exp ((Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I))) :=
    hQ.comp hpt
  have hfst : ContMDiff (𝓘(ℝ, lcPar m × ℝ)) (𝓡 m) Ctop
      (fun q : lcPar m × ℝ => t.1 + q.1.1.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hmain := hΞ.2.1.comp (hfst.prodMk hQ5)
  refine hmain.congr fun q => ?_
  simp only [Function.comp_def, coreLoop, pertChart, lcLoop]

/-- **The plane-presentation family is jointly `C^∞`.** -/
theorem lcPlane_contMDiff
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w₀ : ℝ) :
    ContMDiff (𝓘(ℝ, lcPar m × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : lcPar m × EuclideanSpace ℝ (Fin 2) => lcPlane Ξ Q t w₀ q.1 q.2) := by
  intro q₀
  refine Work.Drive.contMDiffAt_rotCapping_comp (I := 𝓘(ℝ, lcPar m × EuclideanSpace ℝ (Fin 2)))
    (fun q : lcPar m × EuclideanSpace ℝ (Fin 2) => Ξ (t.2 + q.1.1.2) (diskPlane Q q.2))
    (fun q : lcPar m × EuclideanSpace ℝ (Fin 2) => w₀ + q.1.2) q₀ ?_ ?_
  · have h1 : ContMDiffAt (𝓘(ℝ, lcPar m × EuclideanSpace ℝ (Fin 2))) (𝓡 m) Ctop
        (fun q : lcPar m × EuclideanSpace ℝ (Fin 2) => t.2 + q.1.1.2) q₀ :=
      (contMDiff_iff_contDiff.mpr (by fun_prop)).contMDiffAt
    have h2 : ContMDiffAt (𝓘(ℝ, lcPar m × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
        (fun q : lcPar m × EuclideanSpace ℝ (Fin 2) => diskPlane Q q.2) q₀ :=
      ((contMDiff_diskPlane hQ).comp (contMDiff_iff_contDiff.mpr (by fun_prop))).contMDiffAt
    have h3 := hΞ.2.1.contMDiffAt.comp q₀ (h1.prodMk h2)
    refine h3.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext q
    simp only [Function.comp_def, pertChart, diskPlane]
  · exact (contMDiff_iff_contDiff.mpr (by fun_prop)).contMDiffAt

/-- **The chain family is jointly `C^∞`.** -/
theorem lcChain_contMDiff
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w₀ : ℝ) :
    ContMDiff (𝓘(ℝ, lcPar m × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : lcPar m × EuclideanSpace ℝ (Fin 3) => lcChain Ξ Q c t w₀ q.1 q.2) := by
  have h := contMDiff_clampedSweep_family_gen (P := lcPar m) c (fun s : ℝ => 1 - s)
    (by fun_prop) (fun u => lcPlane Ξ Q t w₀ u) (lcPlane_contMDiff Ξ Q hΞ hQ t w₀)
  simpa only [lcChain] using h

/-! ## The shift of the angle -/

/-- **A shift realising a nearby angle.**  If `w₀` is a lift of `w`, then for every `w'` there is a
real shift `s` with `|s| = dist w' w` and `w₀ + s` a lift of `w'`.  (The two lifts of
`Work.Drive.sep_exists_lift_pair` are compared through the fixed lift `w₀`.) -/
lemma exists_shift_of_coe_eq {w₀ : ℝ} {w : UnitAddCircle}
    (hw₀ : ((w₀ : ℝ) : UnitAddCircle) = w) (w' : UnitAddCircle) :
    ∃ s : ℝ, |s| = dist w' w ∧ ((w₀ + s : ℝ) : UnitAddCircle) = w' := by
  obtain ⟨a, a', ha, ha', hd⟩ := sep_exists_lift_pair w w'
  refine ⟨a' - a, ?_, ?_⟩
  · rw [← hd]
  · rw [AddCircle.coe_add, AddCircle.coe_sub, hw₀, ha, ha']
    abel

/-! ## The main theorem -/

theorem CntAt_locallyConstant {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsSmoothChart Q) (hc : 0 < c)
    (w : UnitAddCircle) (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (ht : Work.Drive.GoodAt Ξ Q c w t) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖t' - t‖ < ρ → dist w' w < ρ →
          Work.Drive.CntAt Ξ Q c w' t' = Work.Drive.CntAt Ξ Q c w t := by
  classical
  -- a lift of the angle `w`
  obtain ⟨w₀, hw₀⟩ := Quotient.mk''_surjective w
  have hw₀' : ((w₀ : ℝ) : UnitAddCircle) = w := hw₀
  -- the two curves of the joint family
  set L : lcPar m → ℝ → CappingSpace := lcLoop Ξ Q t with hLdef
  set D : lcPar m → EuclideanSpace ℝ (Fin 3) → CappingSpace := lcChain Ξ Q c t w₀ with hDdef
  -- ## the base identifications
  have hzero1 : (0 : lcPar m).1.1 = 0 := rfl
  have hzero2 : (0 : lcPar m).1.2 = 0 := rfl
  have hzero3 : (0 : lcPar m).2 = 0 := rfl
  have hP0 : lcPlane Ξ Q t w₀ (0 : lcPar m) = rotPresentation (pertChart Ξ Q t.2) w := by
    funext y
    simp only [lcPlane]
    rw [hzero2, hzero3, add_zero, add_zero]
    rw [show ((w₀ : ℝ) : UnitAddCircle) = w from hw₀']
    rfl
  have hL0 : L 0 = coreLoop (pertChart Ξ Q t.1) := by
    rw [hLdef]
    funext y
    simp only [lcLoop]
    rw [hzero1, add_zero]
  have hD0 : D 0
      = clampedSweep c (fun s => 1 - s) (rotPresentation (pertChart Ξ Q t.2) w) := by
    rw [hDdef]
    show clampedSweep c (fun s => 1 - s) (lcPlane Ξ Q t w₀ 0)
      = clampedSweep c (fun s => 1 - s) (rotPresentation (pertChart Ξ Q t.2) w)
    rw [hP0]
  have hmeet0 : meetBox (L 0) (D 0)
      = coreMeet (pertChart Ξ Q t.1) c (rotPresentation (pertChart Ξ Q t.2) w) := by
    rw [hL0, hD0]
    rfl
  -- ## the regularity data at the base configuration
  obtain ⟨-, -, hfin0, hint0, htrans0⟩ := ht
  have hfin : (meetBox (L 0) (D 0)).Finite := by rw [hmeet0]; exact hfin0
  have hint : ∀ p ∈ meetBox (L 0) (D 0),
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro p hp
    rw [hmeet0] at hp
    exact hint0 p hp
  have htrans : ∀ p ∈ meetBox (L 0) (D 0),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (L 0) p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (D 0) p.2).toLinearMap = ⊤ := by
    intro p hp
    rw [hmeet0] at hp
    rw [hL0, hD0]
    exact htrans0 p hp
  -- ## joint smoothness
  have hLsm : ContMDiff (𝓘(ℝ, lcPar m × ℝ)) (𝓡 4) Ctop
      (fun q : lcPar m × ℝ => L q.1 q.2) := by
    rw [hLdef]
    exact lcLoop_contMDiff Ξ Q hΞ hQ t
  have hDsm : ContMDiff (𝓘(ℝ, lcPar m × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : lcPar m × EuclideanSpace ℝ (Fin 3) => D q.1 q.2) := by
    rw [hDdef]
    exact lcChain_contMDiff Ξ Q c hΞ hQ t w₀
  -- ## the engine
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp
    (eventually_ncard_meetBox_eq_manifold (P := lcPar m) L D hLsm hDsm hfin hint htrans)
  refine ⟨ρ, hρpos, ?_⟩
  intro t' w' ht' hw'
  -- a lift of `w'` at distance `dist w' w` from the fixed lift `w₀`
  obtain ⟨s, hs1, hs2⟩ := exists_shift_of_coe_eq hw₀' w'
  set u : lcPar m := ((t'.1 - t.1, t'.2 - t.2), s) with hudef
  have hu1 : u.1.1 = t'.1 - t.1 := by rw [hudef]
  have hu2 : u.1.2 = t'.2 - t.2 := by rw [hudef]
  have hu3 : u.2 = s := by rw [hudef]
  have hnorm : ‖u‖ < ρ := by
    have h1 : ‖t'.1 - t.1‖ ≤ ‖t' - t‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have h2 : ‖t'.2 - t.2‖ ≤ ‖t' - t‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hs : |s| < ρ := by rw [hs1]; exact hw'
    have key : ‖u‖ = max (max ‖t'.1 - t.1‖ ‖t'.2 - t.2‖) |s| := by
      rw [hudef]
      simp only [Prod.norm_def, Real.norm_eq_abs]
    rw [key]
    exact max_lt (max_lt (lt_of_le_of_lt h1 ht') (lt_of_le_of_lt h2 ht')) hs
  have hev : (meetBox (L u) (D u)).ncard = (meetBox (L 0) (D 0)).ncard :=
    hρ (by rw [Metric.mem_ball, dist_zero_right]; exact hnorm)
  -- the two curves at the shifted parameter
  have hLu : L u = coreLoop (pertChart Ξ Q t'.1) := by
    rw [hLdef]
    funext y
    simp only [lcLoop]
    rw [hu1, show t.1 + (t'.1 - t.1) = t'.1 from by abel]
  have hP : lcPlane Ξ Q t w₀ u = rotPresentation (pertChart Ξ Q t'.2) w' := by
    funext y
    simp only [lcPlane]
    rw [hu2, show t.2 + (t'.2 - t.2) = t'.2 from by abel, hu3, hs2]
    rfl
  have hDu : D u = clampedSweep c (fun s => 1 - s) (rotPresentation (pertChart Ξ Q t'.2) w') := by
    rw [hDdef]
    show clampedSweep c (fun s => 1 - s) (lcPlane Ξ Q t w₀ u)
      = clampedSweep c (fun s => 1 - s) (rotPresentation (pertChart Ξ Q t'.2) w')
    rw [hP]
  -- the two counts
  have hb : CntAt Ξ Q c w t = (meetBox (L 0) (D 0)).ncard := by
    show (coreMeet (pertChart Ξ Q t.1) c (rotPresentation (pertChart Ξ Q t.2) w)).ncard = _
    rw [← hmeet0]
  have ha : CntAt Ξ Q c w' t' = (meetBox (L u) (D u)).ncard := by
    show (coreMeet (pertChart Ξ Q t'.1) c (rotPresentation (pertChart Ξ Q t'.2) w')).ncard = _
    rw [hLu, hDu]
    rfl
  rw [ha, hev, ← hb]


end

end Work.Drive
