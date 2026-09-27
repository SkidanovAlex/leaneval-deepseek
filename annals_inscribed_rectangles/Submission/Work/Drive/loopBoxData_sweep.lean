import Mathlib
import Submission.Work.Drive.boxThreeDefs
import Submission.Work.Drive.boxThree_of_good_family
import Submission.Work.Drive.sgGoodChain_of_small_shift_sweep
import Submission.Work.Drive.t5FaceAvoid
import Submission.Work.Drive.contMDiff_loopFam
import Submission.Work.Drive.sideGermDefs

/-!
# The box-restricted regularity data of the two T5 loop families against a shifted sweep

For the two deformation families of the radial-collapse transport (`diamFam Q θ`, the straight-line
interpolation from the diameter loop to the half-circle loop, and `arcFam Q θ`, the rotation family)
against a clamped sweep of a *chart-perturbed* plane presentation, there is a shift `p` of the
perturbation parameter, of norm `< ε`, at which **both** families satisfy the box-restricted loop
regularity data `Work.Drive.LoopBoxData` against the same sweep.

This is the analytic content of `Work.Drive.exists_diamFamRegBox_of_small_shift`: the two families
share the chain, so their genericity data have to be produced at **one** parameter, which is what the
multi-family parametric Sard `Work.Drive.boxThree_of_good_family` supplies.  The hypotheses of the
Sard (smoothness of the chain family and the surjectivity of its charted parameter-derivative at
meets) are discharged here from `Work.Drive.contMDiff_sggSweepFam` and
`Work.Drive.hsurj_sggSweepFam`, the level band `levelOf (Q z) > c` on the disk being what rules out
the radial faces of the sweep (`(cbPart y) 2 = 0`), exactly as in
`Work.Drive.sgGoodChain_of_small_shift_sweep`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

theorem exists_loopBoxData_of_small_shift {m : Nat} (Q : ℂ → CappingSpace) (hQ : IsSmoothChart Q)
    (theta c : ℝ) (hc : 0 < c) (hlevQ : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z))
    (Xi : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q0 : ℂ → CappingSpace) (hXi : ChartPert Q0 m Xi) (hQ0 : IsSmoothChart Q0)
    (w : UnitAddCircle) (s0 : EuclideanSpace ℝ (Fin m)) (e0 : ℝ) (he0 : 0 < e0) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < e0 ∧
      LoopBoxData (diamFam Q theta)
        (clampedSweep c (fun s : ℝ => 1 - s)
          (diskPlane (pertChart Xi (fun z => rotCapping w (Q0 z)) (s0 + p)))) ∧
      LoopBoxData (arcFam Q theta)
        (clampedSweep c (fun s : ℝ => 1 - s)
          (diskPlane (pertChart Xi (fun z => rotCapping w (Q0 z)) (s0 + p)))) := by
  classical
  let Qw : ℂ → CappingSpace := fun z => rotCapping w (Q0 z)
  have hQw : IsSmoothChart Qw := by
    show ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => rotCapping w (Q0 z))
    exact (contMDiff_rotCapping_const w).comp hQ0
  let G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun t x => clampedSweep c (fun s => 1 - s) (diskPlane (pertChart Xi Qw (s0 + t))) x
  have hGsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2) :=
    contMDiff_sggSweepFam Xi Qw c hXi hQw s0
  -- the level bands of the two loop families
  have hlevD : ∀ u ∈ Submission.Drive.unitBox 1, c < levelOf (diamFam Q theta u) := by
    intro u hu
    obtain ⟨z, hz, hzu⟩ := diamFam_mem_closedDisk (Q := Q) theta hu
    rw [hzu]
    exact hlevQ z hz
  have hlevA : ∀ u ∈ Submission.Drive.unitBox 1, c < levelOf (arcFam Q theta u) := by
    intro u _
    obtain ⟨z, hz, hzu⟩ := arcFam_mem_circle (Q := Q) theta u
    rw [hzu]
    exact hlevQ z (le_of_eq hz)
  -- the two-element family of loops
  let A : Fin 2 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun i => Fin.cases (diamFam Q theta) (fun _ : Fin 1 => arcFam Q theta) i
  have hAlev : ∀ (i : Fin 2) (u : EuclideanSpace ℝ (Fin 2)), u ∈ Submission.Drive.unitBox 1 →
      c < levelOf (A i u) := by
    intro i u hu
    fin_cases i
    · exact hlevD u hu
    · exact hlevA u hu
  have hAsm : ∀ i : Fin 2, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (A i) := by
    intro i
    fin_cases i
    · exact contMDiff_diamFam hQ theta
    · exact contMDiff_arcFam hQ theta
  -- the parameter-surjectivity of the chain family at meets in the box
  have hsurj : ∀ (i : Fin 2) (t : EuclideanSpace ℝ (Fin m)) (y : Amb 4),
      y ∈ Submission.Drive.unitBox 4 → A i (sqPart y) = G t (cbPart y) →
      ∀ (p : CappingSpace), G t (cbPart y) ∈ (chr p).source →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (G t' (cbPart y))) t) := by
    intro i t y hy heq p hsrc
    have hy1 : sqPart y ∈ Submission.Drive.unitBox 1 := ((mem_unitBox_five_iff y).mp hy).1
    -- the radial parameter of the sweep does not vanish at a meet (level band)
    have hx2 : (cbPart y) 2 ≠ 0 := by
      intro h2
      have hlvlG : levelOf (G t (cbPart y)) = c :=
        levelOf_sggSweep_face_zero c hc (diskPlane (pertChart Xi Qw (s0 + t))) (cbPart y) h2
      have hlvlA : levelOf (A i (sqPart y)) = c := by rw [heq]; exact hlvlG
      have hgt := hAlev i (sqPart y) hy1
      rw [hlvlA] at hgt
      exact absurd hgt (lt_irrefl c)
    -- the two shapes of the chain family
    have hGfam : ∀ t' : EuclideanSpace ℝ (Fin m),
        G t' = clampedSweep c (fun s => 1 - s)
          (fun y' => Xi (s0 + t') (diskPlane Qw y')) := by
      intro t'
      show clampedSweep c (fun s => 1 - s) (diskPlane (pertChart Xi Qw (s0 + t')))
        = clampedSweep c (fun s => 1 - s) (fun y' => Xi (s0 + t') (diskPlane Qw y'))
      rfl
    have hsrc' : clampedSweep c (fun s => 1 - s)
        (fun y' => Xi (s0 + t) (diskPlane Qw y')) (cbPart y) ∈ (chr p).source := by
      rw [← hGfam t]
      exact hsrc
    have h := hsurj_sggSweepFam Xi Qw c hc hXi hQw s0 (cbPart y) hx2 t p hsrc'
    simpa only [← hGfam] using h
  -- the multi-family parametric Sard
  obtain ⟨p, hp, hpall⟩ := boxThree_of_good_family (M := CappingSpace) (m := m) (ι := Fin 2)
    A hAsm G hGsm (0 : EuclideanSpace ℝ (Fin m)) e0 he0 hsurj
  have hGp : G (0 + p) = clampedSweep c (fun s : ℝ => 1 - s)
      (diskPlane (pertChart Xi (fun z => rotCapping w (Q0 z)) (s0 + p))) := by
    show clampedSweep c (fun s : ℝ => 1 - s)
        (diskPlane (pertChart Xi Qw (s0 + (0 + p)))) = _
    rw [zero_add]
  refine ⟨p, hp, ?_, ?_⟩
  · have h := hpall 0
    rw [hGp] at h
    exact loopBoxData_of_boxThree h
  · have h := hpall 1
    rw [hGp] at h
    exact loopBoxData_of_boxThree h

end

end Work.Drive
