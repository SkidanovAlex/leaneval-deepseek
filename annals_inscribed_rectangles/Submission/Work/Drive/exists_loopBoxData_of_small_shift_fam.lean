import Mathlib
import Submission.Work.Drive.classRowsSweepVocab

/-!
# The box-restricted regularity data of a finite family of loops against a shifted sweep

`Work.Drive.exists_loopBoxData_of_small_shift` (`Submission/Work/Drive/loopBoxData_sweep.lean`)
produces, for the **two** loop families of the radial-collapse transport, a single shift `p` of the
chart-perturbation parameter, of norm `< ε`, at which both satisfy `Work.Drive.LoopBoxData` against
the clamped sweep of the shifted, rotated, perturbed chart `Q₀`.

This file is its **finite-family** form: an arbitrary finite family `A : ι → ℝ² → CappingSpace` of
smooth plane presentations whose values on the unit box all lie in the levels `> c`.  The proof is
the same application of the multi-family parametric Sard `Work.Drive.boxThree_of_good_family` (which
is already stated for an arbitrary finite index type `ι`), with the two analytic inputs
`Work.Drive.contMDiff_sggSweepFam` and `Work.Drive.hsurj_sggSweepFam` supplying the smoothness of
the chain family and the parameter-surjectivity of its charted derivative at meets.  The level band
`c < levelOf (A i u)` rules out the radial faces of the sweep, exactly as in the two-family version.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

theorem exists_loopBoxData_of_small_shift_fam {m : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hA : ∀ i, Work.Drive.SmoothPlane₂ (A i))
    (c : ℝ) (hc : 0 < c)
    (hAlev : ∀ (i : ι) (u : EuclideanSpace ℝ (Fin 2)),
      u ∈ Submission.Drive.unitBox 1 → c < Work.Drive.levelOf (A i u))
    (Xi : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q0 : ℂ → Work.Drive.CappingSpace) (hXi : Work.Drive.ChartPert Q0 m Xi)
    (hQ0 : Work.Drive.IsSmoothChart Q0)
    (w : UnitAddCircle) (s0 : EuclideanSpace ℝ (Fin m)) (e0 : ℝ) (he0 : 0 < e0) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < e0 ∧ ∀ i : ι,
      Work.Drive.LoopBoxData (A i) (Work.Drive.clampedSweep c (fun s : ℝ => 1 - s)
        (Work.Drive.diskPlane (Work.Drive.pertChart Xi
          (fun z => Work.Drive.rotCapping w (Q0 z)) (s0 + p)))) := by
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
  have hAsm : ∀ i : ι, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (A i) :=
    fun i => hA i
  -- the parameter-surjectivity of the chain family at meets in the box
  have hsurj : ∀ (i : ι) (t : EuclideanSpace ℝ (Fin m)) (y : Amb 4),
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
  obtain ⟨p, hp, hpall⟩ := boxThree_of_good_family (M := CappingSpace) (m := m) (ι := ι)
    A hAsm G hGsm (0 : EuclideanSpace ℝ (Fin m)) e0 he0 hsurj
  have hGp : G (0 + p) = clampedSweep c (fun s : ℝ => 1 - s)
      (diskPlane (pertChart Xi (fun z => rotCapping w (Q0 z)) (s0 + p))) := by
    show clampedSweep c (fun s : ℝ => 1 - s)
        (diskPlane (pertChart Xi Qw (s0 + (0 + p)))) = _
    rw [zero_add]
  refine ⟨p, hp, ?_⟩
  intro i
  have h := hpall i
  rw [hGp] at h
  exact loopBoxData_of_boxThree h

end

end Work.Drive
