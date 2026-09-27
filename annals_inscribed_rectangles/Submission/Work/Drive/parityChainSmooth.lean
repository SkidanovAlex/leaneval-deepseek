import Mathlib
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff_general

/-!
# Joint smoothness of a *family* of clamped sweeps (general parameter space)

`Work.Drive.contMDiff_clampedSweep` (in `clampedSweep.lean`) proves the smoothness of a single clamped
sweep `clampedSweep c ψ P` in the *box* variable, for a fixed plane presentation `P`.  The parity
locality of `Work.Drive.sideGerm` deforms the plane presentation itself, so what is needed is the joint
smoothness in the presentation family and the box variable:

> `(q : P × 𝔼³) ↦ clampedSweep c ψ (Pp q.1) q.2` is `C^∞` when `(q : P × 𝔼²) ↦ Pp q.1 q.2` is.

This file proves it, together with the two general-parameter lemmas its proof needs (the analogues for a
normed source space `P` of `Work.Drive.contMDiffAt_log_levelOf` and
`Work.Drive.CapSmooth.contMDiffAt_scaleCapping`):

* `Work.Drive.contMDiffAt_log_levelOf_gen` — `x ↦ log (levelOf (f x))` is smooth whenever `f` is;
* `Work.Drive.contMDiffAt_scaleCapping_gen` — `x ↦ scaleCapping ⟨A x, ·⟩ (F x)` is smooth;
* `Work.Drive.contMDiff_clampedSweep_family_gen` — **the family form**.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.projCharted Work.Drive.halfLineProjectiveCharted

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

/-! ## The auxiliary smoothness of `mk2` -/

/-- The map `w ↦ mk2 (w 0) (w 1)` is `C^∞`. -/
lemma contDiff_mk2_proj :
    ContDiff ℝ Ctop (fun w : EuclideanSpace ℝ (Fin 3) => Work.Drive.mk2 (w 0) (w 1)) := by
  rw [show (fun w : EuclideanSpace ℝ (Fin 3) => Work.Drive.mk2 (w 0) (w 1))
      = fun w => WithLp.toLp 2 (![w 0, w 1] : Fin 2 → ℝ) from rfl]
  rw [contDiff_piLp (p := 2) (E := fun _ : Fin 2 => ℝ)]
  intro i
  fin_cases i
  · simpa using ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).contDiff (n := Ctop))
  · simpa using ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 1).contDiff (n := Ctop))

/-! ## The logarithm of the radial coordinate, for a general source -/

/-- **The logarithm of the radial coordinate of a smooth map into the capping space is smooth**, for a
normed source space `P`.  This is `Work.Drive.contMDiffAt_log_levelOf` with `𝓡 k` replaced by
`𝓘(ℝ, P)`, using the general component criterion
`Work.Drive.contMDiffAt_halfLineProjective_iff_general`. -/
theorem contMDiffAt_log_levelOf_gen {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : P → CappingSpace) (x₀ : P)
    (hf : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop f x₀) :
    ContMDiffAt (𝓘(ℝ, P)) 𝓘(ℝ, ℝ) Ctop (fun w => Real.log (levelOf (f w))) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  have hg : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop (fun w => cappingSpaceHomeoProj (f w)) x₀ := by
    have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := P) (H' := P) (𝓘(ℝ, P))
      (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := Ctop)
      Work.Drive.cappingSpaceHomeoProj.symm f Set.univ x₀
    exact hiff.mp hf
  obtain ⟨hρ, -⟩ := (Work.Drive.contMDiffAt_halfLineProjective_iff_general (𝓘(ℝ, P))
    (fun w => cappingSpaceHomeoProj (f w)) x₀).mp hg
  have key : (fun w => Real.log (levelOf (f w)))
      = fun w => Work.Drive.CapSmooth.euclLog (Work.Drive.expHomeo.symm
          ((fun w => cappingSpaceHomeoProj (f w)) w).1) := by
    funext w
    rw [levelOf, Work.Drive.expHomeo_symm_apply, Work.Drive.CapSmooth.euclLog_logEucl]
  rw [key, contMDiffAt_iff_contDiffAt]
  exact (Work.Drive.CapSmooth.euclLog.contDiff.contDiffAt).comp x₀
    (contMDiffAt_iff_contDiffAt.mp hρ)

/-! ## Smoothness of the radial dilation, for a general source -/

/-- **Smoothness of the radial dilation `x ↦ scaleCapping ⟨A x, ·⟩ (F x)`**, for a normed source
space `P`.  This is `Work.Drive.CapSmooth.contMDiffAt_scaleCapping` with `𝓡 k` replaced by
`𝓘(ℝ, P)`: the transfer along `cappingSpaceHomeoProj` is
`Work.Drive.chartedStructure_contMDiffWithinAt`, and the component criterion is
`Work.Drive.contMDiffAt_halfLineProjective_iff_general`. -/
theorem contMDiffAt_scaleCapping_gen {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → ℝ) (hA : ∀ w, 0 < A w) (F : P → CappingSpace) (x₀ : P)
    (hAs : ContMDiffAt (𝓘(ℝ, P)) 𝓘(ℝ, ℝ) Ctop A x₀)
    (hFs : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop F x₀) :
    ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop
      (fun w => scaleCapping ⟨A w, Set.mem_Ioi.mpr (hA w)⟩ (F w)) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := Work.Drive.projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) :=
    Homeomorph.chartedSpace Work.Drive.expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := Work.Drive.cappingCharted
  let g : P → Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => cappingSpaceHomeoProj (F w)
  have hg : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop g x₀ := by
    have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := P) (H' := P) (𝓘(ℝ, P))
      (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := Ctop)
      Work.Drive.cappingSpaceHomeoProj.symm F Set.univ x₀
    exact hiff.mp hFs
  obtain ⟨hρ, hq⟩ := (Work.Drive.contMDiffAt_halfLineProjective_iff_general (𝓘(ℝ, P)) g x₀).mp hg
  have hlogg : ContMDiffAt (𝓘(ℝ, P)) 𝓘(ℝ, ℝ) Ctop
      (fun w => Real.log ((g w).1 : ℝ)) x₀ := by
    have key : (fun w => Real.log ((g w).1 : ℝ))
        = fun w => Work.Drive.CapSmooth.euclLog (Work.Drive.expHomeo.symm (g w).1) := by
      funext w
      rw [Work.Drive.expHomeo_symm_apply, Work.Drive.CapSmooth.euclLog_logEucl]
    rw [key, contMDiffAt_iff_contDiffAt]
    exact (Work.Drive.CapSmooth.euclLog.contDiff.contDiffAt).comp x₀
      (contMDiffAt_iff_contDiffAt.mp hρ)
  have hlogA : ContDiffAt ℝ Ctop (fun w => Real.log (A w)) x₀ :=
    (Real.contDiffAt_log.mpr (ne_of_gt (hA x₀))).comp x₀ (contMDiffAt_iff_contDiffAt.mp hAs)
  let G : P → Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => (⟨A w * ((g w).1 : ℝ), Set.mem_Ioi.mpr (mul_pos (hA w) (g w).1.2)⟩, (g w).2)
  have hG1 : ContMDiffAt (𝓘(ℝ, P)) (𝓡 1) Ctop
      (fun w => Work.Drive.expHomeo.symm (G w).1) x₀ := by
    have key : (fun w => Work.Drive.expHomeo.symm (G w).1)
        = fun w => Work.Drive.logEucl (Real.log (A w) + Real.log ((g w).1 : ℝ)) := by
      funext w
      have hG1w : (G w).1 = (⟨A w * ((g w).1 : ℝ),
          Set.mem_Ioi.mpr (mul_pos (hA w) (g w).1.2)⟩ : Set.Ioi (0 : ℝ)) := rfl
      rw [hG1w, Work.Drive.expHomeo_symm_apply,
        Real.log_mul (ne_of_gt (hA w)) (ne_of_gt (g w).1.2)]
    rw [key, contMDiffAt_iff_contDiffAt]
    exact (Work.Drive.logEucl.contDiff.contDiffAt).comp x₀
      (hlogA.add (contMDiffAt_iff_contDiffAt.mp hlogg))
  have hG2 : ContMDiffAt (𝓘(ℝ, P)) (𝓡 3) Ctop (fun w => (G w).2) x₀ := by
    have key : (fun w => (G w).2) = fun w => (g w).2 := by funext w; rfl
    rw [key]
    exact hq
  have hG : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop G x₀ :=
    (Work.Drive.contMDiffAt_halfLineProjective_iff_general (𝓘(ℝ, P)) G x₀).mpr ⟨hG1, hG2⟩
  have hiffF := Work.Drive.chartedStructure_contMDiffWithinAt
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (E' := P) (H' := P) (𝓘(ℝ, P))
    (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := CappingSpace) (n := Ctop)
    Work.Drive.cappingSpaceHomeoProj.symm
    (fun w => scaleCapping ⟨A w, Set.mem_Ioi.mpr (hA w)⟩ (F w)) Set.univ x₀
  refine hiffF.mpr ?_
  have key : (fun y => (Work.Drive.cappingSpaceHomeoProj.symm).symm
        (scaleCapping ⟨A y, Set.mem_Ioi.mpr (hA y)⟩ (F y))) = G := by
    funext w
    rw [Homeomorph.symm_symm, Work.Drive.CapSmooth.cappingSpaceHomeoProj_scaleCapping]
  rw [key]
  exact hG

/-! ## The family of clamped sweeps -/

/-- **Joint smoothness of a family of clamped sweeps**: for a `C^∞` family of plane presentations
`Pp` on a normed parameter space `P`, the clamped sweep `(q, x) ↦ clampedSweep c ψ (Pp q) x` is
`C^∞`.  This is the family form of `Work.Drive.contMDiff_clampedSweep`. -/
theorem contMDiff_clampedSweep_family_gen {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : ℝ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ Ctop ψ)
    (Pp : P → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPp : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => Pp q.1 q.2)) :
    ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => clampedSweep c ψ (Pp q.1) q.2) := by
  intro q₀
  -- the plane slice `(q ↦ Pp q.1 (mk2 (q.2 0) (q.2 1)))` is smooth
  have hmk : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => (q.1, Work.Drive.mk2 (q.2 0) (q.2 1))) := by
    rw [contMDiff_iff_contDiff]
    exact (by fun_prop : ContDiff ℝ Ctop (fun q : P × EuclideanSpace ℝ (Fin 3) => q.1)).prodMk
      (contDiff_mk2_proj.comp (f := fun q : P × EuclideanSpace ℝ (Fin 3) => q.2) (by fun_prop))
  have hPaf : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => Pp q.1 (Work.Drive.mk2 (q.2 0) (q.2 1))) q₀ :=
    hPp.contMDiffAt.comp q₀ hmk.contMDiffAt
  have hlog : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) 𝓘(ℝ, ℝ) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) =>
        Real.log (levelOf (Pp q.1 (Work.Drive.mk2 (q.2 0) (q.2 1))))) q₀ :=
    contMDiffAt_log_levelOf_gen _ q₀ hPaf
  have h2 : ContDiffAt ℝ Ctop (fun q : P × EuclideanSpace ℝ (Fin 3) => ψ (q.2 2)) q₀ :=
    hψ.contDiffAt.comp q₀ (by fun_prop)
  have hscale : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) 𝓘(ℝ, ℝ) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => clampScale c ψ (Pp q.1) q.2) q₀ := by
    rw [show (fun q : P × EuclideanSpace ℝ (Fin 3) => clampScale c ψ (Pp q.1) q.2)
        = fun q => Real.exp (ψ (q.2 2) * (Real.log c - Real.log
            (levelOf (Pp q.1 (Work.Drive.mk2 (q.2 0) (q.2 1)))))) from rfl]
    rw [contMDiffAt_iff_contDiffAt]
    exact (Real.contDiff_exp.contDiffAt).comp q₀
      (h2.mul (contDiffAt_const.sub (contMDiffAt_iff_contDiffAt.mp hlog)))
  have hmain := contMDiffAt_scaleCapping_gen
    (fun q : P × EuclideanSpace ℝ (Fin 3) => clampScale c ψ (Pp q.1) q.2)
    (fun q => clampScale_pos c ψ (Pp q.1) q.2)
    (fun q : P × EuclideanSpace ℝ (Fin 3) => Pp q.1 (Work.Drive.mk2 (q.2 0) (q.2 1)))
    q₀ hscale hPaf
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with q
  rfl

end

end Work.Drive
