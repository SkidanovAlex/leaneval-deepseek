import Mathlib
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff_general

/-!
# Joint smoothness of a *family* of clamped radial sweeps

`Work.Drive.contMDiff_clampedSweep` (in `clampedSweep.lean`) proves the smoothness of a single
clamped sweep `clampedSweep c ψ P` in the **box** variable `x`, for a fixed plane presentation `P`.
What the chain construction of the surface count needs is the *joint* smoothness in the family
parameter and the box variable:

> `(q : P × 𝔼³) ↦ clampedSweep c ψ (Pp q.1) q.2` is `C^∞` whenever `(q : P × 𝔼²) ↦ Pp q.1 q.2` is,

for an arbitrary normed parameter space `P`.

This file proves it.  The two ingredients are the versions for a **general normed source space** of
the two smoothness lemmas of `clampedSweep.lean`:

* `Work.Drive.SweepFam.contMDiffAt_log_levelOf_self` — `x ↦ log (levelOf (f x))` is smooth whenever
  `f` is (the general-source form of `Work.Drive.contMDiffAt_log_levelOf`);
* `Work.Drive.SweepFam.contMDiffAt_scaleCapping_self` — `x ↦ scaleCapping ⟨A x, ·⟩ (F x)` is smooth
  (the general-source form of `Work.Drive.CapSmooth.contMDiffAt_scaleCapping`).

Both are proved by the *same* argument as their `𝓡 k` counterparts, with the component criterion
`Work.Drive.contMDiffAt_halfLineProjective_iff_general` (arbitrary charted source) replacing
`Work.Drive.contMDiffAt_halfLineProjective_iff`.

The top-level statement is the one requested by the chain construction
(`Work.Drive.contMDiff_clampedSweep_family`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

-- The transparent smooth structure of the capping space (and the two structures it is transported
-- from) is the one in which all the smoothness statements of this file are read.
attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.halfLineProjectiveCharted

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace SweepFam

/-- The coordinate projection `w ↦ mk2 (w 0) (w 1) : 𝔼³ → 𝔼²` is `C^∞`.  (This is
`Work.Drive.contMDiffAt_mk2_proj` without the pointwise packaging, so that it can be composed with
the first projection of a product.) -/
lemma contDiff_mk2_proj :
    ContDiff ℝ Ctop (fun w : EuclideanSpace ℝ (Fin 3) => mk2 (w 0) (w 1)) := by
  rw [show (fun w : EuclideanSpace ℝ (Fin 3) => mk2 (w 0) (w 1))
      = fun w => WithLp.toLp 2 (![w 0, w 1] : Fin 2 → ℝ) from rfl]
  rw [contDiff_piLp (p := 2) (E := fun _ : Fin 2 => ℝ)]
  intro i
  fin_cases i
  · simpa using ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).contDiff (n := Ctop))
  · simpa using ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 1).contDiff (n := Ctop))

/-- **The logarithm of the radial coordinate of a smooth map into the capping space is smooth**, for
an arbitrary normed source space `P`.  This is `Work.Drive.contMDiffAt_log_levelOf` with `𝓡 k`
replaced by `𝓘(ℝ, P)`, via the general component criterion
`Work.Drive.contMDiffAt_halfLineProjective_iff_general`. -/
theorem contMDiffAt_log_levelOf_self {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : P → CappingSpace) (x₀ : P)
    (hf : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop f x₀) :
    ContMDiffAt (𝓘(ℝ, P)) 𝓘(ℝ, ℝ) Ctop (fun w => Real.log (levelOf (f w))) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  have hg : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop (fun w => cappingSpaceHomeoProj (f w)) x₀ := by
    have hiff := chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := P) (H' := P) (𝓘(ℝ, P))
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := Ctop)
      cappingSpaceHomeoProj.symm f Set.univ x₀
    exact hiff.mp hf
  obtain ⟨hρ, -⟩ := (contMDiffAt_halfLineProjective_iff_general (𝓘(ℝ, P))
    (fun w => cappingSpaceHomeoProj (f w)) x₀).mp hg
  have key : (fun w => Real.log (levelOf (f w)))
      = fun w => CapSmooth.euclLog (expHomeo.symm
          ((fun w => cappingSpaceHomeoProj (f w)) w).1) := by
    funext w
    rw [levelOf, expHomeo_symm_apply, CapSmooth.euclLog_logEucl]
  rw [key, contMDiffAt_iff_contDiffAt]
  exact (CapSmooth.euclLog.contDiff.contDiffAt).comp x₀ (contMDiffAt_iff_contDiffAt.mp hρ)

/-- **Smoothness of the radial dilation**, for an arbitrary normed source space `P`.  This is
`Work.Drive.CapSmooth.contMDiffAt_scaleCapping` with `𝓡 k` replaced by `𝓘(ℝ, P)`. -/
theorem contMDiffAt_scaleCapping_self {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → ℝ) (hA : ∀ w, 0 < A w) (F : P → CappingSpace) (x₀ : P)
    (hAs : ContMDiffAt (𝓘(ℝ, P)) 𝓘(ℝ, ℝ) Ctop A x₀)
    (hFs : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop F x₀) :
    ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop
      (fun w => scaleCapping ⟨A w, Set.mem_Ioi.mpr (hA w)⟩ (F w)) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  let g : P → Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => cappingSpaceHomeoProj (F w)
  -- Step 1: transport the smoothness of `F` along `cappingSpaceHomeoProj`
  have hg : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop g x₀ := by
    have hiff := chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := P) (H' := P) (𝓘(ℝ, P))
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := Ctop)
      cappingSpaceHomeoProj.symm F Set.univ x₀
    exact hiff.mp hFs
  -- Step 2: read off the two components of `g`
  obtain ⟨hρ, hq⟩ := (contMDiffAt_halfLineProjective_iff_general (𝓘(ℝ, P)) g x₀).mp hg
  -- Step 3: the radial coordinate of the dilated point, as a smooth function of the parameter
  have hlogg : ContMDiffAt (𝓘(ℝ, P)) 𝓘(ℝ, ℝ) Ctop
      (fun w => Real.log ((g w).1 : ℝ)) x₀ := by
    have key : (fun w => Real.log ((g w).1 : ℝ))
        = fun w => CapSmooth.euclLog (expHomeo.symm (g w).1) := by
      funext w
      rw [expHomeo_symm_apply, CapSmooth.euclLog_logEucl]
    rw [key, contMDiffAt_iff_contDiffAt]
    exact (CapSmooth.euclLog.contDiff.contDiffAt).comp x₀
      (contMDiffAt_iff_contDiffAt.mp hρ)
  have hlogA : ContDiffAt ℝ Ctop (fun w => Real.log (A w)) x₀ :=
    (Real.contDiffAt_log.mpr (ne_of_gt (hA x₀))).comp x₀ (contMDiffAt_iff_contDiffAt.mp hAs)
  -- Step 4: the composite with `cappingSpaceHomeoProj`, smooth in `(0,∞) × ℝP³`
  let G : P → Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => (⟨A w * ((g w).1 : ℝ), Set.mem_Ioi.mpr (mul_pos (hA w) (g w).1.2)⟩, (g w).2)
  have hG1 : ContMDiffAt (𝓘(ℝ, P)) (𝓡 1) Ctop
      (fun w => expHomeo.symm (G w).1) x₀ := by
    have key : (fun w => expHomeo.symm (G w).1)
        = fun w => logEucl (Real.log (A w) + Real.log ((g w).1 : ℝ)) := by
      funext w
      have hG1w : (G w).1 = (⟨A w * ((g w).1 : ℝ),
          Set.mem_Ioi.mpr (mul_pos (hA w) (g w).1.2)⟩ : Set.Ioi (0:ℝ)) := rfl
      rw [hG1w, expHomeo_symm_apply,
        Real.log_mul (ne_of_gt (hA w)) (ne_of_gt (g w).1.2)]
    rw [key, contMDiffAt_iff_contDiffAt]
    exact (logEucl.contDiff.contDiffAt).comp x₀
      (hlogA.add (contMDiffAt_iff_contDiffAt.mp hlogg))
  have hG2 : ContMDiffAt (𝓘(ℝ, P)) (𝓡 3) Ctop (fun w => (G w).2) x₀ := by
    have key : (fun w => (G w).2) = fun w => (g w).2 := by funext w; rfl
    rw [key]
    exact hq
  have hG : ContMDiffAt (𝓘(ℝ, P)) (𝓡 4) Ctop G x₀ :=
    (contMDiffAt_halfLineProjective_iff_general (𝓘(ℝ, P)) G x₀).mpr ⟨hG1, hG2⟩
  -- Step 5: transport back to the capping space
  have hiffF := chartedStructure_contMDiffWithinAt
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (E' := P) (H' := P) (𝓘(ℝ, P))
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := CappingSpace) (n := Ctop)
    cappingSpaceHomeoProj.symm
    (fun w => scaleCapping ⟨A w, Set.mem_Ioi.mpr (hA w)⟩ (F w)) Set.univ x₀
  refine hiffF.mpr ?_
  have key : (fun y => (cappingSpaceHomeoProj.symm).symm
        (scaleCapping ⟨A y, Set.mem_Ioi.mpr (hA y)⟩ (F y))) = G := by
    funext w
    rw [Homeomorph.symm_symm, CapSmooth.cappingSpaceHomeoProj_scaleCapping]
  rw [key]
  exact hG

end SweepFam

/-- **Joint smoothness of the clamped radial sweep in a `C^∞` family of plane presentations.**  For a
family `Pp` of plane presentations which is `C^∞` jointly in the parameter `p : P` and the plane
coordinate `y : 𝔼²`, the map `(p, x) ↦ clampedSweep c ψ (Pp p) x` is `C^∞` on `P × 𝔼³`. -/
theorem contMDiff_clampedSweep_family {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : ℝ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (Pp : P → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hPp : letI := Work.Drive.cappingCharted
      ContMDiff (modelWithCornersSelf ℝ (P × EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : P × EuclideanSpace ℝ (Fin 2) => Pp q.1 q.2)) :
    letI := Work.Drive.cappingCharted
    ContMDiff (modelWithCornersSelf ℝ (P × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 3) => Work.Drive.clampedSweep c ψ (Pp q.1) q.2) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  intro q₀
  -- the plane map composed with the coordinate projection `ℝ³ → ℝ²` is smooth in the parameter
  have hmk : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => (q.1, mk2 (q.2 0) (q.2 1))) := by
    rw [contMDiff_iff_contDiff]
    exact (contDiff_fst (𝕜 := ℝ) (n := Ctop)).prodMk
      (SweepFam.contDiff_mk2_proj.comp (contDiff_snd (𝕜 := ℝ) (n := Ctop)))
  have hPaf : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => Pp q.1 (mk2 (q.2 0) (q.2 1))) q₀ :=
    hPp.contMDiffAt.comp q₀ hmk.contMDiffAt
  have hlog : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) 𝓘(ℝ, ℝ) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) =>
        Real.log (levelOf (Pp q.1 (mk2 (q.2 0) (q.2 1))))) q₀ :=
    SweepFam.contMDiffAt_log_levelOf_self _ q₀ hPaf
  have h2 : ContDiffAt ℝ Ctop (fun q : P × EuclideanSpace ℝ (Fin 3) => ψ (q.2 2)) q₀ :=
    hψ.contDiffAt.comp q₀
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).contDiff.contDiffAt.comp q₀
        (contDiffAt_snd (𝕜 := ℝ) (n := Ctop)))
  have hscale : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) 𝓘(ℝ, ℝ) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => clampScale c ψ (Pp q.1) q.2) q₀ := by
    rw [show (fun q : P × EuclideanSpace ℝ (Fin 3) => clampScale c ψ (Pp q.1) q.2)
        = fun q => Real.exp (ψ (q.2 2) * (Real.log c - Real.log
            (levelOf (Pp q.1 (mk2 (q.2 0) (q.2 1)))))) from rfl]
    rw [contMDiffAt_iff_contDiffAt]
    exact (Real.contDiff_exp.contDiffAt).comp q₀
      (h2.mul (contDiffAt_const.sub (contMDiffAt_iff_contDiffAt.mp hlog)))
  have hmain := SweepFam.contMDiffAt_scaleCapping_self
    (fun q : P × EuclideanSpace ℝ (Fin 3) => clampScale c ψ (Pp q.1) q.2)
    (fun q => clampScale_pos c ψ (Pp q.1) q.2)
    (fun q : P × EuclideanSpace ℝ (Fin 3) => Pp q.1 (mk2 (q.2 0) (q.2 1)))
    q₀ hscale hPaf
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with q
  rfl

end

end Work.Drive
