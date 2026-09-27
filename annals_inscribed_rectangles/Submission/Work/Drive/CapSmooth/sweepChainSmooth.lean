import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.scaleSweep
import Submission.Work.Drive.CapSmooth.capValueOfProj
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece

namespace Work.Drive.CapSmooth

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-!
# The smoothness of the sweep

`Work.Drive.sweepChain a ha P` is the map `x ↦ s(x) • P (x 0, x 1)`, where `s(x)` is a smooth
positive scalar and `•` is the radial dilation `Work.Drive.scaleCapping` of the capping space.  This
file proves that the sweep is smooth: the smooth structure `Work.Drive.cappingCharted` of the
capping space is transported along `Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³`,
and along that homeomorphism the dilation becomes the multiplication of the first coordinate by the
scalar (`cappingSpaceHomeoProj_scaleCapping`), which is smooth because `x ↦ log s(x)` is.
-/

/-- The linear left inverse of `Work.Drive.logEucl`: the projection onto the single coordinate of
`ℝ¹ = EuclideanSpace ℝ (Fin 1)`. -/
def euclLog : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toContinuousLinearMap.comp
    (EuclideanSpace.equiv (Fin 1) ℝ).toContinuousLinearMap

lemma euclLog_logEucl (z : ℝ) : euclLog (Work.Drive.logEucl z) = z := by
  simp [euclLog, Work.Drive.logEucl, ContinuousLinearEquiv.coe_coe]

/-- **The value of `cappingSpaceHomeoProj` on a radially dilated point.**  The dilation acts on the
radial coordinate only, so it becomes the multiplication of the first coordinate by `A`. -/
theorem cappingSpaceHomeoProj_scaleCapping (A : Work.Drive.Pos) (p : Work.Drive.CappingSpace) :
    Work.Drive.cappingSpaceHomeoProj (Work.Drive.scaleCapping A p)
      = (⟨(A : ℝ) * ((Work.Drive.cappingSpaceHomeoProj p).1 : ℝ),
          Set.mem_Ioi.mpr (mul_pos A.2 (Work.Drive.cappingSpaceHomeoProj p).1.2)⟩,
          (Work.Drive.cappingSpaceHomeoProj p).2) := by
  refine Prod.ext ?_ ?_
  · show (Work.Drive.Φ (Work.Drive.scaleCapping A p)).1 = _
    rw [Work.Drive.Φ_scaleCapping]
    rfl
  · show Work.Drive.lensSpaceHomeoProj ((Work.Drive.Φ (Work.Drive.scaleCapping A p)).2) = _
    rw [Work.Drive.Φ_scaleCapping]
    rfl

section

set_option linter.style.haveILetI false

/-- **Smoothness of the radial dilation, jointly in the parameter and the point.** -/
theorem contMDiffAt_scaleCapping {k : ℕ}
    (A : EuclideanSpace ℝ (Fin k) → ℝ) (hA : ∀ w, 0 < A w)
    (P : EuclideanSpace ℝ (Fin k) → Work.Drive.CappingSpace)
    (x₀ : EuclideanSpace ℝ (Fin k))
    (hAs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) A x₀)
    (hPs : letI := Work.Drive.cappingCharted
      ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P x₀) :
    letI := Work.Drive.cappingCharted
    ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => Work.Drive.scaleCapping ⟨A w, Set.mem_Ioi.mpr (hA w)⟩ (P w)) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := Work.Drive.projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace Work.Drive.expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace :=
    Work.Drive.cappingCharted
  let g : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => Work.Drive.cappingSpaceHomeoProj (P w)
  -- Step 1: transport the smoothness of `P` along `cappingSpaceHomeoProj`
  have hg : ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) g x₀ := by
    have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k)) (𝓡 k)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := Work.Drive.CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      Work.Drive.cappingSpaceHomeoProj.symm P Set.univ x₀
    exact hiff.mp hPs
  -- Step 2: read off the two components of `g`
  obtain ⟨hρ, hq⟩ := (Work.Drive.contMDiffAt_halfLineProjective_iff g x₀).mp hg
  -- Step 3: the radial coordinate of the dilated point, as a smooth function of `w`
  have hlogg : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => Real.log ((g w).1 : ℝ)) x₀ := by
    have key : (fun w => Real.log ((g w).1 : ℝ))
        = fun w => euclLog (Work.Drive.expHomeo.symm (g w).1) := by
      funext w
      rw [Work.Drive.expHomeo_symm_apply, euclLog_logEucl]
    rw [key, contMDiffAt_iff_contDiffAt]
    exact (euclLog.contDiff.contDiffAt).comp x₀ (contMDiffAt_iff_contDiffAt.mp hρ)
  have hlogA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Real.log (A w)) x₀ :=
    (Real.contDiffAt_log.mpr (ne_of_gt (hA x₀))).comp x₀ (contMDiffAt_iff_contDiffAt.mp hAs)
  -- Step 4: the composite with `cappingSpaceHomeoProj`, smooth in the structure of `(0,∞) × ℝP³`
  let G : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => (⟨A w * ((g w).1 : ℝ), Set.mem_Ioi.mpr (mul_pos (hA w) (g w).1.2)⟩, (g w).2)
  have hG1 : ContMDiffAt (𝓡 k) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => Work.Drive.expHomeo.symm (G w).1) x₀ := by
    have key : (fun w => Work.Drive.expHomeo.symm (G w).1)
        = fun w => Work.Drive.logEucl (Real.log (A w) + Real.log ((g w).1 : ℝ)) := by
      funext w
      have hG1w : (G w).1 = (⟨A w * ((g w).1 : ℝ),
          Set.mem_Ioi.mpr (mul_pos (hA w) (g w).1.2)⟩ : Set.Ioi (0:ℝ)) := rfl
      rw [hG1w, Work.Drive.expHomeo_symm_apply,
        Real.log_mul (ne_of_gt (hA w)) (ne_of_gt (g w).1.2)]
    rw [key, contMDiffAt_iff_contDiffAt]
    exact (Work.Drive.logEucl.contDiff.contDiffAt).comp x₀
      (hlogA.add (contMDiffAt_iff_contDiffAt.mp hlogg))
  have hG2 : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (G w).2) x₀ := by
    have key : (fun w => (G w).2) = fun w => (g w).2 := by
      funext w
      rfl
    rw [key]
    exact hq
  have hG : ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) G x₀ :=
    (Work.Drive.contMDiffAt_halfLineProjective_iff G x₀).mpr ⟨hG1, hG2⟩
  -- Step 5: transport back to the capping space
  have hiffF := Work.Drive.chartedStructure_contMDiffWithinAt
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k)) (𝓡 k)
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := Work.Drive.CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    Work.Drive.cappingSpaceHomeoProj.symm
    (fun w => Work.Drive.scaleCapping ⟨A w, Set.mem_Ioi.mpr (hA w)⟩ (P w)) Set.univ x₀
  refine hiffF.mpr ?_
  have key : (fun y => (Work.Drive.cappingSpaceHomeoProj.symm).symm
        (Work.Drive.scaleCapping ⟨A y, Set.mem_Ioi.mpr (hA y)⟩ (P y))) = G := by
    funext w
    rw [Homeomorph.symm_symm, cappingSpaceHomeoProj_scaleCapping]
  rw [key]
  exact hG

theorem sweepChainSmooth (a : ℝ) (ha : 0 < a)
    (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hP : letI := Work.Drive.cappingCharted
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) P) :
    letI := Work.Drive.cappingCharted
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.sweepChain a ha P) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace :=
    Work.Drive.cappingCharted
  intro x
  have hP' : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P := hP
  have hA : ∀ w : EuclideanSpace ℝ (Fin 3), 0 < Real.exp ((1 - w 2) * Real.log a) :=
    fun w => Real.exp_pos _
  have hAs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 3) => Real.exp ((1 - w 2) * Real.log a)) x := by
    rw [contMDiffAt_iff_contDiffAt]
    refine (Real.contDiff_exp.contDiffAt).comp x ?_
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin 3) => w 2) x :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).contDiff.contDiffAt
    exact (contDiffAt_const.sub h2).mul contDiffAt_const
  have hmk : ContMDiffAt (𝓡 3) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 3) => Work.Drive.mk2 (w 0) (w 1)) x := by
    rw [contMDiffAt_iff_contDiffAt]
    have hf : (fun w : EuclideanSpace ℝ (Fin 3) => Work.Drive.mk2 (w 0) (w 1))
        = fun w => WithLp.toLp 2 (![w 0, w 1] : Fin 2 → ℝ) := rfl
    rw [hf, contDiffAt_piLp (p := 2) (E := fun _ : Fin 2 => ℝ)]
    intro i
    fin_cases i
    · simpa using (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0)).contDiff.contDiffAt :
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : EuclideanSpace ℝ (Fin 3) => w 0) x)
    · simpa using (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 1)).contDiff.contDiffAt :
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : EuclideanSpace ℝ (Fin 3) => w 1) x)
  have hPs : ContMDiffAt (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 3) => P (Work.Drive.mk2 (w 0) (w 1))) x :=
    (hP'.contMDiffAt (x := Work.Drive.mk2 (x 0) (x 1))).comp x hmk
  have hmain := contMDiffAt_scaleCapping
    (A := fun w : EuclideanSpace ℝ (Fin 3) => Real.exp ((1 - w 2) * Real.log a))
    hA (fun w : EuclideanSpace ℝ (Fin 3) => P (Work.Drive.mk2 (w 0) (w 1))) x hAs hPs
  exact hmain

end

end

end Work.Drive.CapSmooth
