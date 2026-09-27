import Mathlib
import Submission.Work.Drive.sideGermSepDefs
import Submission.Work.Drive.parityChainSmooth
import Submission.Work.Drive.contMDiff_rotCapping_family

/-!
# The smoothness clause `Work.Drive.SepSmooth` of the separated germ family

The parity-locality engine of the separated germ route
(`Work.Drive.odd_coreSideCount_iff_of_famRegular_gen`, consumed in
`Submission/Work/Drive/sideGerm_parity_eq_of_close_of_separation.lean`) needs the two sides of the
five-box family to be `C^∞`: the loop side `chartLoopFam (sepQfam Ξ Q A B τ₁)` and the chain side
`sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)`.  This file proves exactly that, i.e. the
structure `Work.Drive.SepSmooth` (the smoothness half of `Work.Drive.SepRegular`).

The two sides are built from

* the joint smoothness of the chart perturbation, `ChartPert.2.1` (`(t, p) ↦ Ξ t p` is `C^∞`),
* the smoothness of the disk presentation `Q` (`IsSmoothChart`),
* the straight paths `sepPathL`, `sepPathR` (affine in the path parameter),
* the *varying* rotation `rotPresentation · (sepAngle tR t'R s)`, whose joint smoothness in the path
  parameter and the plane parameter is `Work.Drive.contMDiffAt_rotCapping_family` (the rotation of the
  capping space is smooth in both variables),
* the joint smoothness of a family of clamped sweeps, `contMDiff_clampedSweep_family_gen`.

The two small coordinate linear maps below are the bookkeeping that turns the "family parameter ×
plane point" and "family parameter × chain parameter" splittings into the flat Euclidean spaces on
which the two smoothness lemmas are stated.
-/

namespace Work.Drive

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

open Manifold Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Coordinate linear maps -/

/-- The linear map `(s, y) ↦ (s, y 0, y 1)` from `ℝ × ℝ²` to `ℝ³`. -/
def sepLambdaLin : (ℝ × EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun q := famT3 q.1 (q.2 0) (q.2 1)
  map_add' a b := by ext i; fin_cases i <;> simp [famT3]
  map_smul' a b := by ext i; fin_cases i <;> simp [famT3]

/-- The continuous linear map `(s, y) ↦ (s, y 0, y 1)`. -/
def sepLambdaCLM : (ℝ × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  sepLambdaLin.toContinuousLinearMap

@[simp] lemma sepLambdaCLM_apply (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sepLambdaCLM q = famT3 q.1 (q.2 0) (q.2 1) := rfl

/-- The coordinates of `sepLambdaCLM q` are `(q.1, mk2 (q.2 0) (q.2 1)) = q`. -/
lemma sepLambdaCLM_key (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    ((sepLambdaCLM q) 0, mk2 ((sepLambdaCLM q) 1) ((sepLambdaCLM q) 2)) = (q.1, q.2) := by
  simp [sepLambdaCLM_apply, mk2_eta]

/-- The linear map `u ↦ mk2 (u 1) (u 2)` from `ℝ³` to `ℝ²`. -/
def sepMk2TailLin : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun u := mk2 (u 1) (u 2)
  map_add' a b := by ext i; fin_cases i <;> simp [mk2]
  map_smul' a b := by ext i; fin_cases i <;> simp [mk2]

/-- The continuous linear map `u ↦ mk2 (u 1) (u 2)`. -/
def sepMk2TailCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  sepMk2TailLin.toContinuousLinearMap

@[simp] lemma sepMk2TailCLM_apply (u : EuclideanSpace ℝ (Fin 3)) :
    sepMk2TailCLM u = mk2 (u 1) (u 2) := rfl

/-- The linear map `q ↦ (q 1, q 2, q 3)` from `ℝ⁴` to `ℝ³`. -/
def sepFamT3Lin : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun q := famT3 (q 1) (q 2) (q 3)
  map_add' a b := by ext i; fin_cases i <;> simp [famT3]
  map_smul' a b := by ext i; fin_cases i <;> simp [famT3]

/-- The continuous linear map `q ↦ (q 1, q 2, q 3)`. -/
def sepFamT3CLM : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  sepFamT3Lin.toContinuousLinearMap

@[simp] lemma sepFamT3CLM_apply (q : EuclideanSpace ℝ (Fin 4)) :
    sepFamT3CLM q = famT3 (q 1) (q 2) (q 3) := rfl

/-- The continuous linear map `q ↦ (q 0, q 1, q 2, q 3)`, split as a family parameter and a chain
parameter. -/
def sepSplitCLM : EuclideanSpace ℝ (Fin 4) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  ContinuousLinearMap.prod (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 0) sepFamT3CLM

@[simp] lemma sepSplitCLM_apply (q : EuclideanSpace ℝ (Fin 4)) :
    sepSplitCLM q = (q 0, famT3 (q 1) (q 2) (q 3)) := by
  rw [sepSplitCLM, ContinuousLinearMap.prod_apply, sepFamT3CLM_apply]
  rfl

/-! ## The loop side -/

/-- **The loop side of the separated family is `C^∞`.** -/
theorem sep_contMDiff_chartLoopFam {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 2) (𝓡 4) Ctop (chartLoopFam (sepQfam Ξ Q A B τ₁)) := by
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ
  have hsepPathL : ContDiff ℝ Ctop (fun s : ℝ => sepPathL A B s) := by
    unfold sepPathL
    fun_prop
  have hpath : ContMDiff (𝓡 2) (𝓡 m) Ctop
      (fun p : EuclideanSpace ℝ (Fin 2) => sepPathL A B (p 0) + τ₁) :=
    ((hsepPathL.contMDiff (n := Ctop)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contMDiff).add contMDiff_const
  have hexp : ContMDiff (𝓡 2) (𝓘(ℝ, ℂ)) Ctop
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        Complex.exp (Real.pi * ((p 1 : ℝ) : ℂ) * Complex.I)) := by
    have hlin : ContDiff ℝ Ctop
        (fun p : EuclideanSpace ℝ (Fin 2) => Real.pi * ((p 1 : ℝ) : ℂ) * Complex.I) := by
      have h1 : ContDiff ℝ Ctop
          (fun p : EuclideanSpace ℝ (Fin 2) => ((p 1 : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff
      exact (contDiff_const.mul h1).mul contDiff_const
    exact Complex.contDiff_exp.contMDiff.comp (contMDiff_iff_contDiff.mpr hlin)
  have hmain := hΞ.2.1.comp (hpath.prodMk (hQsm.comp hexp))
  refine hmain.congr fun p => ?_
  simp only [Function.comp_def, chartLoopFam, sepQfam, coreLoop]

/-! ## The chain side -/

/-- **The chain side of the separated family is `C^∞`.** -/
theorem sep_contMDiff_sweepFam {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    (τ₂ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 4) (𝓡 4) Ctop
      (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)) := by
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ
  -- the angle path
  have hθ : ContDiff ℝ Ctop (fun s : ℝ => (1 - s) * tR + s * t'R) := by fun_prop
  have ht : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) Ctop
      (fun u : EuclideanSpace ℝ (Fin 3) => (1 - u 0) * tR + u 0 * t'R) :=
    hθ.contMDiff.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).contMDiff
  -- the perturbed plane presentation family
  have hP : ContMDiff (𝓡 3) (𝓡 4) Ctop
      (fun u : EuclideanSpace ℝ (Fin 3) =>
        Ξ (sepPathR A B (u 0) + τ₂) (diskPlane Q (mk2 (u 1) (u 2)))) := by
    have hsepPathR : ContDiff ℝ Ctop (fun s : ℝ => sepPathR A B s) := by
      unfold sepPathR
      fun_prop
    have hp : ContMDiff (𝓡 3) (𝓡 m) Ctop
        (fun u : EuclideanSpace ℝ (Fin 3) => sepPathR A B (u 0) + τ₂) :=
      ((hsepPathR.contMDiff (n := Ctop)).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).contMDiff).add contMDiff_const
    have hd : ContMDiff (𝓡 3) (𝓡 4) Ctop
        (fun u : EuclideanSpace ℝ (Fin 3) => diskPlane Q (mk2 (u 1) (u 2))) :=
      (contMDiff_diskPlane hQsm).comp sepMk2TailCLM.contMDiff
    exact hΞ.2.1.comp (hp.prodMk hd)
  -- the rotated presentation, jointly smooth in the path parameter and the plane parameter
  have hrot : ContMDiff (𝓡 3) (𝓡 4) Ctop
      (fun u : EuclideanSpace ℝ (Fin 3) =>
        rotCapping ((((1 - u 0) * tR + u 0 * t'R : ℝ)) : UnitAddCircle)
          (Ξ (sepPathR A B (u 0) + τ₂) (diskPlane Q (mk2 (u 1) (u 2))))) := by
    intro u
    exact contMDiffAt_rotCapping_family
      (t := fun u : EuclideanSpace ℝ (Fin 3) => (1 - u 0) * tR + u 0 * t'R)
      (P := fun u : EuclideanSpace ℝ (Fin 3) =>
        Ξ (sepPathR A B (u 0) + τ₂) (diskPlane Q (mk2 (u 1) (u 2)))) ht hP u
  -- the plane-presentation family of the sweep on the flat parameter `ℝ³`
  have hP3 : ContMDiff (𝓡 3) (𝓡 4) Ctop
      (fun u : EuclideanSpace ℝ (Fin 3) =>
        sepPfam Ξ Q tR t'R A B τ₂ (u 0) (mk2 (u 1) (u 2))) := by
    refine hrot.congr fun u => ?_
    simp only [sepPfam, rotPresentation, diskPlane, sepAngle]
  -- regroup as `ℝ × ℝ²`
  have hPp : ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => sepPfam Ξ Q tR t'R A B τ₂ q.1 q.2) := by
    refine (hP3.comp sepLambdaCLM.contMDiff).congr fun q => ?_
    exact (congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
      sepPfam Ξ Q tR t'R A B τ₂ z.1 z.2) (sepLambdaCLM_key q)).symm
  -- the family form of the clamped sweep
  have hgen := contMDiff_clampedSweep_family_gen (P := ℝ) c (fun u : ℝ => 1 - u) (by fun_prop)
    (fun s y => sepPfam Ξ Q tR t'R A B τ₂ s y) hPp
  refine (hgen.comp sepSplitCLM.contMDiff).congr fun q => ?_
  simp only [Function.comp_def, sepSplitCLM_apply, sweepFam]

end

theorem sep_fam_smooth {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsSmoothChart Q) (hc : 0 < c)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) :
    Work.Drive.SepSmooth Ξ Q c tR t'R A B τ₁ τ₂ :=
  ⟨sep_contMDiff_chartLoopFam Ξ Q hΞ hQ A B τ₁,
    sep_contMDiff_sweepFam Ξ Q c hΞ hQ A B tR t'R τ₂⟩

end Work.Drive
