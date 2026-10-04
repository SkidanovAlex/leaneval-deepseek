import Submission.Work.Diff.C.LDG.Defs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `(n+1)`-tuple normalization map: smoothness and differential, first pieces
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology EuclideanSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.LDG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `U F` is smooth when all components are. -/
theorem contMDiff_U {F : Idx E → M → ℝ} (hFsm : ∀ i, CMDiff ∞ (F i)) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) ∞ (U F) := by
  have hP : ContMDiff I 𝓘(ℝ, Idx E → ℝ) ∞ (fun x : M => fun i => F i x) :=
    contMDiff_pi_space.mpr hFsm
  have hT : ContMDiff 𝓘(ℝ, Idx E → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) ∞
      (fun g : Idx E → ℝ => WithLp.toLp 2 g) := by
    have h := (PiLp.contDiff_toLp (𝕜 := ℝ) (n := ∞) (p := 2)
      (E := fun _ : Idx E => ℝ)).contMDiff
    simpa using h
  exact hT.comp hP

/-- The components of `mfderiv (U F) x` are the derivatives of the components. -/
theorem ofLp_mfderiv_U {F : Idx E → M → ℝ}
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) ∞ (U F))
    (x : M) (v : TangentSpace I x) (i : Idx E) :
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x v).ofLp i
      = mfderiv I 𝓘(ℝ,ℝ) (F i) x v := by
  set L : EuclideanSpace ℝ (Idx E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Idx E => ℝ) i).comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Idx E => ℝ)) :
        EuclideanSpace ℝ (Idx E) →L[ℝ] (Idx E → ℝ)) with hL
  have hLi : ∀ y, L (U F y) = F i y := fun y => rfl
  have hU' : HasMFDerivAt I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x) :=
    ((hU x).mdifferentiableAt (by simp)).hasMFDerivAt
  have hLI : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) 𝓘(ℝ,ℝ) (fun z => L z) (U F x) L :=
    ContinuousLinearMap.hasMFDerivAt L
  have hcomp : HasMFDerivAt I 𝓘(ℝ,ℝ) (fun y => L (U F y)) x
      (L.comp (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x)) :=
    HasMFDerivAt.comp x hLI hU'
  have hfun : (fun y => L (U F y)) = F i := funext fun y => hLi y
  have heq : mfderiv I 𝓘(ℝ,ℝ) (F i) x
      = L.comp (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x) := by
    rw [← hfun, hcomp.mfderiv]
  rw [heq]
  rfl

/-- The normalized map into the unit sphere is smooth. -/
theorem contMDiff_G {F : Idx E → M → ℝ} (hFsm : ∀ i, CMDiff ∞ (F i))
    (hpos : ∀ x, 0 < sq F x) :
    ContMDiff I (𝓡 (Module.finrank ℝ E)) ∞ (G F hpos) := by
  have hU := contMDiff_U (I := I) (M := M) hFsm
  have hne : ∀ y : M, U F y ≠ 0 := fun y h => by
    have h1 : 0 < rad F y := rad_pos F (hpos y)
    have h2 : ‖U F y‖ = 0 := by rw [h]; simp
    rw [norm_U F y] at h2
    exact absurd h2 (ne_of_gt h1)
  have hG₀ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) ∞ (G₀ F) := by
    have hΦ : ∀ y : EuclideanSpace ℝ (Idx E), y ≠ 0 →
        ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) ∞
          (fun z => ‖z‖⁻¹ • z) y := by
      intro y hy
      rw [contMDiffAt_iff_contDiffAt]
      have hnorm : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Idx E) => ‖z‖) y :=
        ContDiffAt.norm ℝ contDiffAt_id hy
      have hne' : (fun z : EuclideanSpace ℝ (Idx E) => ‖z‖) y ≠ 0 := by
        simpa using (norm_ne_zero_iff.mpr hy)
      exact ContDiffAt.smul (ContDiffAt.inv hnorm hne') contDiffAt_id
    have hfe : G₀ F = (fun z : EuclideanSpace ℝ (Idx E) => ‖z‖⁻¹ • z) ∘ (U F) := by
      funext y
      rw [Function.comp_apply, G₀_def, norm_U F y]
    rw [hfe]
    exact fun y => (hΦ (U F y) (hne y)).comp y (hU y)
  have hmem : ∀ x : M, G₀ F x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Idx E)) 1 := fun x => by
    rw [mem_sphere_zero_iff_norm]
    exact norm_G₀ F (hpos x)
  have hres := ContMDiff.codRestrict_sphere (n := Module.finrank ℝ E) hG₀ hmem
  have hfun : G F hpos = Set.codRestrict (G₀ F) (Metric.sphere 0 1) hmem := by
    funext x
    rfl
  rw [hfun]
  exact hres

end Work.Diff.C.LDG
