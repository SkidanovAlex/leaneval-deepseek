import Mathlib
import Submission.Work.Drive.sepFamDefs
import Submission.Work.Drive.sep_fam_smooth

/-!
# The `C^∞` clauses of the separated germ family

`Work.Drive.sepContMDiffFams` collects the three smoothness facts that the parity engine of the
separated germ route needs about the two sides of the five-box family of
`Work.Drive.sep_fam_regular` (see `Submission/Work/Drive/sepFamDefs.lean`):

* `Work.Drive.SepLoopSmooth` — the loop family `chartLoopFam (sepQfam Ξ Q A B τ₁)` is `C^∞` in the
  loop parameter;
* `Work.Drive.SepChainSmooth` — the chain family `sweepFam c (1 - ·) (sepPfam Ξ Q tR t'R A B τ₂)` is
  `C^∞` in the chain parameter, at a fixed shift;
* `Work.Drive.SepChainSmoothJoint` — the chain family is `C^∞` *jointly* in the shift `τ₂` and the
  chain parameter.

The first two are `Work.Drive.sep_contMDiff_chartLoopFam` and `Work.Drive.sep_contMDiff_sweepFam`
(`Submission/Work/Drive/sep_fam_smooth.lean`), proved there by rewriting the two sides as composites
of the jointly smooth chart perturbation `ChartPert.2.1`, the smooth disk presentation `Q`, the
smooth rotation action `rotCapping`, and the jointly smooth clamped sweep.

The third is the content of this file.  Its two ingredients are

* `sepJointPfamSmooth` — the plane-presentation family
  `(τ, s, y) ↦ sepPfam Ξ Q tR t'R A B τ s y` is jointly `C^∞` in the shift `τ`, the path parameter
  `s` and the plane point `y`: the perturbed chart `(τ, s, y) ↦ Ξ (sepPathR A B s + τ) (diskPlane Q y)`
  is smooth by `ChartPert.2.1`, and the rotation by the angle `(1 - s) tR + s t'R` is applied to it by
  `Work.Drive.contMDiffAt_rotCapping_comp` (the rotation action is smooth in a `C^∞` angle and a
  `C^∞` family of points);
* `contMDiff_clampedSweep_family_gen` — the clamped sweep is jointly `C^∞` in a `C^∞` family of plane
  presentations and the box parameter.

The shift and the path parameter are `(τ, s) = q.1` of the family parameter of the clamp, so the four
chain coordinates are regrouped by the linear map `sepJointRegroupCLM`.  The two model shapes
(`𝓘(ℝ, E × F)` for the flattened parameter space and `(𝓡 m).prod (𝓡 4)` for the product manifold)
are exchanged by `modelWithCornersSelf_prod` and `chartedSpaceSelf_prod`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000

variable {m : ℕ}

/-! ## The regrouping of the joint parameters -/

/-- **The regrouping of the chain coordinates.**  The joint parameter space of
`Work.Drive.SepChainSmoothJoint` is `ℝᵐ × ℝ⁴`: the first factor is the shift `τ₂` and the second the
chain parameter `q`.  In the chain family `sepChainFam`, the shift and the *path* parameter `q 0`
together form the family parameter of the clamped sweep, whose box parameter is `famT3 (q 1) (q 2)
(q 3)`; this continuous linear map is that regrouping. -/
def sepJointRegroupCLM (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) →L[ℝ]
      ((EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.prod
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 4)))
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 0).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 4)))))
    (sepFamT3CLM.comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 4))))

@[simp] lemma sepJointRegroupCLM_apply (m : ℕ)
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) :
    sepJointRegroupCLM m q = ((q.1, q.2 0), famT3 (q.2 1) (q.2 2) (q.2 3)) := rfl

/-! ## The joint smoothness of the two intermediate families -/

/-- **The plane-presentation family is jointly `C^∞`** in the shift `τ`, the path parameter `s` and
the plane point `y`. -/
theorem sepJointPfamSmooth
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (tR t'R : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun r : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        sepPfam Ξ Q tR t'R A B r.1.1 r.1.2 r.2) := by
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ
  -- the perturbed plane presentation `(τ, s, y) ↦ Ξ (sepPathR A B s + τ) (diskPlane Q y)`
  have hP : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun r : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        Ξ (sepPathR A B r.1.2 + r.1.1) (diskPlane Q r.2)) := by
    have hpath : ContDiff ℝ Ctop
        (fun r : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
          sepPathR A B r.1.2 + r.1.1) := by
      have h0 : ContDiff ℝ Ctop (fun s : ℝ => sepPathR A B s) := by unfold sepPathR; fun_prop
      fun_prop
    have h1 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 m) Ctop
        (fun r : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
          sepPathR A B r.1.2 + r.1.1) :=
      contMDiff_iff_contDiff.mpr hpath
    have h2 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop
        (fun r : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) => diskPlane Q r.2) :=
      (contMDiff_diskPlane hQsm).comp
        (contMDiff_iff_contDiff.mpr (by fun_prop))
    exact hΞ.2.1.comp (h1.prodMk h2)
  -- the rotated plane presentation
  have hrot : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun r : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        rotCapping ((((1 - r.1.2) * tR + r.1.2 * t'R : ℝ)) : UnitAddCircle)
          (Ξ (sepPathR A B r.1.2 + r.1.1) (diskPlane Q r.2))) := by
    intro r
    exact contMDiffAt_rotCapping_comp
      (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2)))
      (P := fun r : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        Ξ (sepPathR A B r.1.2 + r.1.1) (diskPlane Q r.2))
      (τ := fun r : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        (1 - r.1.2) * tR + r.1.2 * t'R) r hP.contMDiffAt
      ((contMDiff_iff_contDiff.mpr (by fun_prop)).contMDiffAt)
  refine hrot.congr fun r => ?_
  simp only [sepPfam, rotPresentation, diskPlane, sepAngle]

/-- **The chain family is jointly `C^∞`**, in the flattened form of the parameter space
`ℝᵐ × ℝ⁴ = 𝓘(ℝ, ℝᵐ × ℝ⁴)`. -/
theorem sepJointChainSmoothFlat
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) =>
        sepChainFam Ξ Q c tR t'R A B q.1 q.2) := by
  have hPp := sepJointPfamSmooth Ξ Q tR t'R hΞ hQ A B
  -- the clamped sweep, jointly in the family of plane presentations and the box parameter
  have hJ := contMDiff_clampedSweep_family_gen (P := EuclideanSpace ℝ (Fin m) × ℝ) c
      (fun u : ℝ => 1 - u) (by fun_prop)
      (fun p : EuclideanSpace ℝ (Fin m) × ℝ => fun y => sepPfam Ξ Q tR t'R A B p.1 p.2 y) hPp
  have hCLM : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)))
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 3))) Ctop
      (sepJointRegroupCLM m) := (sepJointRegroupCLM m).contMDiff
  refine (hJ.comp hCLM).congr fun q => ?_
  simp only [Function.comp_def, sepJointRegroupCLM_apply, sepChainFam, sweepFam]

/-- **The chain family is jointly `C^∞` in the shift and the chain parameter.**  The statement is the
definition `Work.Drive.SepChainSmoothJoint` (whose product model `(𝓡 m).prod (𝓡 4)` is exchanged
with the flattened one by `modelWithCornersSelf_prod`). -/
theorem sepJointChainSmooth
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    SepChainSmoothJoint Ξ Q c tR t'R A B := by
  rw [SepChainSmoothJoint]
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact sepJointChainSmoothFlat Ξ Q c tR t'R hΞ hQ A B

/-! ## The three clauses -/

theorem sepContMDiffFams {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (hΞ : Work.Drive.ChartPert Q m Ξ)
    (hQ : Work.Drive.IsSmoothChart Q) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) :
    Work.Drive.SepLoopSmooth Ξ Q A B τ₁ ∧
      Work.Drive.SepChainSmooth Ξ Q c tR t'R A B τ₂ ∧
      Work.Drive.SepChainSmoothJoint Ξ Q c tR t'R A B := by
  refine ⟨?_, ?_, ?_⟩
  · exact sep_contMDiff_chartLoopFam Ξ Q hΞ hQ A B τ₁
  · exact sep_contMDiff_sweepFam Ξ Q c hΞ hQ A B tR t'R τ₂
  · exact sepJointChainSmooth Ξ Q c tR t'R hΞ hQ A B

end

end Work.Drive
