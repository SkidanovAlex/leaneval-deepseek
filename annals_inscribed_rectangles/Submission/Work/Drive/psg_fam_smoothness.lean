import Mathlib
import Submission.Work.Drive.psgFamilyDefs
import Submission.Work.Drive.contMDiff_rotPresentation
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.parityChainSmooth

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-! ## The linear bookkeeping map of the chain side

The joint smoothness of a family of clamped sweeps (`Work.Drive.contMDiff_clampedSweep_family_gen`)
is stated for a family indexed by a normed space `P` and the box `𝔼³`, on the product `P × 𝔼³`.  The
chain parameters of the `psg` family here are `q : 𝔼^m × 𝔼⁴`, with `q.1` the chart perturbation and
`(q.2 0, q.2 1, q.2 2, q.2 3)` the family parameter and the three box coordinates; the linear map
below is the reindexing that the family form consumes. -/

/-- `q ↦ ((q.1, q.2 0), (q.2 1, q.2 2, q.2 3))`. -/
def psgSplitLin (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) →ₗ[ℝ]
      ((EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 3)) where
  toFun q := ((q.1, q.2 0), famT3 (q.2 1) (q.2 2) (q.2 3))
  map_add' a b := by
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_ <;> simp
    · ext i; fin_cases i <;> simp [famT3]
  map_smul' a b := by
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_ <;> simp
    · ext i; fin_cases i <;> simp [famT3]

/-- The continuous form of `psgSplitLin`. -/
def psgSplitCLM (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) →L[ℝ]
      ((EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  (psgSplitLin m).toContinuousLinearMap

@[simp] lemma psgSplitCLM_apply (m : ℕ)
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) :
    psgSplitCLM m q = ((q.1, q.2 0), famT3 (q.2 1) (q.2 2) (q.2 3)) := rfl

/-! ## The smoothness of the two sides of the family

The statements are proved first in the *joint* form, on the product of the perturbation space and the
box, and the fixed-perturbation forms are the immediate consequences. -/

/-- **The loop side is `C^∞` jointly in the chart perturbation and the two-box parameter.** -/
theorem psg_contMDiff_loop_joint {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff ((𝓡 m).prod (𝓡 2)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        psgLoopFam Ξ Q A B q.1 q.2) := by
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ.1
  have hexp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, ℂ)) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        Complex.exp (Real.pi * ((q.2 1 : ℝ) : ℂ) * Complex.I)) := by
    have hlin : ContDiff ℝ Ctop
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
          Real.pi * ((q.2 1 : ℝ) : ℂ) * Complex.I) := by
      have h1 : ContDiff ℝ Ctop
          (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
            ((q.2 1 : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff.comp
            (contDiff_snd (𝕜 := ℝ) (n := Ctop)))
      exact (contDiff_const.mul h1).mul contDiff_const
    exact Complex.contDiff_exp.contMDiff.comp (contMDiff_iff_contDiff.mpr hlin)
  have hpath : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 m) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        psgPathL A B (q.2 0) + q.1) := by
    rw [contMDiff_iff_contDiff]
    exact ((contDiff_psgPathL A B).comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff.comp
          (contDiff_snd (𝕜 := ℝ) (n := Ctop)))).add
      (contDiff_fst (𝕜 := ℝ) (n := Ctop))
  have hmain := hΞ.2.1.comp (hpath.prodMk (hQsm.comp hexp))
  rw [← modelWithCornersSelf_prod]
  rw [chartedSpaceSelf_prod]
  refine hmain.congr fun q => ?_
  simp only [Function.comp_def, psgLoopFam, chartLoopFam, psgQFam, coreLoop]

/-- **The loop side is `C^∞` on the two-box, for a fixed chart perturbation.** -/
theorem psg_contMDiff_loop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 2) (𝓡 4) Ctop (psgLoopFam Ξ Q A B τ₁) := by
  have hp : ContMDiff (𝓡 2) ((𝓡 m).prod (𝓡 2)) Ctop
      (fun p : EuclideanSpace ℝ (Fin 2) => (τ₁, p)) :=
    contMDiff_const.prodMk contMDiff_id
  exact ((psg_contMDiff_loop_joint Ξ Q hΞ hQ A B).comp hp).congr fun p => rfl

/-- **The chain side is `C^∞` jointly in the chart perturbation and the four-box parameter.** -/
theorem psg_contMDiff_chain_joint {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tA tB : ℝ) :
    ContMDiff ((𝓡 m).prod (𝓡 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) =>
        psgChainFam Ξ Q c A B tA tB q.1 q.2) := by
  have hψ : ContDiff ℝ Ctop (fun u : ℝ => 1 - u) := by fun_prop
  -- the plane-presentation family: jointly smooth in the perturbation, the path parameter and the
  -- plane parameter
  have hPp : ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        psgPFam Ξ Q A B tA tB q.1.1 q.1.2 q.2) := by
    -- the angle path
    have hθ : ContMDiff
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2))) 𝓘(ℝ, ℝ) Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
          psgAngle tA tB q.1.2) := by
      rw [contMDiff_iff_contDiff]
      unfold psgAngle
      fun_prop
    -- the perturbed plane presentation
    have hPbase : ContMDiff
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
          Ξ (psgPathR A B q.1.2 + q.1.1) (diskPlane Q q.2)) := by
      refine hΞ.2.1.comp (ContMDiff.prodMk ?_ ?_)
      · rw [contMDiff_iff_contDiff]
        exact ((contDiff_psgPathR A B).comp (by fun_prop)).add (by fun_prop)
      · exact (contMDiff_diskPlane hQ.1).comp (contMDiff_iff_contDiff.mpr (by fun_prop))
    have hrot := contMDiff_rotCapping.comp (hθ.prodMk hPbase)
    refine hrot.congr fun q => ?_
    simp only [Function.comp_def, psgPFam, rotPresentation, diskPlane, psgAngleClass]
  have hgen := contMDiff_clampedSweep_family_gen
    (P := EuclideanSpace ℝ (Fin m) × ℝ) c (fun u : ℝ => 1 - u) hψ
    (fun (u : EuclideanSpace ℝ (Fin m) × ℝ) (y : EuclideanSpace ℝ (Fin 2)) =>
      psgPFam Ξ Q A B tA tB u.1 u.2 y) hPp
  have hmain := hgen.comp (psgSplitCLM m).contMDiff
  rw [← modelWithCornersSelf_prod]
  rw [chartedSpaceSelf_prod]
  refine hmain.congr fun q => ?_
  simp only [Function.comp_def, psgSplitCLM_apply, psgChainFam, sweepFam]

/-- **The chain side is `C^∞` on the four-box, for a fixed chart perturbation.** -/
theorem psg_contMDiff_chain {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tA tB : ℝ)
    (τ₂ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 4) (𝓡 4) Ctop (psgChainFam Ξ Q c A B tA tB τ₂) := by
  have hp : ContMDiff (𝓡 4) ((𝓡 m).prod (𝓡 4)) Ctop
      (fun p : EuclideanSpace ℝ (Fin 4) => (τ₂, p)) :=
    contMDiff_const.prodMk contMDiff_id
  exact ((psg_contMDiff_chain_joint Ξ Q c hΞ hQ A B tA tB).comp hp).congr fun p => rfl

end


/-! ## The target -/

theorem psg_fam_smoothness {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ)
    (hQ : Work.Drive.IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tA tB : ℝ)
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace :=
      Work.Drive.cappingCharted
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) Work.Drive.CappingSpace := Work.Drive.isManifold_cappingCharted
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.psgLoopFam Ξ Q A B τ₁) ∧
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂) ∧
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.psgLoopFam Ξ Q A B q.1 q.2) ∧
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) =>
        Work.Drive.psgChainFam Ξ Q c A B tA tB q.1 q.2) := by
  refine ⟨psg_contMDiff_loop Ξ Q hΞ hQ A B τ₁,
    psg_contMDiff_chain Ξ Q c hΞ hQ A B tA tB τ₂,
    psg_contMDiff_loop_joint Ξ Q hΞ hQ A B, ?_⟩
  exact psg_contMDiff_chain_joint Ξ Q c hΞ hQ A B tA tB

end Work.Drive
