import Mathlib
import Submission.Work.Drive.cone_chain

namespace Work.Drive

/-!
# The derivative of `H ∘ (x ↦ (x 0, x 1))`

The coordinate projection `p : ℝ³ → ℝ²`, `p u = (u 0, u 1)`, is linear, hence its own derivative;
composing with a differentiable `H : ℝ² → Z` and applying the chain rule gives the Fréchet
derivative of `u ↦ H (u 0, u 1)`, evaluated on a vector `w`, as `fderiv H (p x) (p w)`.

`mk2ProjCLM` is `p` packaged as a continuous linear map, built from the coordinate projections
`PiLp.proj` and the canonical identification `PiLp 2 (fun _ => ℝ) ≃L (Fin 2 → ℝ)`.
-/

/-- The coordinate projection `u ↦ (u 0, u 1)` from `ℝ³` to `ℝ²`, as a continuous linear map. -/
noncomputable def mk2ProjCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm :
      (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ∘L
    ContinuousLinearMap.pi (fun i : Fin 2 =>
      if i = 0 then PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 else PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1)

/-- `mk2ProjCLM` computes `u ↦ mk2 (u 0) (u 1)`. -/
lemma mk2ProjCLM_apply (u : EuclideanSpace ℝ (Fin 3)) :
    mk2ProjCLM u = mk2 (u 0) (u 1) := by
  have hcoe : ∀ v : Fin 2 → ℝ,
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm :
        (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) v = WithLp.toLp 2 v := fun v => rfl
  simp only [mk2ProjCLM, ContinuousLinearMap.comp_apply, hcoe, mk2]
  congr 1
  ext i
  fin_cases i <;> simp [ContinuousLinearMap.pi_apply, PiLp.proj_apply]

/-- **Chain rule for the coordinate projection**: the derivative of `u ↦ H (u 0, u 1)` at `x`,
applied to `w`, is the derivative of `H` at `(x 0, x 1)` applied to `(w 0, w 1)`. -/
theorem fderiv_mk2_proj_comp_apply
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (H : EuclideanSpace ℝ (Fin 2) → Z) (x w : EuclideanSpace ℝ (Fin 3))
    (hH : DifferentiableAt ℝ H (Work.Drive.mk2 (x 0) (x 1))) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => H (Work.Drive.mk2 (u 0) (u 1))) x w
      = fderiv ℝ H (Work.Drive.mk2 (x 0) (x 1)) (Work.Drive.mk2 (w 0) (w 1)) := by
  have hfun : (fun u : EuclideanSpace ℝ (Fin 3) => mk2 (u 0) (u 1)) = ⇑mk2ProjCLM :=
    funext (fun u => (mk2ProjCLM_apply u).symm)
  have hg : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin 3) => mk2 (u 0) (u 1)) mk2ProjCLM x := by
    simpa only [hfun] using mk2ProjCLM.hasFDerivAt (x := x)
  have hHd : HasFDerivAt H (fderiv ℝ H (mk2 (x 0) (x 1))) (mk2 (x 0) (x 1)) := hH.hasFDerivAt
  have hcomp : HasFDerivAt (H ∘ fun u : EuclideanSpace ℝ (Fin 3) => mk2 (u 0) (u 1))
      ((fderiv ℝ H (mk2 (x 0) (x 1))) ∘SL mk2ProjCLM) x := hHd.comp x hg
  have hfder : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => H (mk2 (u 0) (u 1))) x
      = (fderiv ℝ H (mk2 (x 0) (x 1))) ∘SL mk2ProjCLM := hcomp.fderiv
  rw [hfder, ContinuousLinearMap.comp_apply, mk2ProjCLM_apply]

end Work.Drive
