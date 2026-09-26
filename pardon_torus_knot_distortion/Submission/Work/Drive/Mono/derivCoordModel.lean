import Mathlib
import Submission.Work.Drive.Mono.arcHeightAux

namespace Work.Drive.Mono

open Filter

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on the two basis
vectors: `φ (x, y) = x * φ (1, 0) + y * φ (0, 1)`. -/
theorem clm_prod_apply (φ : ℝ × ℝ →L[ℝ] ℝ) (x y : ℝ) :
    φ (x, y) = x * φ (1, 0) + y * φ (0, 1) := by
  have h : ((x, y) : ℝ × ℝ) = x • ((1:ℝ), (0:ℝ)) + y • ((0:ℝ), (1:ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- `faceVertDet` in terms of the derivatives of the two coordinate functions. -/
theorem faceVertDet_coordFun (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3)
    (p : ℝ × ℝ) :
    faceVertDet ψ σ i j p
      = (fderiv ℝ (coordFun ψ σ i) p) (1,0) * (fderiv ℝ (coordFun ψ σ j) p) (0,1)
        - (fderiv ℝ (coordFun ψ σ i) p) (0,1) * (fderiv ℝ (coordFun ψ σ j) p) (1,0) := rfl

/-- `faceTangent` in terms of the derivative of the coordinate function. -/
theorem faceTangent_coordFun (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (p : ℝ × ℝ) :
    faceTangent ψ σ i p
      = (-(fderiv ℝ (coordFun ψ σ i) p) (0,1), (fderiv ℝ (coordFun ψ σ i) p) (1,0)) := rfl

/-- **The coordinate model of a face curve.**  If a curve `q` in the parameter space keeps the
coordinate `σ i` constant and moves the coordinate `σ 2` at unit speed near `t`, and the
coordinate `σ i` is a submersion at `q t`, then the velocity of `q` is tangent to the face curve
`Γ_i`, the velocity of the `σ j`-coordinate is its vertical-tangent determinant times the speed,
and the speed is the reciprocal of the derivative of `σ 2` in the tangent direction. -/
theorem derivCoordModel (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3)
    {A B : ℝ} {q : ℝ → ℝ × ℝ} {t : ℝ}
    (hq : HasDerivAt q (deriv q t) t)
    (hxi : (fun τ => Work.Drive.Mono.coordFun ψ σ i (q τ)) =ᶠ[nhds t] (fun _ => A))
    (hx2 : (fun τ => Work.Drive.Mono.coordFun ψ σ 2 (q τ)) =ᶠ[nhds t] (fun τ => B + τ))
    (hne : fderiv ℝ (Work.Drive.Mono.coordFun ψ σ i) (q t) ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ deriv q t = c • Work.Drive.Mono.faceTangent ψ σ i (q t) ∧
      deriv (fun τ => Work.Drive.Mono.coordFun ψ σ j (q τ)) t =
        c * Work.Drive.Mono.faceVertDet ψ σ i j (q t) ∧
      c * fderiv ℝ (Work.Drive.Mono.coordFun ψ σ 2) (q t)
        (Work.Drive.Mono.faceTangent ψ σ i (q t)) = 1 := by
  have hF (k : Fin 3) : HasFDerivAt (coordFun ψ σ k)
      (fderiv ℝ (coordFun ψ σ k) (q t)) (q t) :=
    ((contDiffAt_coordFun ψ σ k (q t)).differentiableAt (by simp)).hasFDerivAt
  have hchain (k : Fin 3) : HasDerivAt (fun τ => coordFun ψ σ k (q τ))
      (fderiv ℝ (coordFun ψ σ k) (q t) (deriv q t)) t := by
    simpa only [Function.comp_def] using (hF k).comp_hasDerivAt t hq
  have hA : fderiv ℝ (coordFun ψ σ i) (q t) (deriv q t) = 0 := by
    rw [← (hchain i).deriv, hxi.deriv_eq]
    simp
  obtain ⟨c, hc⟩ := eq_smul_of_apply_eq_zero hne hA
  have h2 : fderiv ℝ (coordFun ψ σ 2) (q t) (deriv q t) = 1 := by
    rw [← (hchain 2).deriv, hx2.deriv_eq]
    simp
  have hcond3 : c * fderiv ℝ (coordFun ψ σ 2) (q t) (faceTangent ψ σ i (q t)) = 1 := by
    have hh : fderiv ℝ (coordFun ψ σ 2) (q t) (c • faceTangent ψ σ i (q t)) = 1 := by
      rw [faceTangent_coordFun]
      have h2' := h2
      rw [hc] at h2'
      exact h2'
    rwa [map_smul, smul_eq_mul] at hh
  refine ⟨c, ?_, ?_, ?_, hcond3⟩
  · intro h; rw [h, zero_mul] at hcond3; exact one_ne_zero hcond3.symm
  · rw [hc, faceTangent_coordFun]
  · rw [(hchain j).deriv, hc, faceVertDet_coordFun]
    rw [map_smul, smul_eq_mul]
    congr 1
    rw [clm_prod_apply]
    ring

end Work.Drive.Mono
