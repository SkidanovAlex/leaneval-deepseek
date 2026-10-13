import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Psi.deriv_psiInv
import Submission.Work.WilE9.Psi.hasDerivAt_psi

namespace Work.WilE9.Psi

/-- The derivative of the coordinatewise `psi`: the `j`-th component of the image of a vector `v`
is `psig (x j) ^ 3 * v j`, which is the linear map appearing in the chain rule below. -/
theorem hasFDerivAt_psiV_coord {n : ℕ} (x : Fin n → ℝ) :
    HasFDerivAt WilkiesDesign.E.psiV
      (ContinuousLinearMap.pi fun j : Fin n =>
        (ContinuousLinearMap.toSpanSingleton ℝ (Work.WilE9.psig (x j) ^ 3)).comp
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  change HasFDerivAt (fun y : Fin n → ℝ => fun j : Fin n => WilkiesDesign.E.psi (y j))
    (ContinuousLinearMap.pi fun j : Fin n =>
      (ContinuousLinearMap.toSpanSingleton ℝ (Work.WilE9.psig (x j) ^ 3)).comp
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x
  refine (hasFDerivAt_pi (φ := fun j : Fin n => fun y : Fin n → ℝ => WilkiesDesign.E.psi (y j))
    (φ' := fun j : Fin n =>
      (ContinuousLinearMap.toSpanSingleton ℝ (Work.WilE9.psig (x j) ^ 3)).comp
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))).2 ?_
  intro j
  have hproj : HasFDerivAt (fun y : Fin n → ℝ => y j)
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply j x
  exact ((hasDerivAt_psi (x j)).hasFDerivAt).comp x hproj

/-- **The `psi`-transport of a first derivative.**  If `f : ℝⁿ → ℝ` is `ψ⁻¹ ∘ H ∘ ψ` with `H`
differentiable at `ψ x`, then the `i`-th partial derivative of `f` at `x` is
`(psig (ψ⁻¹ (H (ψ x))) ^ 3)⁻¹ · ∂ᵢH (ψ x) · psig (x i) ^ 3` — a product of the derivative of
`H` in the `ψ`-coordinates with two factors that are algebraic in `(ψ⁻¹ H, psig (ψ⁻¹ H))` and
`(x i, psig (x i))` respectively.  (The first factor is the *reciprocal* of `psig ^ 3`: it is
the derivative of `psiInv`.)  Those two auxiliary coordinates, together with
`psi_sq_add_psig_sq`, are what make the transported derivative formula semi-algebraic: it is
this identity that lets the implicit-function formula for `H` (in the `ψ`-coordinates of the
`Star`-presentation) be converted into the derivative formula for `f`. -/
theorem fderiv_psiInv_comp {n : ℕ} (H : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n)
    (hH : DifferentiableAt ℝ H (WilkiesDesign.E.psiV x))
    (h1 : |H (WilkiesDesign.E.psiV x)| < 1) :
    fderiv ℝ (fun x' : Fin n → ℝ => Work.WilE9.psiInv (H (WilkiesDesign.E.psiV x'))) x
        (Pi.single i (1 : ℝ))
      = (Work.WilE9.psig (Work.WilE9.psiInv (H (WilkiesDesign.E.psiV x))) ^ 3)⁻¹ *
          (fderiv ℝ H (WilkiesDesign.E.psiV x) (Pi.single i (1 : ℝ))) *
          Work.WilE9.psig (x i) ^ 3 := by
  -- the derivative of `psiInv` at the value `H (ψ x)` of the intermediate point
  have hd : HasFDerivAt Work.WilE9.psiInv
      (ContinuousLinearMap.toSpanSingleton ℝ
        ((Work.WilE9.psig (Work.WilE9.psiInv (H (WilkiesDesign.E.psiV x))) ^ 3)⁻¹))
      (H (WilkiesDesign.E.psiV x)) :=
    (deriv_psiInv (H (WilkiesDesign.E.psiV x)) h1).hasFDerivAt
  -- the derivative of the composite `ψ⁻¹ ∘ H`
  have hd2 : HasFDerivAt (Work.WilE9.psiInv ∘ H)
      ((ContinuousLinearMap.toSpanSingleton ℝ
          ((Work.WilE9.psig (Work.WilE9.psiInv (H (WilkiesDesign.E.psiV x))) ^ 3)⁻¹)).comp
        (fderiv ℝ H (WilkiesDesign.E.psiV x)))
      (WilkiesDesign.E.psiV x) :=
    hd.comp (WilkiesDesign.E.psiV x) hH.hasFDerivAt
  -- the chain rule `ψ⁻¹ ∘ H ∘ ψ`
  have hchain :
      HasFDerivAt (fun x' : Fin n → ℝ => Work.WilE9.psiInv (H (WilkiesDesign.E.psiV x')))
        (((ContinuousLinearMap.toSpanSingleton ℝ
            ((Work.WilE9.psig (Work.WilE9.psiInv (H (WilkiesDesign.E.psiV x))) ^ 3)⁻¹)).comp
          (fderiv ℝ H (WilkiesDesign.E.psiV x))).comp
          (ContinuousLinearMap.pi fun j : Fin n =>
            (ContinuousLinearMap.toSpanSingleton ℝ (Work.WilE9.psig (x j) ^ 3)).comp
              (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) x :=
    hd2.comp x (hasFDerivAt_psiV_coord x)
  -- the `ψ`-component of the derivative, evaluated on `eᵢ`
  have key1 : (ContinuousLinearMap.pi fun j : Fin n =>
        (ContinuousLinearMap.toSpanSingleton ℝ (Work.WilE9.psig (x j) ^ 3)).comp
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) (Pi.single i (1 : ℝ))
      = Work.WilE9.psig (x i) ^ 3 • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    funext j
    rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply]
    by_cases h : j = i
    · subst h
      simp [Pi.single_eq_same, smul_eq_mul]
    · rw [Pi.single_eq_of_ne h]
      simp [smul_eq_mul]
  -- `fderiv H` is linear, so the scalar factor comes out
  have key2 : (fderiv ℝ H (WilkiesDesign.E.psiV x))
        (Work.WilE9.psig (x i) ^ 3 • (Pi.single i (1 : ℝ) : Fin n → ℝ))
      = Work.WilE9.psig (x i) ^ 3 *
          (fderiv ℝ H (WilkiesDesign.E.psiV x) (Pi.single i (1 : ℝ))) := by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [hchain.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, key1, key2,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

end Work.WilE9.Psi
