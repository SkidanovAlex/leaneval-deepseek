import Mathlib.Analysis.InnerProductSpace.Calculus

namespace Commons.Analysis.Savin

open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Hessian (second Fréchet derivative) of the concave paraboloid
`z ↦ -(a/2) * ‖z - y‖ ^ 2 + c` in a real inner product space is the constant linear map
`-a • innerSL ℝ`, valid for every `a`, `c : ℝ` and every centre `y`.

This is the general form of `hessian_concave_paraboloid`, stated for an arbitrary real
inner product space so that it can be reused in other dimensions. -/
theorem hessian_concave_paraboloid_gen (a c : ℝ) (y x : F) :
    fderiv ℝ (fderiv ℝ (fun z : F => -(a / 2) * ‖z - y‖ ^ 2 + c)) x
      = -(a • (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)) := by
  have hgrad : ∀ z : F, fderiv ℝ (fun w : F => -(a / 2) * ‖w - y‖ ^ 2 + c) z
      = (-a) • (innerSL ℝ (z - y) : F →L[ℝ] ℝ) := by
    intro z
    have h1 : HasFDerivAt (fun w : F => ‖w - y‖ ^ 2)
        (2 • (innerSL ℝ (z - y) : F →L[ℝ] ℝ)) z := by
      have hid : HasFDerivAt (fun w : F => w - y) (ContinuousLinearMap.id ℝ F) z := by
        simpa using (hasFDerivAt_id (𝕜 := ℝ) z).sub_const y
      simpa only [ContinuousLinearMap.comp_id] using hid.norm_sq
    have h2 : HasFDerivAt (fun w : F => -(a / 2) * ‖w - y‖ ^ 2 + c)
        ((-(a / 2)) • (2 • (innerSL ℝ (z - y) : F →L[ℝ] ℝ))) z := by
      have h3 : HasFDerivAt (fun w : F => (-(a / 2)) • ‖w - y‖ ^ 2)
          ((-(a / 2)) • (2 • (innerSL ℝ (z - y) : F →L[ℝ] ℝ))) z :=
        h1.const_smul (-(a / 2))
      have h4 : HasFDerivAt (fun w : F => -(a / 2) * ‖w - y‖ ^ 2)
          ((-(a / 2)) • (2 • (innerSL ℝ (z - y) : F →L[ℝ] ℝ))) z := by
        simpa only [smul_eq_mul] using h3
      exact h4.add_const c
    rw [h2.fderiv]
    ext v
    simp only [smul_apply]
    ring
  have hfun : fderiv ℝ (fun w : F => -(a / 2) * ‖w - y‖ ^ 2 + c)
      = fun z => (-a) • (innerSL ℝ (z - y) : F →L[ℝ] ℝ) := funext hgrad
  rw [hfun]
  have hdiff : DifferentiableAt ℝ (fun z : F => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (z - y)) x := by
    have hid : DifferentiableAt ℝ (fun z : F => z - y) x := by
      exact ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y).differentiableAt
    exact (ContinuousLinearMap.differentiableAt (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (x := x - y)).comp
      x hid
  rw [fderiv_fun_const_smul hdiff (-a)]
  have hL : fderiv ℝ (fun z : F => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (z - y)) x
      = (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) := by
    rw [fderiv_fun_comp (f := fun z : F => z - y)
        (g := (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)) x
        (by exact (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).differentiableAt) (by fun_prop)]
    rw [ContinuousLinearMap.fderiv]
    have hsub : fderiv ℝ (fun z : F => z - y) x = ContinuousLinearMap.id ℝ F := by
      simpa using ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y).fderiv
    rw [hsub, ContinuousLinearMap.comp_id]
  rw [hL]
  exact neg_smul a (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)

open scoped RealInnerProductSpace in
theorem hessian_concave_paraboloid (a c : ℝ) (y : EuclideanSpace ℝ (Fin 4))
    (x : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) => -(a / 2) * ‖z - y‖ ^ 2 + c)) x
      = -(a • (innerSL ℝ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ)) := by
  exact hessian_concave_paraboloid_gen a c y x

end Commons.Analysis.Savin