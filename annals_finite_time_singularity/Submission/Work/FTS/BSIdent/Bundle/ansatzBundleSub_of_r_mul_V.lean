/-
# The Liouville bundle for the axis-regular stream function `ψ(r,z) = r · V(r²,z)`

`Work.FTS.BSIdent.Bundle.AnsatzBundleSub ψ` is the class of the Liouville route of the
Biot–Savart identification: the stream-function field of `ψ` is `C¹`, sublinear, and odd.  This
file proves it for the axis-regular (`axiField`) form `ψ(r,z) = r·V(r²,z)`, from

* `hV : V` is jointly `C²`,
* `hV0 : V(0,z) = 0` (axis regularity),
* `hodd : V` is odd in its second variable,
* `hbd :` the two profiles `a = ∂_zV` and `b = -2V - 2w∂_wV` decay like `(1 + √(w+z²))⁻¹` on
  `w ≥ 0`.

The three components of the bundle are then

1. **smoothness** — `psiField (r·V(r²,·)) = axiField a b`
   (`Work.FTS.BSIdent.Cyl.psiField_r_mul_V_eq_axiField`), and `axiField a b` is `C¹` as soon as
   the two profiles are jointly `C¹` (`Work.FTS.BSIdent.Axi.contDiff_axiField`).  The profiles
   are the two partial derivatives of the `C²` function `V`, hence `C¹`; that is the only
   substance here, and it is the content of the two helper lemmas below
   (`fderiv_prod_apply_snd`/`fderiv_prod_apply_fst` identify the partial derivative of the
   curried function with the `fderiv` of the uncurried one, evaluated on `(0,1)` resp. `(1,0)`,
   and `ContDiff.fderiv_right` + `ContDiff.clm_apply` give the regularity);
2. **sublinearity** — `Work.FTS.BSIdent.Cyl.sublinear_axiField`, which needs precisely `hbd`;
3. **oddness** — `Work.Cyl.isOdd_psiField_of_oddZ`, which needs `ψ` odd in `z`; here
   `r·V(r²,-z) = -r·V(r²,z)` is exactly `hodd`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.BSIdent.Bundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Bundle

/-- **The axial partial derivative of a jointly `C²` function of two variables is `C¹`.**

`(w,z) ↦ ∂_z V(w,z)` is the `fderiv` of the uncurried `V`, evaluated on the constant direction
`(0,1)`; the pointwise identification is `Work.Cyl.fderiv_prod_apply_snd`. -/
theorem contDiff_uncurry_pdZ_of_contDiff_two {V : ℝ → ℝ → ℝ}
    (hV : ContDiff ℝ 2 (Function.uncurry V)) :
    ContDiff ℝ 1 (Function.uncurry (fun w z => deriv (fun z' => V w z') z)) := by
  have hF : ContDiff ℝ 2 (fun p : ℝ × ℝ => V p.1 p.2) := hV
  have hdF : ContDiff ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => V p.1 p.2)) :=
    hF.fderiv_right (by norm_num)
  have hcomp : ContDiff ℝ 1
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => V q.1 q.2) p (0, 1)) :=
    hdF.clm_apply (contDiff_const (c := ((0, 1) : ℝ × ℝ)))
  show ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun z' => V p.1 z') p.2)
  rw [show (fun p : ℝ × ℝ => deriv (fun z' => V p.1 z') p.2)
      = (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => V q.1 q.2) p (0, 1)) from by
    funext p
    exact (Work.Cyl.fderiv_prod_apply_snd V p.1 p.2
      (hF.differentiable (by norm_num)).differentiableAt).symm]
  exact hcomp

/-- **The axial profile `b = -2V - 2w∂_wV` of a jointly `C²` function is jointly `C¹`.**

Both summands are products of the `C¹` functions `V`, `∂_wV` (the radial partial derivative,
identified with `fderiv` on `(1,0)` via `Work.Cyl.fderiv_prod_apply_fst`) and the coordinate
`(w,z) ↦ w`. -/
theorem contDiff_uncurry_profileB_of_contDiff_two {V : ℝ → ℝ → ℝ}
    (hV : ContDiff ℝ 2 (Function.uncurry V)) :
    ContDiff ℝ 1 (Function.uncurry
      (fun w z => -2 * V w z - 2 * w * deriv (fun w' => V w' z) w)) := by
  have hF : ContDiff ℝ 2 (fun p : ℝ × ℝ => V p.1 p.2) := hV
  have hdF : ContDiff ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => V p.1 p.2)) :=
    hF.fderiv_right (by norm_num)
  have hcomp : ContDiff ℝ 1
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => V q.1 q.2) p (1, 0)) :=
    hdF.clm_apply (contDiff_const (c := ((1, 0) : ℝ × ℝ)))
  have hW : ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun w' => V w' p.2) p.1) := by
    rw [show (fun p : ℝ × ℝ => deriv (fun w' => V w' p.2) p.1)
        = (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => V q.1 q.2) p (1, 0)) from by
      funext p
      exact (Work.Cyl.fderiv_prod_apply_fst V p.1 p.2
        (hF.differentiable (by norm_num)).differentiableAt).symm]
    exact hcomp
  show ContDiff ℝ 1
    (fun p : ℝ × ℝ => -2 * V p.1 p.2 - 2 * p.1 * deriv (fun w' => V w' p.2) p.1)
  have hV1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => V p.1 p.2) := hF.of_le (by norm_num)
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => -2 * V p.1 p.2) := by
    simpa only [smul_eq_mul] using hV1.const_smul (-2 : ℝ)
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => 2 * p.1) := by fun_prop
  have h3 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => (2 * p.1) * deriv (fun w' => V w' p.2) p.1) := h2.mul hW
  exact h1.sub h3

theorem ansatzBundleSub_of_r_mul_V {V : ℝ → ℝ → ℝ} (hV : ContDiff ℝ 2 (Function.uncurry V))
    (hV0 : ∀ z, V 0 z = 0) (hodd : ∀ w z, V w (-z) = -V w z)
    (hbd : ∃ C : ℝ, 0 < C ∧ ∀ w z, 0 ≤ w →
      ‖deriv (fun z' => V w z') z‖ ≤ C / (1 + Real.sqrt (w + z ^ 2)) ∧
      ‖-2 * V w z - 2 * w * deriv (fun w' => V w' z) w‖
        ≤ C / (1 + Real.sqrt (w + z ^ 2))) :
    Work.FTS.BSIdent.AnsatzBundleSub (fun r z => r * V (r ^ 2) z) := by
  -- the field is the `axiField` with profiles `∂_zV` and `-2V - 2w∂_wV`
  have hfield := Work.FTS.BSIdent.Cyl.psiField_r_mul_V_eq_axiField V hV hV0
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness: `contDiff_axiField` + the `C¹`-regularity of the two profiles
    rw [hfield]
    exact Work.FTS.BSIdent.Axi.contDiff_axiField _ _
      (contDiff_uncurry_pdZ_of_contDiff_two hV)
      (contDiff_uncurry_profileB_of_contDiff_two hV)
  · -- sublinearity: exactly the decay hypothesis `hbd`
    rw [hfield]
    exact Work.FTS.BSIdent.Cyl.sublinear_axiField _ _ hbd
  · -- oddness: `ψ(r,z) = r·V(r²,z)` is odd in `z`
    refine Work.Cyl.isOdd_psiField_of_oddZ (fun r z => ?_)
    show r * V (r ^ 2) (-z) = -(r * V (r ^ 2) z)
    rw [hodd]
    ring

end Work.FTS.BSIdent.Bundle
