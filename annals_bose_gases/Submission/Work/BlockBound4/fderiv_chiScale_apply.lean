import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BlockBound4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4

/-- **Chain rule for the scaled cutoff `χ_s(x) = χ(s⁻¹ • x)`**
(`Submission.BoseGases.chiScale`): differentiating the rescaling
`y ↦ s⁻¹ • y` (a continuous linear map with itself as derivative) and using
that `χ` is `C^∞` (`Submission.BoseGases.chi_contDiff`) gives

    d(χ_s)_x(v) = s⁻¹ · dχ_{s⁻¹•x}(v).

No hypothesis on `s` is needed: at `s = 0` both sides vanish
(`chiScale 0` is the constant `χ 0`). -/
theorem fderiv_chiScale_apply (s : ℝ) (x v : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (Submission.BoseGases.chiScale s) x v
      = s⁻¹ * fderiv ℝ Submission.BoseGases.chi ((s⁻¹) • x) v := by
  -- `χ` is differentiable everywhere (it is `C^∞`).
  have hchi : DifferentiableAt ℝ Submission.BoseGases.chi ((s⁻¹) • x) :=
    Submission.BoseGases.chi_contDiff.differentiable (by norm_num) _
  -- The rescaling `y ↦ s⁻¹ • y` is continuous linear, hence its own derivative.
  have hlin : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => (s⁻¹) • y)
      ((s⁻¹) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) x :=
    (hasFDerivAt_id x).const_smul (s⁻¹)
  -- Chain rule.
  have hcomp : HasFDerivAt
      (Submission.BoseGases.chi ∘ fun y : EuclideanSpace ℝ (Fin 3) => (s⁻¹) • y)
      ((fderiv ℝ Submission.BoseGases.chi ((s⁻¹) • x)) ∘SL
        ((s⁻¹) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)))) x :=
    hchi.hasFDerivAt.comp x hlin
  have hfun : Submission.BoseGases.chiScale s
      = (Submission.BoseGases.chi ∘ fun y : EuclideanSpace ℝ (Fin 3) => (s⁻¹) • y) := rfl
  rw [hfun, hcomp.fderiv]
  -- Evaluate the composite at `v` and use `ℝ`-linearity.
  rw [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

end Work.BlockBound4
