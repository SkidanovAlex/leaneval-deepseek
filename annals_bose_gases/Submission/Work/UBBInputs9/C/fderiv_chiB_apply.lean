import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.C

open Submission.BoseGases

/-- The pointwise Fréchet derivative of the `u`-localised cutoff
`chiB ℓ d u = chiScale ℓ · (chiScale (ℓ*d) ∘ (· - (ℓ*d)•u))` is the product rule:
`χ_{B(u)} = χ_ℓ · (χ_{ℓd}(· - ℓd u))` so
`dχ_{B(u)}(x)e = χ_ℓ(x)·dχ_{ℓd}(x - ℓd u)e + χ_{ℓd}(x - ℓd u)·dχ_ℓ(x)e`. -/
theorem fderiv_chiB_apply (ℓ d : ℝ) (hℓ : ℓ ≠ 0) (hd : d ≠ 0)
    (u x e : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB ℓ d u y) x e
      = Submission.BoseGases.chiScale ℓ x *
          (fderiv ℝ (Submission.BoseGases.chiScale (ℓ * d)) (x - (ℓ * d) • u) e)
        + Submission.BoseGases.chiScale (ℓ * d) (x - (ℓ * d) • u) *
          (fderiv ℝ (Submission.BoseGases.chiScale ℓ) x e) := by
  have hld : ℓ * d ≠ 0 := mul_ne_zero hℓ hd
  have hf : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 3) => chiScale ℓ y) x :=
    (chiScale_contDiff hℓ).contDiffAt.differentiableAt (by simp)
  have hT : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 3) => y - (ℓ * d) • u) x := by
    fun_prop
  have hg : DifferentiableAt ℝ
      (fun y : EuclideanSpace ℝ (Fin 3) => chiScale (ℓ * d) (y - (ℓ * d) • u)) x :=
    ((chiScale_contDiff hld).contDiffAt.differentiableAt (by simp)).comp x hT
  have hcomp : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        chiScale (ℓ * d) (y - (ℓ * d) • u)) x
      = fderiv ℝ (chiScale (ℓ * d)) (x - (ℓ * d) • u) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 3) => chiScale (ℓ * d) (y - (ℓ * d) • u))
          = chiScale (ℓ * d) ∘ (fun y : EuclideanSpace ℝ (Fin 3) => y - (ℓ * d) • u)
          from rfl]
    rw [fderiv_comp x ((chiScale_contDiff hld).contDiffAt.differentiableAt (by simp)) hT]
    rw [show (fun y : EuclideanSpace ℝ (Fin 3) => y - (ℓ * d) • u)
          = (fun y : EuclideanSpace ℝ (Fin 3) =>
              (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) y - (ℓ * d) • u)
          from rfl]
    rw [fderiv_sub_const
      (f := (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))) ((ℓ * d) • u)]
    rw [fderiv_id]
    exact ContinuousLinearMap.comp_id _
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) => chiB ℓ d u y)
        = (fun y => chiScale ℓ y) * (fun y => chiScale (ℓ * d) (y - (ℓ * d) • u))
        from rfl]
  rw [fderiv_mul hf hg, hcomp]
  simp [add_apply, smul_apply]

end Work.UBBInputs9.C
