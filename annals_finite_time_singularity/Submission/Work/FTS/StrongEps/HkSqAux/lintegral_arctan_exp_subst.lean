/-
Copyright: work module for the Elgindi finite-time singularity project.

# `lintegral_arctan_exp_subst`

The log-coordinate substitution `θ = arctan (e^ζ)` in the angular variable, in `lintegral` form
(so that no integrability hypothesis on `F` is needed).  The Jacobian is
`kappa ζ = (arctan ∘ exp)'(ζ) = e^ζ / (1 + e^{2ζ})`, and `ζ ↦ arctan (e^ζ)` is a strictly
monotone bijection of `ℝ` onto `(0, π/2)` (`range_arctan_exp`, in `Defs.lean`).

The proof is the one-dimensional monotone change-of-variables formula
`MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`, applied on `Set.univ`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.FTS.StrongEps.HkSqAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

/-- `ζ ↦ arctan (e^ζ)` is strictly increasing. -/
theorem strictMono_arctan_exp : StrictMono fun ζ : ℝ => Real.arctan (Real.exp ζ) :=
  Real.arctan_strictMono.comp Real.exp_strictMono

/-- The derivative of `ζ ↦ arctan (e^ζ)` is `kappa`. -/
theorem hasDerivAt_arctan_exp (ζ : ℝ) :
    HasDerivAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) (kappa ζ) ζ := by
  have h1 : HasDerivAt (fun ζ' : ℝ => Real.exp ζ') (Real.exp ζ) ζ := Real.hasDerivAt_exp ζ
  have h2 := (Real.hasDerivAt_arctan (Real.exp ζ)).comp ζ h1
  have hdv : (1 / (1 + (Real.exp ζ) ^ 2)) * Real.exp ζ = kappa ζ := by
    rw [kappa]
    have h4 : 1 + (Real.exp ζ) ^ 2 = 1 + Real.exp (2 * ζ) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [h4, div_eq_mul_inv]
    ring_nf
  exact hdv ▸ h2

theorem lintegral_arctan_exp_subst (F : ℝ → ℝ) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (F θ))
      = ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.kappa ζ)
          * ENNReal.ofReal (F (Real.arctan (Real.exp ζ))) := by
  have hmono : MonotoneOn (fun ζ : ℝ => Real.arctan (Real.exp ζ)) Set.univ :=
    strictMono_arctan_exp.monotone.monotoneOn Set.univ
  have hderiv : ∀ ζ ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) (kappa ζ) Set.univ ζ :=
    fun ζ _ => (hasDerivAt_arctan_exp ζ).hasDerivWithinAt
  have h := MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := Set.univ) (f := fun ζ : ℝ => Real.arctan (Real.exp ζ)) (f' := kappa)
    MeasurableSet.univ hderiv hmono (fun θ => ENNReal.ofReal (F θ))
  have hrange : Set.range (fun ζ : ℝ => Real.arctan (Real.exp ζ)) = Set.Ioo 0 (Real.pi / 2) := by
    simpa [Set.image_univ] using range_arctan_exp
  simpa [hrange] using h

end Work.FTS.StrongEps.HkSqAux
