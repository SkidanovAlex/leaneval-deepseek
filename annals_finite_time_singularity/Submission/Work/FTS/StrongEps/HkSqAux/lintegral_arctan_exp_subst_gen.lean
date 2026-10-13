/-
Copyright: work module for the Elgindi finite-time singularity project.

# `lintegral_arctan_exp_subst_gen`

The log-coordinate substitution `θ = arctan (e^ζ)` in the angular variable, in `lintegral` form
for an **arbitrary** `ENNReal`-valued function `U` (so that no real-valued function `F` with
`U = ENNReal.ofReal ∘ F`, and no integrability hypothesis, is needed).  This is the general
form of `lintegral_arctan_exp_subst`, which only covers `U = ENNReal.ofReal ∘ F` and cannot be
applied directly to a general `U` (the two functions agree only off the set where `U = ⊤`).

The Jacobian is `kappa ζ = (arctan ∘ exp)'(ζ) = e^ζ / (1 + e^{2ζ})`, and `ζ ↦ arctan (e^ζ)` is
a strictly monotone bijection of `ℝ` onto `(0, π/2)` (`Defs.range_arctan_exp`).

The proof is the one-dimensional monotone change-of-variables formula
`MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`, applied on `Set.univ`:
with `f := fun ζ => arctan (e^ζ)`, `f' := kappa`, `s := univ`, it gives

  `∫⁻ θ in f '' univ, U θ = ∫⁻ ζ in univ, ofReal (kappa ζ) * U (f ζ)`,

and `f '' univ = range f = Ioo 0 (π/2)` by `Defs.range_arctan_exp`; the restricted integral
over `univ` is the unrestricted integral.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_arctan_exp_subst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

theorem lintegral_arctan_exp_subst_gen (U : ℝ → ENNReal) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2), U θ)
      = ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.kappa ζ)
          * U (Real.arctan (Real.exp ζ)) := by
  have hmono : MonotoneOn (fun ζ : ℝ => Real.arctan (Real.exp ζ)) Set.univ :=
    strictMono_arctan_exp.monotone.monotoneOn Set.univ
  have hderiv : ∀ ζ ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) (kappa ζ) Set.univ ζ :=
    fun ζ _ => (hasDerivAt_arctan_exp ζ).hasDerivWithinAt
  have h := MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := Set.univ) (f := fun ζ : ℝ => Real.arctan (Real.exp ζ)) (f' := kappa)
    MeasurableSet.univ hderiv hmono U
  have hrange : Set.range (fun ζ : ℝ => Real.arctan (Real.exp ζ)) = Set.Ioo 0 (Real.pi / 2) := by
    simpa [Set.image_univ] using range_arctan_exp
  simpa [hrange] using h

end Work.FTS.StrongEps.HkSqAux
