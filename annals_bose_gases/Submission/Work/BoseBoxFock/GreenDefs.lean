import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Submission.Work.BoseBoxFock.AliasDefs
import Submission.Work.BoseFixR.LocaliseProof.C1DirFTC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.GreenDefs` — the coordinate IBP toolkit of the logarithmic peel

The target

    ∫_u (Δ𝒢)(u)‖u−z‖^{−2} = ∫_u (Δ²𝒢)(u)log‖u−z‖      (𝒢 = re (autocorr g), ‖z‖ ≥ ℓ)

is the second Newtonian peel `Δ log‖·‖ = ‖·‖^{−2}`.  It is proved by two integrations by parts
against a *regularised* logarithmic kernel

    `kernelEps ε x = ½·log(‖x‖² + ε²)`   (`ε > 0`),

whose Laplacian is explicit and everywhere smooth, followed by `ε → 0⁺`.  This file fixes the
vocabulary:

* `dirB i` — the coordinate directions (the standard orthonormal basis of `EuclideanSpace ℝ (Fin 3)`,
  written `Submission.BoseGases.kcStdBasis` so that it is *definitionally* the basis of the
  fundamental-theorem-of-calculus lemma `Work.BoseFixR.LocaliseProof.integral_fderiv_kcStdBasis_eq_zero`);
* `lapPt f x = ∑ᵢ ∂ᵢ∂ᵢ f x` — the coordinate Laplacian, identified with `Laplacian.laplacian`
  in `Work.BoseBoxFock.lapPt_eq_laplacian`;
* `kernelEps ε` — the regularised logarithmic potential.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped Real

/-- The three coordinate directions of `ℝ³`, matching the basis of the workspace FTC lemma. -/
noncomputable def dirB (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  Submission.BoseGases.kcStdBasis i

/-- The **coordinate Laplacian** `lapPt f x = ∑ᵢ ∂ᵢ∂ᵢ f x` of a function on `ℝ³`. -/
noncomputable def lapPt (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ f y (dirB i)) x (dirB i)

/-- The **regularised logarithmic potential** `K_ε(x) = ½·log(‖x‖² + ε²)`, whose Laplacian is
`(‖x‖² + 3ε²)/(‖x‖² + ε²)²` and tends, as `ε → 0⁺`, to `log‖x‖` pointwise (off `0`) and to
`‖x‖^{−2}` in the Laplacian. -/
noncomputable def kernelEps (ε : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 / 2) * Real.log (‖x‖ ^ 2 + ε ^ 2)

end Work.BoseBoxFock
