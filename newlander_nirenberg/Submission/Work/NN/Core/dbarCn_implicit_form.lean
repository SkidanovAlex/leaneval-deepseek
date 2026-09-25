import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.DbarCnPertAux

/-!
# The implicit (coupled) form of the perturbed `∂̄`-equation on `ℂⁿ`

The Beltrami system attached to `∂̄_{Jstd + A}` was written in `DbarCnPertAux` in *implicit*
form: if `dbarCn (Jstd + A) W z = 0` then `∂̄_k W(z) = Σ_j (β k j z ∂_j W(z) - conj(β k j z) ∂̄_j W(z))`.
That requires the equation to hold.  Here we record the **identity underlying it**, valid for
*every* `W`, with no hypothesis at all:

`(1 + BopBar A z) (∂̄ W(z)) = (∂̄_{Jstd + A} W(z))(e_j)_j + Bop A z (∂ W(z))`,

i.e. coordinatewise
`∂̄_k W(z) + Σ_j conj(β k j z) ∂̄_j W(z) = ∂̄_{Jstd + A,k} W(z) + Σ_j β k j z ∂_j W(z)`.

Setting the first term of the right-hand side to zero recovers the implicit Beltrami form.
The point of the present shape is that the *coefficient vector* `∂̄W(z)` is described by a
matrix acting on itself (the term `BopBar A z (∂̄W)`) plus the perturbation term
`dbarCoef_lin` (via `Lcoef`) and the `∂`-derivative vector; this is what makes the
small-perturbation estimate a contraction estimate on the vector of Wirtinger derivatives.

The proof is the Wirtinger decomposition `fderiv_eq_sum_dCoord_dbarCoord` and the definitional
identity `conj(β k j z) = (I/2) · conj((A z e_k)_j)`, both of which are already in the library.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

/-- **The implicit form of the perturbed `∂̄`-equation**, valid for every `W`:
`(1 + \bar B(z)) ∂̄W(z) = ∂̄_{Jstd+A}W(z) + B(z) ∂W(z)`. -/
theorem dbarCn_implicit_form {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (W : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) :
    (1 + Work.NN.Core.BopBar A z) (fun j => Work.CR.Flat.dbarCoord j W z)
      = (fun j => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) W z (Pi.single j (1 : ℂ)))
        + Work.NN.Core.Bop A z (fun j => Work.CR.Flat.dCoord j W z) := by
  ext k
  have hβ : ∀ j : Fin n, starRingEnd ℂ (betaCoef A k j z)
      = (Complex.I / 2) * starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j) := by
    intro j
    simp only [betaCoef, map_mul, map_neg, map_div₀, map_ofNat, Complex.conj_I]
    ring
  have hL : Lcoef A W k z
      = ∑ j : Fin n, ((Complex.I / 2) * ((A z (Pi.single k (1 : ℂ))) j
            * Work.CR.Flat.dCoord j W z)
        + (Complex.I / 2) * (starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j)
            * Work.CR.Flat.dbarCoord j W z)) := by
    rw [Lcoef, fderiv_eq_sum_dCoord_dbarCoord, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- peel the operator identities down to coordinates
  simp only [add_apply, one_apply_eq_self, Pi.add_apply,
    BopBar_apply, Bop_apply, dbarCoef_lin, hL]
  -- normalise the two sums
  have h1 : (∑ j : Fin n, Work.CR.Flat.dbarCoord j W z * starRingEnd ℂ (betaCoef A k j z))
      = ∑ j : Fin n, (Complex.I / 2) * (starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j)
          * Work.CR.Flat.dbarCoord j W z) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hβ j]; ring
  have h2 : (∑ j : Fin n, Work.CR.Flat.dCoord j W z * betaCoef A k j z)
      = ∑ j : Fin n, -((Complex.I / 2) * ((A z (Pi.single k (1 : ℂ))) j
          * Work.CR.Flat.dCoord j W z)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [betaCoef]; ring
  rw [h1, h2, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

end Work.NN.Core
