/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Bochner–Martinelli row potential and its defect

For a `(0,2)`-form `η : Fin n → Fin n → ℂⁿ → ℂ`, the *Bochner–Martinelli row potential* is the
`(0,1)`-form

  `bmRow η i z = -γ⁻¹ Σ_l ∫ bmKernel l x · η_{i l} (z + x) dx`     (`γ = bmGamma n ≠ 0`),

i.e. the Bochner–Martinelli potential of the `i`-th row of `η`.  It is the explicit linear solution
operator for the *supported* `(0,2)`-problem: if `η` has `C¹`, compactly supported, `∂̄`-closed
(antisymmetric) components then `∂̄_j (bmRow η)_k - ∂̄_k (bmRow η)_j = η_{jk}` everywhere.

Applying one step to the cut-off form `χ · ζ` (with `χ` smooth of compact support) produces a
*defect*: with

  `H(χ,ζ)_{jk,l} := ∂̄_l χ · ζ_{jk} + ∂̄_j χ · ζ_{kl} - ∂̄_k χ · ζ_{jl}`

one has the pointwise identity (for `ζ` closed, `C¹`)

  `∂̄_j (bmRow (χ·ζ))_k - ∂̄_k (bmRow (χ·ζ))_j = ζ_{jk} + bmDefect χ ζ j k`,

  `bmDefect χ ζ j k = (χ - 1) ζ_{jk} - γ⁻¹ bmPot (H(χ,ζ)_{jk,·})`,

obtained by differentiating the potential under the integral sign (`bmPot_dbarCoord`), using
closedness of `ζ` and the Bochner–Martinelli divergence formula applied to the supported translate
of `ζ_{jk}`.  The point of the formula is that `H(χ,ζ)` is *algebraic* in `ζ` — it never involves a
derivative of `ζ` — so `bmPot (H(χ,ζ)_{jk,·})` gains one derivative over `ζ` on the region where
`χ = 1` (where the term `(χ-1)ζ` vanishes).
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.telescopeTwo

noncomputable section

open scoped NNReal ENNReal
open Set
open Work.CR.Flat

namespace Work.NN.Core

variable {n : ℕ}

/-- The Bochner–Martinelli row potential `bmRow η i = -γ⁻¹ bmPot (η_{i·})`. -/
noncomputable def bmRow (η : Fin n → Fin n → Cn n → ℂ) : Fin n → Cn n → ℂ :=
  fun i z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
    Work.CR.Flat.Cauchy.bmPot (fun l => η i l) z

/-- The `(0,2)`-form `H(χ,ζ)_{jk,l} = ∂̄_l χ · ζ_{jk} + ∂̄_j χ · ζ_{kl} - ∂̄_k χ · ζ_{jl}` which
appears in the defect of one Bochner–Martinelli step. -/
noncomputable def bmH (χ : Cn n → ℂ) (ζ : Fin n → Fin n → Cn n → ℂ) :
    Fin n → Fin n → Fin n → Cn n → ℂ :=
  fun j k l w => Work.CR.Flat.dbarCoord l χ w * ζ j k w
    + Work.CR.Flat.dbarCoord j χ w * ζ k l w
    - Work.CR.Flat.dbarCoord k χ w * ζ j l w

/-- The defect of one Bochner–Martinelli step applied to `χ · ζ`:
`bmDefect χ ζ j k = (χ - 1) ζ_{jk} - γ⁻¹ bmPot (H(χ,ζ)_{jk,·})`. -/
noncomputable def bmDefect (χ : Cn n → ℂ) (ζ : Fin n → Fin n → Cn n → ℂ) :
    Fin n → Fin n → Cn n → ℂ :=
  fun j k z => (χ z - 1) * ζ j k z
    - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
        Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j k l) z

@[simp] lemma bmRow_apply (η : Fin n → Fin n → Cn n → ℂ) (i : Fin n) (z : Cn n) :
    bmRow η i z = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
      Work.CR.Flat.Cauchy.bmPot (fun l => η i l) z := rfl

@[simp] lemma bmDefect_apply (χ : Cn n → ℂ) (ζ : Fin n → Fin n → Cn n → ℂ)
    (j k : Fin n) (z : Cn n) :
    bmDefect χ ζ j k z = (χ z - 1) * ζ j k z
      - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
          Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j k l) z := rfl

end Work.NN.Core
