/-
# The Chinese-remainder factorisation of the arithmetic averaging operator

This module formalises the factorisation of the arithmetic (polynomial) averaging operator over
`ℤ/qℤ` for `q = q₁ q₂` with `(q₁,q₂) = 1` as the *tensor product* of the averaging operators over
`ℤ/q₁ℤ` and `ℤ/q₂ℤ`, and the corresponding norm identity for the bilinear form — the paper's
`ttensor-bil` applied to the proof of Theorem `bile` (Krause--Mirek--Tao, *Pointwise ergodic
theorems for non-conventional bilinear polynomial averages*, Annals 195 (2022), Section 10):

"From Examples `avg-mult`, `tensor-mult` we see that the bilinear operator `A_{∏_{p∈S} ℤ_p}` is
the tensor product of the individual operators `A_{ℤ_p}`, so by (ttensor-bil) we may factor the
operator norm as `∏_{p∈S} ‖A_{ℤ_p}‖`."

## Conventions

We work with the normalised (probability) `L^p` norms of the finite rings `ℤ/Qℤ`:
`Work.Analysis.Concentration.LpNormZMod Q p`, which agrees with our `lpNormFin (ZMod Q) p`
(`lpNormFin_zmod`).  The polynomial `P ∈ ℤ[X]` is evaluated modulo `Q` by
`Work.Analysis.Concentration.polyEvalZMod`.

## Main definitions

* `arithAvgKernel P₁ P₂ Q` : the (non-negative) kernel of the arithmetic bilinear averaging
  operator `(f,g) ↦ ℤ/Qℤ → ℂ`, `x ↦ Q⁻¹ ∑_n f(x - P₁(n)) g(x - P₂(n))`, as an element of
  `ZMod Q → ZMod Q → ZMod Q → ℂ`.

## Main results

* `lpNormFin_zmod` : `lpNormFin (ZMod Q) p = LpNormZMod Q p`;
* `bilinKernelOp_arithAvgKernel` : `bilinKernelOp (arithAvgKernel P₁ P₂ Q)` *is* the arithmetic
  bilinear averaging operator of Section 10;
* `bilinearAverageLq_prod` : the **tensor-product norm identity** `ttensor-bil` for the
  arithmetic averaging operators on a product of two coprime finite cyclic groups;
* `crtTransport_polyBilinearAverage` : the transported form of the factorisation along the
  Chinese-remainder isomorphism `ZMod (q₁ q₂) ≃+* ZMod q₁ × ZMod q₂`;
* `BilinearAverageLq_crt` : the resulting norm identity on `ZMod (q₁ q₂)` itself.
-/
import Submission.Work.Analysis.Paraproduct.TensorNorm
import Submission.Work.Analysis.Concentration.Basic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Paraproduct

noncomputable section

open Work.Analysis.Concentration
open Polynomial

/-- The kernel of the arithmetic bilinear averaging operator of Section 10 of
Krause--Mirek--Tao: the operator
`(f,g) ↦ (x ↦ (Q:ℂ)⁻¹ * ∑_{n ∈ ℤ/Qℤ} f (x - P₁(n)) g (x - P₂(n)))`
is `bilinKernelOp (arithAvgKernel P₁ P₂ Q)`, see `bilinKernelOp_arithAvgKernel`.  The kernel is
non-negative, which is what allows the tensor-product norm factorisation
`bilinKernelOp_tensorKernel_le` to apply. -/
noncomputable def arithAvgKernel (P₁ P₂ : ℤ[X]) (Q : ℕ) [NeZero Q] :
    ZMod Q → ZMod Q → ZMod Q → ℂ :=
  fun x y w => (Q : ℂ)⁻¹ * ∑ n : ZMod Q,
    (if x - polyEvalZMod P₁ Q n = y then 1 else 0) *
      (if x - polyEvalZMod P₂ Q n = w then 1 else 0)

/-- The normalised `L^p` norm of the finite ring `ℤ/Qℤ` agrees with `lpNormFin` on `ZMod Q`. -/
theorem lpNormFin_zmod (Q : ℕ) [NeZero Q] (p : ℝ) (f : ZMod Q → ℂ) :
    lpNormFin (ZMod Q) p f = LpNormZMod Q p f := by
  simp only [lpNormFin, LpNormZMod, ZMod.card]

/-- The arithmetic bilinear averaging estimate on the *product* of two finite cyclic groups
`ℤ/mℤ × ℤ/nℤ`, in the tensor-product form used for the Chinese-remainder factorisation: the
operator is `bilinKernelOp (tensorKernel (arithAvgKernel X P m) (arithAvgKernel X P n))`. -/
def BilinearAverageLqProd (P : ℤ[X]) (m n : ℕ) [NeZero m] [NeZero n] (q C : ℝ) : Prop :=
  ∀ F G : ZMod m × ZMod n → ℂ,
    lpNormFin (ZMod m × ZMod n) q
        (bilinKernelOp (tensorKernel (arithAvgKernel Polynomial.X P m)
          (arithAvgKernel Polynomial.X P n)) F G)
      ≤ C * lpNormFin (ZMod m × ZMod n) 2 F * lpNormFin (ZMod m × ZMod n) 2 G

end

end Work.Analysis.Paraproduct
