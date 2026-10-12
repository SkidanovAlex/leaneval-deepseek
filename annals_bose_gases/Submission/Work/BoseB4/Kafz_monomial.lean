import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.BargmannLift
import Submission.Work.BoseB4.Phi_a0d
import Submission.Work.BoseB4.adjoint_a0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Kafz_monomial` — the `c`-number substitution for one anti-normal monomial

FS §8.3 (`thm:Kafz`) replace the condensate ladder operators by the complex numbers
`z`, `z̄` by resolving the identity in coherent states `|z⟩ = e^{z a₀†}Ω`,
`dν(z) = e^{-|z|²} d²z/π`.  For the *anti-normal monomial* of FS `eq:HLambdaSecond`

    `monoOp p q B = a₀^p ∘ (a₀†)^q ∘ lift B`

(with `B` an operator on the spectator space `𝓕(θ^⊥)`, `lift B` acting levelwise in
the condensate number) the substitution rule `a₀ ↦ z`, `a₀† ↦ z̄` reads

    `⟪Ψ, a₀^p (a₀†)^q (lift B) Ψ⟫ = ∫_ℂ z^p z̄^q ⟪Φ Ψ z, B (Φ Ψ z)⟫ dν(z)`

— the statement proved below.  The case `p = q = 0` is the Bargmann isometry with a
spectator operator (`Work.BoseB4.bargmann_lift`), and the general case is obtained
from it by (i) moving the `a₀^p` to the *left* by adjointness (`a0d` is the Hilbert
adjoint of `a0`, `Work.BoseB4.adjoint_a0`), (ii) using that `Φ (a₀†)^q Ψ = z̄^q Φ Ψ`
(`Work.BoseB4.Phi_a0d`), and (iii) the fact that `z̄^p`, being a *constant* on the
left slot of a sesquilinear form, contributes `z^p` (the inner product is
conjugate-linear in its first argument).

## The pieces

* `Phi_a0dpow` — `Φ ((a₀†)^q Ψ) z = z̄^q • Φ Ψ z` (induction from `Phi_a0d`);
* `a0d_comp_a0dpow` — `a0d ∘ (a0†)^q = (a0†)^q ∘ a0d` (powers of one operator
  commute, by associativity — *no* CCR needed);
* `lift_comp_a0dpow`, `lift_comm_a0dpow` — the spectator operators `lift B` commute
  with the powers of `a₀†` (`Work.BoseB4.lift_comm_a0d`);
* `inner_a0pow_a0dpow` — `⟪Ψ, (a₀)^p Ψ'⟫ = ⟪(a₀†)^p Ψ, Ψ'⟫`: the iterated form of
  `adjoint_a0`, by induction on `p`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Creation acts on the coherent-state transform as multiplication by the
appropriate power of `z̄`: `Φ ((a₀†)^q Ψ) z = z̄^q • Φ Ψ z`.  Iteration of
`Work.BoseB4.Phi_a0d` (the substitution rule `a₀† ↦ z̄`). -/
lemma Phi_a0dpow (q : ℕ) (Ψ : FockCore E) (z : ℂ) :
    Phi (a0dpow q Ψ) z = (starRingEnd ℂ z) ^ q • Phi Ψ z := by
  induction q generalizing Ψ with
  | zero => simp
  | succ d ih =>
    rw [a0dpow_succ, LinearMap.comp_apply, ih (a0d Ψ), Phi_a0d, smul_smul, pow_succ]

/-- `a₀†` commutes with its own powers: `a0d ∘ (a₀†)^q = (a₀†)^q ∘ a0d`.  Purely
associative — the recursive definition of `a0dpow` already has `a0d` on the right. -/
lemma a0d_comp_a0dpow (q : ℕ) :
    (a0d : FockCore E →ₗ[ℂ] FockCore E).comp (a0dpow q) = (a0dpow q).comp a0d := by
  induction q with
  | zero => ext x; simp
  | succ d ih =>
    rw [a0dpow_succ, ← LinearMap.comp_assoc, ih]

/-- A spectator operator commutes with the powers of condensate creation:
`lift B ∘ (a₀†)^q = (a₀†)^q ∘ lift B`. -/
lemma lift_comp_a0dpow (B : E →ₗ[ℂ] E) (q : ℕ) :
    (lift B).comp (a0dpow q) = (a0dpow q).comp (lift B) := by
  induction q with
  | zero => ext x; simp
  | succ d ih =>
    rw [a0dpow_succ, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, lift_comm_a0d,
      ← LinearMap.comp_assoc, ← a0dpow_succ]

/-- The applied form of `lift_comp_a0dpow`. -/
lemma lift_comm_a0dpow (B : E →ₗ[ℂ] E) (q : ℕ) (Ψ : FockCore E) :
    lift B (a0dpow q Ψ) = a0dpow q (lift B Ψ) := by
  rw [← LinearMap.comp_apply, lift_comp_a0dpow, LinearMap.comp_apply]

/-- **The iterated adjointness of the ladder operators**: moving `p` annihilations
from the second slot to the first slot turns them into `p` creations,
`⟪Ψ, a₀^p Ψ'⟫ = ⟪(a₀†)^p Ψ, Ψ'⟫`.  Induction on `p`, the step being
`adjoint_a0d` (`a₀` is the adjoint of `a₀†`). -/
lemma inner_a0pow_a0dpow (p : ℕ) (Ψ Ψ' : FockCore E) :
    inner ℂ (Embed E Ψ) (Embed E (a0pow p Ψ'))
      = inner ℂ (Embed E (a0dpow p Ψ)) (Embed E Ψ') := by
  induction p generalizing Ψ Ψ' with
  | zero => simp
  | succ d ih =>
    rw [a0pow_succ, LinearMap.comp_apply, ih Ψ (a0 Ψ')]
    rw [← adjoint_a0d (a0dpow d Ψ) Ψ']
    congr 1
    have h : a0d (a0dpow d Ψ) = a0dpow (d + 1) Ψ := by
      rw [← LinearMap.comp_apply, a0d_comp_a0dpow d, LinearMap.comp_apply, a0dpow_succ,
        LinearMap.comp_apply]
    rw [h]

/-- **The `c`-number substitution for one anti-normal monomial** (FS `thm:Kafz`
term by term): the expectation of `a₀^p (a₀†)^q (lift B)` in a core state `Ψ` equals
the Gaussian integral of the anti-Wick symbol `z^p z̄^q B` against the coherent-state
transform `Φ Ψ`,

`⟪Ψ, a₀^p (a₀†)^q (lift B) Ψ⟫ = ∫_ℂ z^p z̄^q ⟪Φ Ψ z, B (Φ Ψ z)⟫ dν(z)`.

Proof: move `a₀^p` left by `inner_a0pow_a0dpow`, pull the spectator `B` out of the
creation powers by `lift_comm_a0dpow`, apply the Bargmann isometry with spectator
(`bargmann_lift`) which is the case `p = q = 0`, and finally rewrite the
integrand pointwise with `Phi_a0dpow`. -/
theorem Kafz_monomial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (p q : ℕ) (B : E →ₗ[ℂ] E) (Ψ : Work.BoseB4.FockCore E) :
    inner ℂ (Work.BoseB4.Embed E Ψ) (Work.BoseB4.Embed E (Work.BoseB4.monoOp p q B Ψ))
      = ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q * inner ℂ (Work.BoseB4.Phi Ψ z) (B (Work.BoseB4.Phi Ψ z))
          ∂(Work.BoseB4.gauss) := by
  -- Unfold the monomial: `monoOp p q B Ψ = a0^p ((a0†)^q (lift B Ψ))`.
  rw [monoOp, LinearMap.comp_apply, LinearMap.comp_apply]
  -- Move `a0^p` to the left slot of the inner product as `(a0†)^p`.
  rw [inner_a0pow_a0dpow p Ψ (a0dpow q (lift B Ψ))]
  -- Move the spectator operator `B` outside the creation powers.
  rw [← lift_comm_a0dpow B q Ψ]
  -- The case `p = q = 0`: the Bargmann isometry with a spectator operator.
  rw [bargmann_lift B (a0dpow p Ψ) (a0dpow q Ψ)]
  -- Rewrite the integrand pointwise: `Φ (a0†)^k Ψ = z̄^k • Φ Ψ`, and the constant
  -- `z̄^p` in the *first* slot of the (conjugate-linear) inner product becomes `z^p`.
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [Phi_a0dpow p Ψ z, Phi_a0dpow q Ψ z, map_smul, inner_smul_left, inner_smul_right]
  rw [show starRingEnd ℂ ((starRingEnd ℂ z) ^ p) = z ^ p from by simp]
  ring

end Work.BoseB4
