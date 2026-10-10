import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.Defs
import Submission.Work.MotC.TransData
import Submission.Work.MotC.not_algEquiv_twistField
import Submission.Work.MotC.algEquiv_ratFunc_cancel

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RatFunc K_P ≇ RatFunc K_{kP}` (audit node C6 (iii))

The lead's non-vanishing argument at `z = 𝔭_{D_P}` compares the residue field `K_P(t)` of the
component `D_P` with the residue field `K_{kP}(t)` of the component `D_Q` (audit nodes K5, K6), so
it needs the *stable* non-isomorphism `RatFunc K_P ≇ RatFunc K_{kP}`, not only the curve-level
non-isomorphism `K_P ≇ K_{kP}` of node C5.

## Why this is not a formal consequence of C5

The unconditional cancellation `RatFunc F₁ ≅ RatFunc F₂ ⟹ F₁ ≅ F₂` is **false** (it fails for
stably birational, non-birational fields; the `𝕜`-automorphism of `𝕜(t)(X)` with `X ↦ tX` is an
explicit obstruction whenever no such `X`-direction is intrinsic).  What is proved in
`Work.MotC.algEquiv_ratFunc_cancel` is the cancellation *under the hypothesis that the isomorphism
preserves the constants*, and that hypothesis is precisely the geometric input that is missing:

* `C_P × ℙ¹` and `C_{kP} × ℙ¹` are ruled surfaces over the genus-one curves `C_P`, `C_{kP}`, which
  have the *same* Jacobian `E`; so the Albanese cannot separate them, and
* the statement "a birational map of ruled surfaces over a curve of genus `≥ 1` preserves the
  ruling" (equivalently: a `𝕜`-isomorphism of the function fields carries the constants of the base
  curve to the constants of the base curve) is the Castelnuovo / relative-minimal-model input that
  Mathlib does not have.

It is therefore packaged below as the explicit hypothesis `hRuling` — the *only* input besides
node C5 — so that node C6 (iii) is available now and its residual is a named, checkable statement.
(Caveat for whoever proves `hRuling`: in characteristic `p` the uniqueness of the ruling of a ruled
surface over a curve of genus `≥ 1` can fail by the Lang–Néron phenomenon, so the residual should be
examined separately in characteristic `p`.)
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The ruling residual, as a named node.**  `RulingStable 𝕜 A B` is the assertion that *every*
`𝕜`-algebra isomorphism `RatFunc A ≃ₐ[𝕜] RatFunc B` carries the constants `A` of `A(t)` into the
constants `B` of `B(t)`.

For function fields `A`, `B` of curves this is the algebraic content of "a birational map of ruled
surfaces over a curve of genus `≥ 1` preserves the ruling": for `A = K_P`, `B = K_{kP}` the two
surfaces are the ruled surfaces `C_P × ℙ¹` and `C_{kP} × ℙ¹`, whose rulings are onto curves of genus
`1`, and the ruling of such a surface is unique in characteristic `0` (Castelnuovo / relative
minimal models) but is *not* known to be unique in characteristic `p` (Lang–Néron phenomenon); so
`RulingStable 𝕜 K_P K_{kP}` should be treated as a named geometric residual, and its
characteristic-`p` satisfiability needs a separate examination before it is relied on.

`Work.MotC.rulingStable_iff_isEmpty` records that, once the curve-level non-isomorphism `A ≇ B` is
known (node C5), this residual is *equivalent* to the conclusion `RatFunc A ≇ RatFunc B` (node
C6 (iii)): the two halves are C4 (`Work.MotC.algEquiv_ratFunc_cancel`) and C5. -/
def RulingStable (𝕜 A B : Type*) [Field 𝕜] [Field A] [Field B] [Algebra 𝕜 A]
    [Algebra 𝕜 B] : Prop :=
  ∀ θ : RatFunc A ≃ₐ[𝕜] RatFunc B, ∀ a : A,
    ∃ b : B, θ (algebraMap A (RatFunc A) a) = algebraMap B (RatFunc B) b

/-- **Cancellation up to the ruling residual.**  If the fields `A`, `B` are not `𝕜`-isomorphic, and
every `𝕜`-isomorphism `RatFunc A ≃ₐ[𝕜] RatFunc B` preserves the constants, then `RatFunc A` and
`RatFunc B` are not `𝕜`-isomorphic. -/
theorem not_algEquiv_ratFunc_of_ruling {A B : Type*} [Field A] [Field B]
    [Algebra 𝕜 A] [Algebra 𝕜 B]
    (hAB : IsEmpty (A ≃ₐ[𝕜] B))
    (hRuling : RulingStable 𝕜 A B) :
    IsEmpty (RatFunc A ≃ₐ[𝕜] RatFunc B) := by
  rw [isEmpty_iff]
  rintro θ
  obtain ⟨e⟩ := algEquiv_ratFunc_cancel θ (hRuling θ)
  exact hAB.false e

/-- **The ruling residual is exactly the missing half of node C6 (iii).**  Given that `A` and `B` are
not `𝕜`-isomorphic (node C5, `Work.MotC.not_algEquiv_twistField` for the twists), `RulingStable 𝕜 A B`
holds if and only if `RatFunc A` and `RatFunc B` are not `𝕜`-isomorphic (node C6 (iii)).  So the
residual is not a weaker input: it *is* the statement, and it is precisely the geometric half (the
ruled-surface input). -/
theorem rulingStable_iff_isEmpty {A B : Type*} [Field A] [Field B]
    [Algebra 𝕜 A] [Algebra 𝕜 B] (hAB : IsEmpty (A ≃ₐ[𝕜] B)) :
    RulingStable 𝕜 A B ↔ IsEmpty (RatFunc A ≃ₐ[𝕜] RatFunc B) :=
  ⟨not_algEquiv_ratFunc_of_ruling hAB,
    fun h θ _ => (h.false θ).elim⟩

variable [DecidableEq 𝕜]

/-- **Audit node C6 (iii).**  The residue fields `K_P(t) = RatFunc (twistField D α_P)` and
`K_{kP}(t) = RatFunc (twistField D α_{kP})` attached to the components `D_P` and `D_Q` of the
quadro-cubic link are not `𝕜`-isomorphic, for `k = 2` (the class of `D_Q`) and `k = 3`.

The hypotheses are: the translation-pullback data `TD` (node C2), the classification `hC2` of the
`L`-algebra automorphisms of `L(E)` (node C2), the pointlessness `hP : P ∉ (σ-1)E(L)`, and the
ruling residual `hRuling` described in the module docstring (the ruled-surface input, absent from
Mathlib).  The curve-level non-isomorphism is `Work.MotC.not_algEquiv_twistField` (node C5);
the passage from it to the stable statement is `Work.MotC.not_algEquiv_ratFunc_of_ruling`, i.e.
`Work.MotC.algEquiv_ratFunc_cancel` (node C4). -/
theorem not_algEquiv_ratFunc_twistField (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (TD : TransData D)
    (hC2 : ∀ Θ : WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[D.ext.L]
        WeierstrassCurve.Affine.FunctionField (baseCurve D),
      ∃ (R : WeierstrassCurve.Affine.Point (baseCurve D)) (ε : ℤˣ),
        Θ = (TD.neg ^ (ε : ℤ)).trans (TD.τ R))
    (hP : ¬ ∃ R : WeierstrassCurve.Affine.Point (baseCurve D),
      galPoint D R - R = markPoint D)
    (k : ℕ) (hk : k = 2 ∨ k = 3)
    (hRuling : RulingStable 𝕜 ↥(twistField D (twistAut D (TD.τ (markPoint D))))
      ↥(twistField D (twistAut D (TD.τ (k • markPoint D))))) :
    IsEmpty (RatFunc ↥(twistField D (twistAut D (TD.τ (markPoint D)))) ≃ₐ[𝕜]
      RatFunc ↥(twistField D (twistAut D (TD.τ (k • markPoint D))))) :=
  not_algEquiv_ratFunc_of_ruling (not_algEquiv_twistField D TD hC2 hP k hk) hRuling

end

end Work.MotC
