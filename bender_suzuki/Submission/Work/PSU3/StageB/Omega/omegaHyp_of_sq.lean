/-
# `Work.PSU3.StageB.Omega.omegaHyp_of_sq`

The final step of Peterfalvi II, Ch. VII §2 (19)/(20)+Prop. at the level of a single
element: if `ω ∈ Q ∖ Q₀` is a square root of an element of `Q₀` in the sense that

* `f (ω) = (ω · zc α)^ζ`  (`hf`) and
* `ω * ω = zc α`           (`hsq`),

and if moreover `h (ω) ∈ W` (`hh`), then `ω` already satisfies `OmegaHyp`:

`t ω t = g(ω) · h(ω) · t · (ζ⁻¹ ω⁻¹ ζ)`.

Indeed, the defining relation of the canonical maps (`canon_spec`) gives
`t ω t = g(ω) h(ω) t f(ω)`, and the two hypotheses on `ω` force the auxiliary identity
`f (ω) = ζ⁻¹ ω⁻¹ ζ`: since `zc α` is an involution and `ω · ω = zc α`, one has
`ω⁻¹ = ω · zc α`, so `(ω zc α)^ζ = ζ⁻¹ ω ζ · zc α = ζ⁻¹ ω⁻¹ ζ`.

This is the input the `Prop.` of Ch. VII §2 consumes: the element `ω` produced by
(19)/(20) differs from an `OmegaHyp`-element only in that its canonical data are not
*known*, and this lemma converts those data into the `OmegaHyp` shape.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.ThetaOmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Auxiliary identities -/

/-- `zc u` (for `u ∈ F*`) lies in `Q₀`, hence is an involution. -/
lemma zcQF_mul_self (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    (zcQF fr u : G) * (zcQF fr u : G) = 1 :=
  Q0_mul_self fr (fr.zc_mem (fval u) u.2)

/-- If `ω * ω = zc α` with `α ∈ F*`, then `ω⁻¹ = ω * zc α` (both sides are `ω³ = ω⁻¹`,
because `ω⁴ = (ω²)² = (zc α)² = 1`). -/
lemma inv_eq_mul_zcQF_of_sq (fr : CoarseFrame H Q t n) {ω : ↥Q} {α : ↥(FX n)}
    (hsq : ω * ω = zcQF fr α) :
    (ω : G)⁻¹ = (ω : G) * (zcQF fr α : G) := by
  have hωsq : (ω : G) * (ω : G) = (zcQF fr α : G) := by
    have h := congrArg (fun z : ↥Q => (z : G)) hsq
    simpa using h
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hωsq, zcQF_mul_self fr α]

/-- **(19)/(20) at a single element**: if `f (ω) = (ω · zc α)^ζ` and `ω² = zc α`, then
`f (ω) = ζ⁻¹ ω⁻¹ ζ`. -/
lemma fcan_eq_zeta_inv_of_sq (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} {α : ↥(FX n)}
    (hf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    (hsq : ω * ω = zcQF fr α) :
    (fcan hS.split ω : G) = (fr.ζ : G)⁻¹ * (ω : G)⁻¹ * (fr.ζ : G) := by
  have h1 : (fcan hS.split ω : G) =
      (qconj hS.split (zetaD fr) (ω * zcQF fr α) : G) := by rw [hf]
  rw [h1, qconj_coe]
  have h2 : (zetaD fr : G) = (fr.ζ : G) := rfl
  rw [h2, Subgroup.coe_mul, inv_eq_mul_zcQF_of_sq fr hsq]

/-! ## The main lemma -/

theorem omegaHyp_of_sq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    (hsq : ω * ω = Work.PSU3.StageB.zcQF fr α)
    (hh : (Work.PSU3.StageB.hcan hS.split ω : G) ∈ Work.ThmF.W H t) :
    Work.PSU3.OmegaHyp fr (ω : G) := by
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hfeq : (fcan hS.split ω : G) = (fr.ζ : G)⁻¹ * (ω : G)⁻¹ * (fr.ζ : G) :=
    fcan_eq_zeta_inv_of_sq hS fr hf hsq
  refine ⟨ω.2, hω, (gcan hS.split ω : G), (gcan hS.split ω).2,
    (hcan hS.split ω : G), hh, ?_⟩
  rw [canon_spec hS.split hω1, hfeq]

end Work.PSU3.StageB.Omega
