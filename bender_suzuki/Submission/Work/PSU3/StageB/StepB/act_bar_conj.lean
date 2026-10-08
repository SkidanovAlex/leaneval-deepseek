/-
# `Work.PSU3.StageB.StepB.act_bar_conj` — the scalar-equivariance of the `D`-action on `Q/Q₀`

The frame interface gives the action of `D = twoPoint H t` on `Q/Q₀ ≅ E n` **only on
`KW`** (`fr.act_bar`: `bar (d⁻¹ x d) = κ d · bar x` for `d : fr.KW`).  Everything in
Peterfalvi's Ch. VII §2 Proposition and in §4 ("Setting for the computation", l. 463–468:
`(c x)^η = c^μ x^η`) needs that this action is *equivariant* with respect to the
`κ (KW)`-scalar action for **all** of `D`:

  `bar (d⁻¹ (w⁻¹ x w) d) = κ (d⁻¹ w d) · bar (d⁻¹ x d)`      (`w ∈ fr.KW`, `d ∈ D`),

i.e. `(c·x)^d = c^d · x^d`.  The point is that the *conjugated* scalar `d⁻¹ w d` is again an
element of `KW` (i.e. `KW ⊴ D`) — for a frame whose `ζ` generates `W` this is
`Work.PSU3.StageB.StepB.conj_mem_KW_of_mem_twoPoint`, proved from `ChIIFourProp` — so that
`fr.act_bar` applies to it.  No semilinearity input (e.g. `ThmF.ChV12.AppV_semilinear`) is
needed: the equivariance is a rewriting consequence of `act_bar` alone.

Consequences recorded here: `D` normalises the `KW`-action on `Q` (`qconj_kact`), hence maps
`KW`-orbits to `KW`-orbits, i.e. permutes the `KW`-orbits on `(Q/Q₀)^#`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.Frame

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

namespace Work.PSU3.StageB.StepB

open Work.ThmF
open Work.PSU3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- **`D` normalises the `KW`-action on `Q`**: `qconj` and `kact` commute in the sense that
`d⁻¹ (w⁻¹ x w) d = e⁻¹ (d⁻¹ x d) e` with `e = d⁻¹ w d ∈ KW`.  Purely group-theoretic (the
normality input `hN` is what exhibits `e` as an element of `fr.KW`). -/
theorem qconj_kact (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hN : ∀ d : ↥(twoPoint H t), ∀ w : fr.KW, (d : G)⁻¹ * (w : G) * (d : G) ∈ fr.KW)
    (d : ↥(twoPoint H t)) (w : fr.KW) (x : ↥Q) :
    qconj hS.split d (kact hS fr w x) =
      kact hS fr ⟨(d : G)⁻¹ * (w : G) * (d : G), hN d w⟩ (qconj hS.split d x) := by
  apply Subtype.ext
  simp only [qconj_coe, kact_coe, Subgroup.coe_inv, Subgroup.coe_mul]
  group

/-- **The scalar-equivariance of the `D`-action on `Q/Q₀`** (Peterfalvi Ch. VII §4,
`(c x)^η = c^μ x^η`): for `d ∈ D` and `w ∈ KW`, the `bar`-classes satisfy

  `bar (d⁻¹ (w⁻¹ x w) d) = κ (d⁻¹ w d) · bar (d⁻¹ x d)`.

In other words `ρ_d (κ w · bar x) = κ (d⁻¹ w d) · ρ_d (bar x)`: the `D`-action is
semilinear with the scalar twist induced by conjugation on `κ (KW)`. -/
theorem act_bar_conj (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hN : ∀ d : ↥(twoPoint H t), ∀ w : fr.KW, (d : G)⁻¹ * (w : G) * (d : G) ∈ fr.KW)
    (d : ↥(twoPoint H t)) (w : fr.KW) (x : ↥Q) :
    fr.bar (qconj hS.split d (kact hS fr w x)) =
      Multiplicative.ofAdd ((fr.κ ⟨(d : G)⁻¹ * (w : G) * (d : G), hN d w⟩ : E n) *
        Multiplicative.toAdd (fr.bar (qconj hS.split d x))) := by
  rw [qconj_kact hS fr hN d w x]
  apply Multiplicative.toAdd.injective
  rw [kact_bar, toAdd_ofAdd]

end Work.PSU3.StageB.StepB
