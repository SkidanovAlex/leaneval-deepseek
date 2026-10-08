/-
# Stage B, node B1: `DFpfBar` against the semilinear action of `V = C_D(t)` on `Q/Q₀`

Peterfalvi II Ch. V §1 Prop. 3 (`Work.ThmF.ChV12.prop3`, **in the tree, hole-free**) says that
`V = centD H t` acts on `Q₀ = Q0sub H ≅ 𝔽_q` by **field automorphisms**, with kernel
`W = C_V(K)`: there is `ρ : V →* (𝔽_q ≃+* 𝔽_q)` with `ρ.ker = W.subgroupOf V`.  Its engine is
`Work.ThmF.ChV12.AppV_semilinear` (also in the tree): a group acting compatibly with a scalar
action `K ≅ Fˣ` and fixing one point acts by *ring* automorphisms.

The same statement for the action of `V` on `Q/Q₀ ≅ 𝔽_{q²}` would close node B1 outright: if
every `η ∈ V ∖ W` acted on `Q/Q₀` by a ring automorphism, then `η` would fix the class of a lift
of `1 ∈ 𝔽_{q²}` and hence have a fixed point on `(Q/Q₀)^#`, contradicting `DFpfBar`; so `V ≤ W`,
and then `D = K·V = K·W = KW`, so that B1 follows from `Omega.exists_omega_of_fpf_of_D_eq_KW`
(see `Work.PSU3.StageB.exists_omega_of_fpf_rebuilt_of_V_eq_W` in the parent file).

This module records the part of that argument which is unconditional:

* `not_dfpfBar_of_fixed_lift` — a *single* `η ∈ V ∖ W` that fixes the `Q₀`-class of an element of
  `Q ∖ Q₀` already violates `DFpfBar`.  (No semilinearity is needed for this step: `DFpfBar`
  forbids *elementwise* fixed classes of every `1 ≠ d ∈ D`, and such an `η` is one.)
* `centD_le_W_of_dfpfBar_of_fixed_lift` — consequently, `DFpfBar` together with "every
  `η ∈ V ∖ W` fixes the class of some lift of `1`" forces `V ≤ W`.

The hypothesis of the second statement is exactly the missing half of Ch. V §1 Prop. 3: the
`V`-action on `Q/Q₀` being by field automorphisms (the source's "`V/W` is a cyclic group of field
automorphisms", Ch. VII §2, standing hypotheses).  Note that `AppV_semilinear` *can* be applied
to the `Q/Q₀`-action as soon as one `V`-fixed class is known — and knowing one such class is
precisely what `DFpfBar` denies, so this route cannot be closed by `AppV_semilinear` alone.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageB.StepB.W_normal_twoPoint
import Submission.Work.PSU3.StageB.StepB.conj_mem_KW_of_mem_twoPoint
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

namespace Work.PSU3.StageB.StepB

open Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- **A single fixed class in `V ∖ W` contradicts `DFpfBar`.**

If `η ∈ centD H t` fixes the `Q₀`-class of an element `s ∈ Q ∖ Q₀` (i.e.
`η⁻¹ s η s⁻¹ ∈ fr.Q0`), then, since `η ∈ D` is nontrivial (`η ∉ W`), `DFpfBar` — "`D` acts
fixed-point-freely on `(Q/Q₀)^#`" — fails.  Only the identification `fr.Q0 = Q0sub H` of the
frame with the intrinsic `Q₀ = ⟨Inv H⟩` is used. -/
theorem not_dfpfBar_of_fixed_lift (hS : Work.PSU3.PSU3Hyp H Q t)
    (fr : Work.PSU3.CoarseFrame H Q t n) {η : G} (hηV : η ∈ centD H t) (hηW : η ∉ W H t)
    {s : ↥Q} (hs0 : (s : G) ∉ fr.Q0)
    (hsfix : ((qconj hS.split
        (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ : ↥(twoPoint H t)) s * s⁻¹ : ↥Q) : G)
        ∈ fr.Q0) :
    ¬ Work.PSU3.DFpfBar H Q t := by
  intro hfpf
  have hηD : η ∈ twoPoint H t := Work.ThmF.centD_le_twoPoint (H := H) t hηV
  have hη1 : η ≠ 1 := fun h => hηW (h ▸ (W H t).one_mem)
  have hsQ : (s : G) ∈ Q := s.2
  have hsQ0 : (s : G) ∉ Work.ThmF.Q0sub H := by
    rw [← frameQ0_eq_Q0sub hS fr]; exact hs0
  have hbad := hfpf η hηD hη1 (s : G) hsQ hsQ0
  apply hbad
  have hz : ((qconj hS.split (⟨η, hηD⟩ : ↥(twoPoint H t)) s * s⁻¹ : ↥Q) : G)
      ∈ Work.ThmF.Q0sub H := by
    rw [← frameQ0_eq_Q0sub hS fr]; exact hsfix
  simpa only [qconj_coe, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] using hz

/-- **`DFpfBar` forces `V ≤ W` once every `η ∈ V ∖ W` fixes the `Q₀`-class of some lift.**

The hypothesis is the concrete form of "the `V`-action on `Q/Q₀` is by field automorphisms"
(the last piece of Ch. V §1 Prop. 3 not available in the tree): each `η ∈ V ∖ W` must have a
fixed class on `(Q/Q₀)^#`.  Under `DFpfBar` no such `η` exists, so `V = W`. -/
theorem centD_le_W_of_dfpfBar_of_fixed_lift (hS : Work.PSU3.PSU3Hyp H Q t)
    (fr : Work.PSU3.CoarseFrame H Q t n)
    (hfix : ∀ η : G, (hηV : η ∈ centD H t) → η ∉ W H t →
      ∃ s : ↥Q, (s : G) ∉ fr.Q0 ∧
        ((qconj hS.split
            (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ : ↥(twoPoint H t)) s * s⁻¹ : ↥Q) : G)
          ∈ fr.Q0)
    (hfpf : Work.PSU3.DFpfBar H Q t) :
    centD H t ≤ W H t := by
  intro v hv
  by_contra hvW
  obtain ⟨s, hs0, hsf⟩ := hfix v hv hvW
  exact not_dfpfBar_of_fixed_lift hS fr hv hvW hs0 hsf hfpf

end Work.PSU3.StageB.StepB
