/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# [JZLA20, Proposition 3.11] as an explicit hypothesis, in three vocabularies

The analytic input of the JZLA20 engine's induction step (the hypothesis `hHF` of
`Work.ORHughesFree.Section6.thm61Step_nonempty`) is [JZLA20, Proposition 3.11] / [Jaikin, *The
base change in the Atiyah and the Lück approximation conjectures*, GAFA 29 (2019), Corollary
12.2]: for a locally indicable group, the von Neumann rank `rk_G` restricted to `K[G]` is
Hughes-free.  In the rank-free form of the lead's audit (`OR_REMAINING_LEAD.md` §3.1, H3) it reads:
for `N ⊴ H ≤ G` with `H = N ⋊ ⟨t⟩`, and `A` a matrix over the `∗`-regular closure of the image of
`K[N]`, the matrix `1 + A·ι(t)` is invertible.

This file records the three vocabularies in which the statement is needed, and how they are
related.  Only `Prop311On` (the `∗`-regular closure vocabulary) is consumed by the engine; the
other two are the forms in which node ORP311 states its output.

* `Work.ORDivLoc.Prop311OnComplex G` — the pure node N5 vocabulary: `φ = ι` is the structure map
  of `U(G)`, over `ℂ`, and the identity `1 + A·ι(t)` is a unit of `Mat_n(U(G))`;
* `Work.ORDivLoc.Prop311OnToUK K G φK` — the same over an arbitrary coefficient field `K` with
  `φK : K →+* ℂ`;
* `Work.ORDivLoc.Prop311On K G φK` — the engine's vocabulary: the same statement for the structure
  map `K[H] →+* V_H` into the `∗`-regular closure `V_H ⊆ U(G)` of the image of `K[H]`.

The conversions `Prop311OnComplex → Prop311OnToUK → Prop311On` are
`Work.ORDivLoc.Closure.isHughesFreeEnv_toUK_of_complex` and
`Work.ORDivLoc.Closure.isHughesFreeEnv_starClosureCod`.
-/
import Submission.Work.ORDivLoc.Closure.isHughesFreeEnv_starClosureCod
import Submission.Work.ORDivLoc.Main
import Submission.Work.ORHughesFree.Section6.HughesFreeEnv

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORDivLoc

/-- **[JZLA20, Proposition 3.11] in the vocabulary of `U(G)` over `ℂ`**: for every locally
indicable `H ≤ G`, the structure map `ℂ[H] →+* U(G)` satisfies the rank-free Hughes-freeness
condition `Work.ORHughesFree.IsHughesFreeEnv`.  This is the statement node ORP311 proves. -/
def Prop311OnComplex (G : Type) [Group G] [Countable G] : Prop :=
  ∀ H : Subgroup G, Work.ORLocInd.Group.LocallyIndicable H →
    Work.ORHughesFree.IsHughesFreeEnv
      (Work.ORBridgeLinnell.toUK (Work.ORBridgeLinnell.countableEnvelope G) (RingHom.id ℂ)
        H).toRingHom

/-- **[JZLA20, Proposition 3.11] at the `∗`-regular closure over `ℂ`**: the exact form of the
hypothesis `hHF` of the engine at `(↥H, V_ℂ, starClosureCod …)` with `K = ℂ`.  It is obtained from
`Work.ORDivLoc.Prop311OnComplex` by `Work.ORDivLoc.prop311OnComplexClosure_of_complex`. -/
def Prop311OnComplexClosure (G : Type) [Group G] [Countable G] : Prop :=
  ∀ H : Subgroup G, Work.ORLocInd.Group.LocallyIndicable H →
    Work.ORHughesFree.IsHughesFreeEnv
      (starClosureCod (Work.ORBridgeLinnell.countableEnvelope G) (RingHom.id ℂ) H)

/-- **[JZLA20, Proposition 3.11] in the vocabulary of `U(G)` over a field `K` with a fixed
embedding `φK : K →+* ℂ`.** -/
def Prop311OnToUK (K : Type) [Field K] (G : Type) [Group G] [Countable G] (φK : K →+* ℂ) : Prop :=
  letI := Work.ORBridgeLinnell.kAlgebra (Work.ORBridgeLinnell.countableEnvelope G) φK
  ∀ H : Subgroup G, Work.ORLocInd.Group.LocallyIndicable H →
    Work.ORHughesFree.IsHughesFreeEnv
      (Work.ORBridgeLinnell.toUK (Work.ORBridgeLinnell.countableEnvelope G) φK H).toRingHom

/-- **[JZLA20, Proposition 3.11] in the vocabulary of the `∗`-regular closure `V_H ⊆ U(G)`**,
i.e. the exact form of the hypothesis `hHF` of
`Work.ORHughesFree.Section6.thm61Step_nonempty` at `(↥H, V_H, starClosureCod …)`. -/
def Prop311On (K : Type) [Field K] (G : Type) [Group G] [Countable G] (φK : K →+* ℂ) : Prop :=
  letI := Work.ORBridgeLinnell.kAlgebra (Work.ORBridgeLinnell.countableEnvelope G) φK
  ∀ H : Subgroup G, Work.ORLocInd.Group.LocallyIndicable H →
    Work.ORHughesFree.IsHughesFreeEnv
      (starClosureCod (Work.ORBridgeLinnell.countableEnvelope G) φK H)

/-- **The `∗`-regular-closure vocabulary at `ℂ` follows from the `U(G)` vocabulary at `ℂ`**, by
`Work.ORDivLoc.Closure.isHughesFreeEnv_starClosureCod`. -/
theorem prop311OnComplexClosure_of_complex {G : Type} [Group G] [Countable G]
    (h : Prop311OnComplex G) : Prop311OnComplexClosure G := by
  intro H hLI
  exact Closure.isHughesFreeEnv_starClosureCod (Work.ORBridgeLinnell.countableEnvelope G)
    (RingHom.id ℂ) H (h H hLI)

/-- **The `∗`-regular-closure vocabulary follows from the `U(G)` vocabulary** (the vocabulary
conversion of the engine's hypothesis `hHF`), by
`Work.ORDivLoc.Closure.isHughesFreeEnv_starClosureCod`. -/
theorem prop311On_of_toUK {K : Type} [Field K] {G : Type} [Group G] [Countable G]
    (φK : K →+* ℂ) (h : Prop311OnToUK K G φK) : Prop311On K G φK := by
  letI := Work.ORBridgeLinnell.kAlgebra (Work.ORBridgeLinnell.countableEnvelope G) φK
  intro H hLI
  exact Closure.isHughesFreeEnv_starClosureCod _ φK H (h H hLI)

end Work.ORDivLoc
