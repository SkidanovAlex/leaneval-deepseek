/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The hypothesis interfaces of the M1 bridge

This file records the two *analytic* inputs which the bridge from node N5 to node N7
(`Submission/Work/ORBridgeLinnell/Basic.lean`, `Bridge.lean`) cannot derive from node N5's
envelope interface, and whose exact form is therefore isolated here, together with the packaged
output (`LinBridgeData`) that the final assembly `Submission/Work/ORAssembly/` consumes.

## What is *not* derivable from node N5

The `Work.ORLinnell.LinnellDatum` interface has twelve fields.  Everything that concerns the
*definition* of `D H` inside the ambient `*-regular` ring `U(G)` is proved in `Bridge.lean`
from node N5's `StarRegularEnvelope G`:

* `gen`, `gen_injective`, `D`, `gen_mem`, `algebraMap_mem`, `isDivisionClosed`, `minimal`
  (division closure),
* `independence`, `independence'` (Linnell independence, from `EnvelopeInclusion.linnell`),
* `conjugation` (conjugation by the units `gen g`).

The remaining fields are exactly the content of node **N6** (the JZLA20 engine
`Work.ORHughesFree.hughesFree_exists`) together with Linnell's Ore field of fractions lemma:

* `division_of_torsionFree` — **(I4)**: for a torsion free subgroup `H ≤ G` the division closure
  `D H = D_{K[H]}(U(G))` is a *division ring*.  In the literature this is the Hughes-free / Atiyah
  statement: for `H` torsion free and locally indicable, the von Neumann rank function of `H` is
  Hughes-free (JZLA20, Proposition 3.11) and hence `D(H)` is a division ring
  (JZLA20, Theorem 6.1 / Corollary 6.3) — the engine of node N6.  Note that node N5's envelope
  does *not* carry Hughes-freeness of `rk` as a field (only node N6's own packaging
  `Work.ORHughesFree.StarRegularEnvelope` does), and that the analytic statement "the von Neumann
  rank is Hughes-free" is itself part of the input, so this field genuinely cannot be recovered
  from `Work.ORVonNeumann.StarRegularEnvelope`.
* `ore_field_frac` — **(I4′b)**: for `N ≤ Γ` with `Γ` torsion free and `Γ/N ≅ ℤ`, every element of
  `D Γ` is a right quotient `a * t⁻¹` of elements of the subring `⟨D N ∪ Γ⟩`.  This is Linnell's
  lemma that `D(Γ)` is the classical (Ore) ring of quotients of the twisted Laurent polynomial
  ring `D(N)[t^{±1};τ]` (see the header of `Submission/Work/ORLinnell/Basic.lean`); it is consumed
  by node N7's `Work.ORLinnell.CommonDenominators.exists_common_denominator`.

The companion field **(I4′a)** `ore_field_unit` *is* derived here (see `Bridge.lean`): once `D Γ`
is a division ring, every nonzero element of `⟨D N ∪ Γ⟩ ⊆ D Γ` is a unit with inverse in `D Γ`.

## The packaged output

`LinBridgeData K G` collects exactly the `U` and `datum` fields (together with `hinj`, which the
assembly proves separately as `Work.ORAssembly.Ring.toS_injective` but whose input — the datum —
is what this area produces) of `Work.ORAssembly.RingInputs`.
-/
import Mathlib
import Submission.Work.ORBridgeLinnell.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORBridgeLinnell

open Work.ORVonNeumann

variable {G : Type*} [Group G] {K : Type*} [Field K]

/-- The `K`-algebra structure on `U(G)` induced by a field embedding `K →+* ℂ`; use it as
`letI := kAlgebra E φK`.  It is definitionally `Algebra.compHom`, so that
`algebraMap K E.U k = algebraMap ℂ E.U (φK k)` holds by `rfl`. -/
noncomputable abbrev kAlgebra (E : StarRegularEnvelope G) (φK : K →+* ℂ) : Algebra K E.U :=
  Algebra.compHom E.U φK

/-- The `K`-algebra structure on `U(G)` is the one induced by `φK`: this is the compatibility
hypothesis `hφK` used throughout `Bridge.lean`, true by `rfl` for `kAlgebra`. -/
theorem kAlgebra_compat (E : StarRegularEnvelope G) (φK : K →+* ℂ) (k : K) :
    letI := kAlgebra E φK
    algebraMap K E.U k = algebraMap ℂ E.U (φK k) := rfl

/-- **The inputs still owed by node N6 for the M1 bridge** (plus Linnell's Ore field statement),
stated for the canonical `K`-algebra structure `kAlgebra E φK` on `U(G)`.

The field `div_of_torsionFree` is (I4) of `Work.ORLinnell.LinnellDatum`; `ore_field_frac` is
(I4′b).  Nothing else of the Linnell datum is assumed here. -/
structure HughesFreeInput (K : Type*) [Field K] (G : Type*) [Group G]
    (E : StarRegularEnvelope G) (φK : K →+* ℂ) where
  /-- **(I4)**: for a torsion free subgroup, `D H` is a division ring (Hughes-free / Atiyah;
  node N6). -/
  div_of_torsionFree : ∀ H : Subgroup G, IsMulTorsionFree H →
    letI := kAlgebra E φK
    ∀ x : ↥(D E φK H), x ≠ 0 → IsUnit x
  /-- **(I4′b)**: the Ore field of fractions statement for an extension by `ℤ` (Linnell's lemma;
  the torsion free piece of node N7's L3). -/
  ore_field_frac : ∀ (N Γ : Subgroup G), N ≤ Γ → IsMulTorsionFree Γ →
    letI := kAlgebra E φK
    Work.ORLinnell.IsExtensionByZ N Γ →
    ∀ e ∈ (D E φK Γ : Set E.U), ∃ a ∈ Subring.closure (((D E φK N : Subring E.U) : Set E.U) ∪
        Set.range (fun γ : Γ => (gen E (γ : G) : E.U))),
      ∃ t ∈ Subring.closure (((D E φK N : Subring E.U) : Set E.U) ∪
        Set.range (fun γ : Γ => (gen E (γ : G) : E.U))), t ≠ 0 ∧ e * t = a

/-- **The `U`/`datum` output of the M1 bridge**, in the exact shape of the corresponding fields of
`Work.ORAssembly.RingInputs`: the ambient ring `U = U(G)`, its instances, and the Linnell datum
`D_{K[G]}(U(G))`. A caller builds a `RingInputs` from it with `U := D.U`, `datum := D.datum`. -/
structure LinBridgeData (K : Type*) [Field K] (G : Type*) [Group G] where
  /-- the ambient ring `U(G)` -/
  U : Type*
  [ringU : Ring U]
  [nontrivialU : Nontrivial U]
  [algebraU : Algebra K U]
  /-- the Linnell datum `D_{K[G]}(U(G))` -/
  datum : Work.ORLinnell.LinnellDatum K G U

attribute [instance] LinBridgeData.ringU LinBridgeData.nontrivialU LinBridgeData.algebraU

end Work.ORBridgeLinnell
