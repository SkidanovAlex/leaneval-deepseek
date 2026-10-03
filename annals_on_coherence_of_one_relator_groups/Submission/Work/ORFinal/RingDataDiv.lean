/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ring half without the `IsMulTorsionFree` field: `RingDataDiv`

`Work.ORFinal.RingData` (and the lead's `Work.ORAssembly.RingInputs`) require the finite-index
subgroup `G'` to be `IsMulTorsionFree` — every power map injective.  No delivered node produces
that: node N4 produces a subgroup that is *torsion free* and *locally indicable*
(`Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable`), and the two notions
differ (the Klein bottle group `BS(1,-1) = ⟨a,t | t a t⁻¹ a⟩` is torsion free and locally
indicable, yet `(a t)² = t²`).

The only place where `IsMulTorsionFree G'` is consumed in the ring half is the Artinianity of
`S = D(G)`: `Work.ORLinnell.isSemisimpleRing_S` builds the division-ring structure on `D G'` from
`L.division_of_torsionFree G' ‹IsMulTorsionFree G'›`.  Its *proof* only needs the conclusion of
that field — `∀ x ∈ D G', x ≠ 0 → IsUnit x` — which is exactly what **(I4)** of the paper states
for a *torsion-free* subgroup, and what node N6 supplies for a *locally indicable* one
(`Work.ORFinal.DivLoc`, `Work.ORHughesFree.hughesFree_exists_locallyIndicable`).

`Work.ORFinal.RingDataDiv` therefore replaces the field `torsionFree_G' : IsMulTorsionFree G'` by
the field `hdiv_G' : ∀ x ∈ D G', x ≠ 0 → IsUnit x`, which is supplied by node N4 + node N6:
N4 gives `LocallyIndicable G'` and `Work.ORFinal.DivLoc` gives the division-ring property of
`D G'`.

* `Work.ORFinal.RingDataDiv.ofEnvelope` — the constructor from the M1 bridge;
* `Work.ORFinal.ringCoherent_of_ringDataDiv` — the ring half of Theorem 1.1 for a `RingDataDiv`,
  given the semisimplicity of `S = D(G)` (which
  `Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn` supplies from `hdiv_G'`, the
  replacement of the `IsMulTorsionFree`-based `Work.ORLinnell.isSemisimpleRing_S`).
-/
import Submission.Work.ORFinal.RingData
import Submission.Work.ORFinal.AnalyticInput
import Submission.Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORFinal

open Work.ORAssembly

/-- **The ring half's per-presentation input, with the torsion requirement of the subgroup replaced
by the division-ring property of its closure.**

Every field is a genuine input: `U`, `datum` (nodes N5/N6/N7), `G'` normal of finite index (node
N4), `hdiv_G'` (nodes N4 + N6, see the module docstring), `hgl` (node N3) and `hTor` (node N9). -/
structure RingDataDiv (K : Type u) [Field K] [CharZero K] (G : Type u) [Group G] where
  /-- the ambient ring `U(G)` -/
  U : Type u
  [ringU : Ring U]
  [nontrivialU : Nontrivial U]
  [algebraU : Algebra K U]
  /-- the Linnell datum: the division closures `D H` of `K[H]` in `U(G)` -/
  datum : Work.ORLinnell.LinnellDatum K G U
  /-- node N4: a normal finite-index subgroup -/
  G' : Subgroup G
  normal_G' : G'.Normal
  finiteIndex_G' : G'.FiniteIndex
  /-- nodes N4 + N6: the division closure of `K[G']` is a division ring -/
  hdiv_G' : ∀ x : ↥(datum.D G'), x ≠ 0 → IsUnit x
  /-- node N3: `gl.dim K[G] ≤ 2` -/
  hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞)
  /-- node N9: `Tor₂^{K[G]}(D(G), -) = 0` -/
  hTor : Work.ORCoherence.TorTwoVanishes (LinData.toS datum).toRingHom

attribute [instance] RingDataDiv.ringU RingDataDiv.nontrivialU RingDataDiv.algebraU

variable {K : Type u} [Field K] [CharZero K] {G : Type u} [Group G]

namespace RingDataDiv

/-- **Building a `RingDataDiv` from node N5's envelope and node N6's input.**  The `U`/`datum`
fields are those of the M1 bridge `Work.ORBridgeLinnell.linBridgeDataOf E φK hin`; the remaining
fields are nodes N4, N4+N6, N3 and N9. -/
noncomputable def ofEnvelope (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ)
    (hin : Work.ORBridgeLinnell.HughesFreeInput K G E φK)
    (G' : Subgroup G) (hN : G'.Normal) (hfin : G'.FiniteIndex)
    (hdiv : DivOn K E φK G')
    (hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞))
    (hTor : FlatConclAt K E φK hin) : RingDataDiv K G where
  U := (Work.ORBridgeLinnell.linBridgeDataOf E φK hin).U
  ringU := (Work.ORBridgeLinnell.linBridgeDataOf E φK hin).ringU
  nontrivialU := (Work.ORBridgeLinnell.linBridgeDataOf E φK hin).nontrivialU
  algebraU := (Work.ORBridgeLinnell.linBridgeDataOf E φK hin).algebraU
  datum := Work.ORBridgeLinnell.linnellDatumOfEnvelope E φK hin
  G' := G'
  normal_G' := hN
  finiteIndex_G' := hfin
  hdiv_G' := hdiv
  hgl := hgl
  hTor := hTor

end RingDataDiv

/-- **The ring half of Theorem 1.1 for a `RingDataDiv`**: `S = D(G)` is semisimple by
`Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn` applied to `hdiv_G'` — in place of
the `IsMulTorsionFree`-based `Work.ORLinnell.isSemisimpleRing_S` — and JL Corollary 3.3 (node N10)
concludes. -/
theorem ringCoherent_of_ringDataDiv (D : RingDataDiv K G) : Ring.Coherent (MonoidAlgebra K G) := by
  haveI hss : IsSemisimpleRing ↥(D.datum.S) :=
    Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn K G D.U D.datum D.G'
      D.normal_G' D.finiteIndex_G' D.hdiv_G' ⊤
  haveI hArt : IsArtinianRing ↥(LinData.SAlg D.datum) :=
    inferInstanceAs (IsArtinianRing ↥(D.datum.S))
  exact Work.ORCoherence.coherent_of_embeds_semisimple (LinData.toS D.datum).toRingHom
    (Work.ORAssembly.Ring.toS_injective D.datum) D.hgl D.hTor

end Work.ORFinal
