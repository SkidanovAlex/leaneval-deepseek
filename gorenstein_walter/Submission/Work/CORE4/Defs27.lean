/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — design pass 27: the §4 (12) amalgam count and its `L₂(q)` input

Thin re-export of the lead's design file `Submission/Work/_design_gw/Core27.lean`
(namespace `Work.GW2.C27`), which defines and proves:

* `Work.GW2.C27.L2pLocalProp` — the NEW single-copy `L₂(q)` input (Dickson-type, no fusion data):
  for `E ≅ L₂(r^e)`, `T ≤ H ≤ E` of prime order `p ≠ 2, r` with `p² ∤ |H|` and `N_H(T) ≤ C(T)`,
  either `T` is the only order-`p` subgroup of `H`, or `H` contains a four-group, or `H ≤ N(R)` for
  a Sylow `r`-subgroup `R ≤ E` and every order-`p` subgroup of `H` is a `R ∩ H`-conjugate of `T`.
* `Work.GW2.C27.CopyLocalProp` — the same statement transported to the internal direct product
  `W₀ = P₀ × E₀` with the diagonal `X₁ ≤ P₀ ⊔ T₀`.
* `Work.GW2.C27.FourCentProp I` — the context fact `C_G(V) ≤ M` for four-groups `V ≤ E(M)`.
* `Work.GW2.C27.PerYProp I`, `PerZProp I`, `WitCardProp I`, `AmalgamCtx`,
  `amalgamSII`, `amalgamWit` — the objects of Bender p. 227.
* `Work.GW2.C27.PerXAmalgamCountProp I` — the statement of `Counting.PerXAmalgamCount`.
* `Work.GW2.C27.TrichCoreProp` (pure `p`-group), `TrichCsProp I`, `TrichCPProp I`,
  `EightTrich9Prop I` — the §4 (8) trichotomy of area CORE4 (`CORE4/EightTrich9.lean`).

PROVED there (`#print axioms` = `[propext, Classical.choice, Quot.sound]`):
`Work.GW2.C27.witCard`, `Work.GW2.C27.perXAmalgamCount_of_leaves`,
`Work.GW2.C27.perXAmalgamCount_of_design27`, `Work.GW2.C27.eightTrich9_of_leaves`.

The leaves dispatched by area CORE4 in this round are stated against these names.
-/
import Submission.Work.LEAD.Core27
