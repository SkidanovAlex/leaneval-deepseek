/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Block (i), part (B): instantiating `NK.Indecomposed.RankData`

This module instantiates the structure

```
NK.Indecomposed.RankData p K K' κ κ' = (hp, card_global, card_local, surj)
```

of `Submission/Work/Indecomposed/Defs.lean` — the "rank data" of Neukirch's Theorem 1 — from the
classical input catalogue of `Defs.lean`.  The three non-trivial fields are supplied as follows.

* **`card_global`** — `Nat.card (H²(U, μ_p)) = p` for closed `U ≤ G_K` with `U ≅ G_κ`.  This is
  *proved* here from two pieces:
  * the local computation at the local field itself,
    `NK.BrauerTwist.LocalFieldBrauerCyclic p κ κ'` (`H²(G_κ, μ_p) ≅ ℤ/p`), which gives
    `Nat.card (H²(G_κ, μ_p)) = p` (`natCard_H2Twist_top_of_localFieldBrauerCyclic`, proved below —
    the on-disk input `LocalFieldBrauerCyclic` carries the equivalence with `ZMod p` and
    `Nat.card (ZMod p) = p` is `Nat.card_zmod`);
  * the labelling transport `NK.IndecomposedDeep.GlobalBrauerTransport p K K' κ κ'`, which is the
    one genuinely new classical input (NSW (7.1.7)–(7.1.8) at the labelled subgroups; see
    `README.md` §3).
* **`card_local`** — the input `NK.IndecomposedDeep.LocalGroupBrauer p K K' κ κ'`
  (`p ≤ Nat.card (H²(H ⊓ D_A, μ_p))` for the non-trivial local groups, NSW (7.1.8)(i),(ii)).
* **`surj`** — Neukirch's modified surjectivity (NSW (9.2.1)).  This is *proved* here from the
  unconditional on-disk input `NK.HasseTwist.NeukirchH2modifiedsurj p K K' κ κ'` through the
  on-disk reduction `NK.HasseTwist.NeukirchH2modifiedsurjAt_of` (the guarded form used by the rank
  count is the weaker reading), so no new input is introduced for the surjectivity.

Consequently `RankData p K K' κ κ'` is a *theorem* given the catalogue; see
`rankData_of_inputs` (structures) and `rankData_of_fields` (raw fields).
-/

import Submission.NK.IndecomposedDeep.Defs

open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

open NK.BrauerTwist NK.HasseTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## The cardinality at the local field -/

/-- **`H²(G_κ, μ_p)` has exactly `p` elements.**  This is the *cardinality* half of the local
Brauer computation, and it is *proved* from the on-disk named input
`NK.BrauerTwist.LocalFieldBrauerCyclic` — the Kummer/Brauer statement `Br(κ)[p] ≅ ℤ/p`
(Serre, *Local Fields* XII–XIV; NSW (7.1.7), (7.2.6)), whose own reduction lives in
`Submission/Work/LocalCFT/Brauer/` — because the equivalence `H²(G_κ, μ_p) ≃ ZMod p` alone forces
the cardinality via `Nat.card_congr` and `Nat.card_zmod`. -/
theorem natCard_H2Twist_top_of_localFieldBrauerCyclic
    (h : NK.BrauerTwist.LocalFieldBrauerCyclic (κ := κ) (κ' := κ') p) :
    Nat.card (H2Twist (K := κ) (K' := κ') p ⊤) = p := by
  rw [Nat.card_congr h.1.some, Nat.card_zmod]

/-- **The cardinality at the labelled closed subgroups.**  A closed `U ≤ Gal(K'/K)` isomorphic to
`Gal(κ'/κ)` has `Nat.card (H²(U, μ_p)) = p`: the labelling transport
`NK.IndecomposedDeep.GlobalBrauerTransport` identifies its twisted cohomology with that of `G_κ`,
and `natCard_H2Twist_top_of_localFieldBrauerCyclic` computes the latter. -/
theorem natCard_H2Twist_of_transport (hbr : NK.BrauerTwist.LocalFieldBrauerCyclic (κ := κ) (κ' := κ') p)
    (htr : GlobalBrauerTransport p K K' κ κ')
    (U : Subgroup Gal(K'/K)) (hU : IsClosed (U : Set Gal(K'/K)))
    (hκ : Nonempty (U ≃* Gal(κ'/κ))) :
    Nat.card (H2Twist p U) = p := by
  obtain ⟨e⟩ := htr.equiv U hU hκ
  rw [Nat.card_congr e]
  exact natCard_H2Twist_top_of_localFieldBrauerCyclic hbr

/-! ## Neukirch's surjectivity (NSW (9.2.1)) -/

/-- **Neukirch's modified surjectivity in the guarded form**, from the unconditional on-disk input.
This is a *proved* reduction: the form `NeukirchH2modifiedsurjAt` consumed by the rank count of
`NK.Indecomposed` is the weaker reading of `NK.HasseTwist.NeukirchH2modifiedsurj` (it demands the
surjectivity only at a prime carrying a non-zero local component), and the implication is the
on-disk `NK.HasseTwist.NeukirchH2modifiedsurjAt_of`. -/
theorem neukirchH2modifiedsurjAt_of_input
    (h : NeukirchH2modifiedsurj p K K' κ κ') :
    NeukirchH2modifiedsurjAt p K K' κ κ' :=
  NeukirchH2modifiedsurjAt_of (K := K) (K' := K') (κ := κ) (κ' := κ') p h

/-! ## The rank data -/

/-- **`NK.Indecomposed.RankData` from the classical input catalogue.**

This is block (i)-rank-data of the Neukirch–Uchida endgame, *proved*:
`card_global` follows from the local Brauer computation `LocalFieldBrauerCyclic` (on disk) and the
labelling transport `GlobalBrauerTransport`, `card_local` is the input `LocalGroupBrauer` (the
local Brauer computation at the local groups, NSW (7.1.8)), and `surj` follows from the on-disk
Neukirch surjectivity `NK.HasseTwist.NeukirchH2modifiedsurj` (NSW (9.2.1)). -/
theorem rankData_of_inputs (hp : p.Prime)
    (hbrauer : NK.BrauerTwist.LocalFieldBrauerCyclic (κ := κ) (κ' := κ') p)
    (htransport : GlobalBrauerTransport p K K' κ κ')
    (hlocal : LocalGroupBrauer p K K' κ κ')
    (hsurj : NeukirchH2modifiedsurj p K K' κ κ') :
    NK.Indecomposed.RankData p K K' κ κ' where
  hp := hp
  card_global := fun U hU hκ => natCard_H2Twist_of_transport hbrauer htransport U hU hκ
  card_local := hlocal.card_local
  surj := neukirchH2modifiedsurjAt_of_input hsurj

/-- The same theorem in the raw-field form (no auxiliary structures), for callers that prefer to
supply the four inputs directly.  The fields `card_global`, `card_local` are the literal ones of
`NK.Indecomposed.RankData`. -/
theorem rankData_of_fields (hp : p.Prime)
    (hcard : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → Nat.card (H2Twist p U) = p)
    (hloc : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
      Nonempty (H ≃* Gal(κ'/κ)) →
      ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
          V ≠ ⊥ → p ≤ Nat.card (H2Twist p V))
    (hsurj : NeukirchH2modifiedsurjAt p K K' κ κ') :
    NK.Indecomposed.RankData p K K' κ κ' where
  hp := hp
  card_global := hcard
  card_local := hloc
  surj := hsurj

/-- **The local Brauer non-vanishing follows from the rank data.**  A non-zero class in `H²(H, μ_p)`
exists as soon as the rank data computes its cardinality to be the prime `p`; this is the on-disk
`NK.Indecomposed.localH2Input_of_rankData`, re-exported here so that a caller of this chapter sees
the non-vanishing as a *consequence* of the catalogue. -/
theorem localH2Input_of_rankData (hrank : NK.Indecomposed.RankData p K K' κ κ') :
    NK.BrauerTwist.LocalH2Input p K K' κ κ' :=
  NK.Indecomposed.localH2Input_of_rankData (K := K) (K' := K') (κ := κ) (κ' := κ') hrank

end NK.IndecomposedDeep
