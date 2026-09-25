/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proof routes for the arithmetic inputs of `NK.LocalInputs`

This module contains no mathematics: it is documentation, in the form of docstrings, of the
*intended proof routes* for the lemmas of this area which are delegated to the fleet and for the
named inputs of `NK.LocalInputs.Inputs`.  It is imported by those lemma files so that a prover
(a colleague agent) reading only the statement and its imports can see the classical argument.

## `LocalFieldInputs.principal_units_card` and the power-class count

For `κ = K_𝔭` a `p`-adic field (residue characteristic `p`), the classical chain is

* `κˣ ≅ ℤ × 𝒪_κˣ` (uniformiser and the units), `𝒪_κˣ ⊇ U¹ = 1 + 𝔪` with `𝒪_κˣ/U¹ ≅ F_qˣ`,
  `q = p^f` the residue field order;
* `U¹ ≅ μ_{p^∞}(κ) × ℤ_p^d`, `d = [κ : ℚ_p]` (via the `p`-adic logarithm: the filtration
  `U¹ ⊇ U² ⊇ …` has `U^n/U^{n+1} ≅ 𝔪^n/𝔪^{n+1}`, an `𝔽_p`-vector space of dimension `d`, and
  `1 + 𝔪^{n+1}` is a `p`-th power subgroup of `1 + 𝔪^n`);
* hence `|U¹/(U¹)^p| = |μ_{p^∞}[p]| · p^d = p^{d+δ}` with `δ = 1` iff `ζ_p ∈ κ`, and
  `|κˣ/(κˣ)^p| = p · |U¹/(U¹)^p| = p^{d+1+δ}`.

The `κ = ℚ_p` case of the last count is in the commons, as
`Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`
(`= p²` for `p` odd) and `…natCard_ker_unitsValLog_quot_pow` / `…natCard_adicCompletionIntegers_units_quot_pow`
(`|𝒪ˣ/(𝒪ˣ)^p| = p`).  The general case is the same argument with `ℚ_p` replaced by `ℚ_p^d`;
`Submission/Work/NumberTheory/NumberField/Completion/probe_count.lean` carries the `ℚ_p`-case
machinery (`PpowRat` and the log/exp bootstrap) which generalises.

## `ζ_p ∉ ℚ_p` for `p` odd (`not_exists_isPrimitiveRoot_rat_adic`)

The intended argument is elementary and uses no cyclotomic field theory:

* let `ζ ∈ ℚ_p` be a primitive `p`-th root of unity and put `v = Valued.v` (the `ℤ`-valued
  `𝔭`-adic valuation on `𝔭.adicCompletion ℚ`), normalised so that `v p = WithZero.exp (-1)`
  (`Commons.NumberTheory.NumberField.Completion.val_prime_adicCompletion_rat`);
* the identity `∏_{i=1}^{p-1} (1 - ζ^i) = p` holds in any field
  (it is `(X^p - 1)/(X - 1) = ∏_{i=1}^{p-1} (X - ζ^i)` evaluated at `X = 1`);
* each factor is a *non-unit* of the valuation ring: if `1 - ζ^i` were a unit then `ζ^i` would
  have a reduction `≠ 1` in the residue field `𝔽_p`, forcing `p ∣ p - 1` (the order of `ζ̄`
  divides both `p` and `|𝔽_pˣ| = p - 1`);
* therefore `p ∈ 𝔪^{p-1}`, so `v p ≤ WithZero.exp (-(p-1)) ≤ WithZero.exp (-2)`, contradicting
  `v p = WithZero.exp (-1)`
  (`Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow`).

For `p = 2` the statement is false: `-1` is a primitive `2`-nd root of unity in `ℚ_2`.


## The discrete unit group, its profinite completion, and the `p`-Frattini rank

The prose below replaces an earlier and *incorrect* note of this file, which claimed that the
passage from `κˣ` to its profinite completion `κˣ^{∧}` needed the structure theory
`κˣ ≅ ℤ × μ_κ × ℤ_p^d`.  That is not so: for a commutative group `A`,

  `numIndexSubgroups p A^{∧} = numIndexSubgroups p A`
  (`NK.LocalInputs.CommGroupRank.numIndexSubgroups_profiniteCompletion`),

so `HasFrattiniRank p r (A^{∧}) ↔ HasFrattiniRank p r A`.  Proof sketch: an index-`p` subgroup of a
commutative group is the kernel of a surjection onto `ℤ/p`, and such a surjection `A ↠ ℤ/p` extends
uniquely to a *continuous* `A^{∧} ↠ ℤ/p` (adjunction
`ProfiniteGrp.ProfiniteCompletion.homEquiv`), with open kernel; conversely, if `A/A^p` is finite,
the composite `A → A^{∧} → A^{∧}/(A^{∧})^p` is a surjection of `A/A^p` onto a finite elementary
abelian `p`-group (density plus finiteness), so `|A^{∧}/(A^{∧})^p| ≤ |A/A^p|` and every index-`p`
subgroup of `A^{∧}` (which contains `(A^{∧})^p`) is accounted for.  In the remaining case both sets
of subgroups are infinite and both `Nat.card`s are `0`.

The *pointwise* statement "every index-`p` subgroup of `A^{∧}` is open" is false in general (the
kernel of a discontinuous linear functional on `∏_ℕ ℤ/2` is a non-open index-`2` subgroup), but such
examples only occur when the counts are infinite, i.e. when `Nat.card` is `0` on both sides, so they
do not affect the counting statement above.

Consequently the profinite-completion form of the power-class count is *equivalent* to the discrete
one, and the abelian rank of `G_κ^{ab}` follows from part (1) plus Lubin–Tate, with no further
arithmetic input; see `NK.LocalInputs.InputsOfUnits`.

## Two traps, recorded so that they are not repeated

* **The exponent of the power-class count.**  For a `p`-adic field `F` of residue characteristic
  `p` and absolute degree `d = [F : ℚ_p]`, the correct exponent of `|Fˣ/(Fˣ)^p|` is `d + 1 + δ`
  (`δ = 1` iff `ζ_p ∈ F`), i.e. `2 + d` when `ζ_p ∈ F` and `1 + d` when `ζ_p ∉ F`.  An earlier
  attempt in this workspace used `1 + d` in the `ζ_p ∈ F` case and was refuted; the discrepancy is
  exactly the extra `ℤ/p` coming from the `p`-power roots of unity inside `U¹ = 1 + 𝔪`.  Note that
  `ζ_p ∈ F` *is* possible for a `p`-adic field of residue characteristic `p` — e.g. `F = ℚ_p(ζ_p)`
  — because `μ_p` need not lift to the residue field; the `p`-torsion of `U¹` is
  `μ_{p^∞}(F)`, cyclic of order `≥ p` exactly when `ζ_p ∈ F`.

* **`ℤ_ℓ²`-quotients do not give unbounded `ℓ`-tower rank.**  Shimizu's residue-characteristic
  detector (`HasZl2Quotient ℓ G`: surjections `G ↠ (ℤ/ℓ^n)²` for all `n`) is *not* sufficient for
  `HasUnboundedTowerRank ℓ G`: the group `ℤ_ℓ²` itself has `ℤ_ℓ²`-quotients, while all its open
  subgroups are again `≅ ℤ_ℓ²`, so its `ℓ`-Frattini ranks are bounded by `2`.  In the form used
  here (`HasUnboundedTowerRank`), the `ℓ = p` direction genuinely uses the *non-abelian* Demushkin
  structure of `G_κ^{(p)}` (generator rank `[κ : ℚ_p] + 1 + δ ≥ 3`).

## Ivanov's Lemma 3.12 (`LocalGaloisInputs.proP_unbounded`, `…other_bounded`)

* `ℓ ≠ p`: the wild inertia `V_κ` is a pro-`p` group (so it has no pro-`ℓ` quotients) and the
  tame quotient is `Ẑ ⋉ ∏_{ℓ' ≠ p} ℤ_{ℓ'}`, whose maximal pro-`ℓ` quotient is a pro-`ℓ` group of
  rank `≤ 2`; passing to a finite extension `M/κ` (of `ℓ`-power degree) preserves this bound, and
  the absolute Galois group of `M` is *the same kind of object* (`M` is again a `p`-adic field of
  residue characteristic `p ≠ ℓ`), so the `ℓ`-Frattini ranks of all the open subgroups of `G_κ`
  are bounded.
* `ℓ = p`: for any finite extension `M/κ` the group `Gal(M̄/M)` is the absolute Galois group of a
  `p`-adic field of absolute degree `[M : ℚ_p]`, whose maximal pro-`p` quotient is a Demushkin
  group of generator rank `[M : ℚ_p] + 1 + δ_M` (NSW (7.5.11)); taking `M/κ` totally ramified of
  degree `p^k` gives `[M : ℚ_p] = p^k [κ : ℚ_p] → ∞`, and the number of index-`p` subgroups of
  `Gal(M̄/M)` is `(p^{[M:ℚ_p]+1+δ_M} - 1)/(p - 1) → ∞`.  (This direction therefore follows from the
  abelian-rank input applied to the `p`-power extensions of `κ`; sibling areas
  `Submission/Work/LocalTame/` — `TameStructureInput` — and `Submission/Work/ProfiniteP/`.)
-/
import Submission.NK.LocalInputs.Defs

namespace NK.LocalInputs

end NK.LocalInputs
