/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS2: the `d` even branch, refined interface

Area `ZASS` (design pass 9, `Submission/Work/ZASS/Leaf9.lean`) splits step Z6 of the
Zassenhaus recognition theorem into leaf `Prop`s in namespace `Work.GW2`.  This area
(`Submission/Work/ZASS2/`, namespace `Work.ZASS2`) finishes them.

The leaf `Work.GW2.ZassHkProp` (HB 1.10) is *stated* purely in terms of the Bruhat
decomposition `s * u * s = u₂ * s * u⁻¹ * h`, and its clause (c) asserts that every `h ∈ H`
admits *some* `u` with `h • (s • (u • 0)) = u⁻¹ • 0`.  That is not quite enough to run the
HB 1.11 argument verbatim: one needs a *family* `u ↦ h_u` with the defining properties of
HB 1.9/1.10, in particular `h_{u⁻¹} = h_u` and `h_u • (s • (u • 0)) = u⁻¹ • 0` for *the same*
`h_u`.  The present file records that family as a single `Prop`, `Work.ZASS2.ZassHuProp`.

(The leaf `Work.GW2.ZassInvertEvenProp` is proved in `Submission/Work/ZASS2/zassInvertEven.lean`
by a direct construction of `h_u`; `ZassHuProp` is the abstract statement of the same
computation, and `Work.ZASS2.zassHu` proves it separately, for reuse.)

`ZassHuProp` is HB III.11 1.9 + 1.10 in the form needed downstream:

* `hu u ∈ H = G_{∞0}` for `u ≠ 1` (HB 1.9: `h_u` is a product of two Bruhat cells);
* the Bruhat cell decomposition `s u s = u₂ s u⁻¹ h_u` (HB 1.9);
* `h_u • (s • (u • 0)) = u⁻¹ • 0` (HB 1.10 b);
* `h_{u⁻¹} = h_u` (the implicit `(q-1)/2 = |H|` counting of HB 1.10 a/c);
* every `h ∈ H` is some `h_u` (HB 1.10 c).

The explicit element is `h_u = u · s · (σ u)⁻¹ · s · u · s`, where `σ u` is the element of
`U` with `σ u • 0 = s • (u • 0)` (`Work.ZASS.EvenData.sigma`), so a prover may simply define
it and verify the five clauses.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.EvenSetup

namespace Work.ZASS2

open Work.GW2
open Work.Zassenhaus (pairStab)

/-- **HB 1.9 + 1.10, as an interface.**  In the `d`-even setting (`d = (p^k-1)/2` even,
hence `H = G_{∞0}` has a unique involution inverting `U`, HB 1.8) and for an involution `s`
interchanging `∞` and `0`, there is a family `u ↦ h_u` (`u ∈ U`, `u ≠ 1`) with

1. `h_u ∈ H`;
2. `s u s = u₂ · s · u⁻¹ · h_u` for some `u₂ ∈ U`;
3. `h_u • (s • (u • 0)) = u⁻¹ • 0`;
4. `h_{u⁻¹} = h_u`;
5. every `h ∈ H` equals some `h_u`. -/
def ZassHuProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → Even ((p ^ k - 1) / 2) →
    ∀ (inf zero : X), inf ≠ zero → ∀ U : Subgroup G, ZassUData G X p k inf zero U →
    ∀ s : G, s * s = 1 → s • inf = zero → s • zero = inf →
    ∃ hu : U → G,
      (∀ u : U, u ≠ 1 → hu u ∈ pairStab G inf zero) ∧
      (∀ u : U, u ≠ 1 → ∃ u₂ ∈ U, s * u * s = u₂ * s * u⁻¹ * hu u) ∧
      (∀ u : U, u ≠ 1 → hu u • (s • (u • zero)) = u⁻¹ • zero) ∧
      (∀ u : U, u ≠ 1 → hu u⁻¹ = hu u) ∧
      (∀ h ∈ pairStab G inf zero, ∃ u : U, u ≠ 1 ∧ hu u = h)

end Work.ZASS2
