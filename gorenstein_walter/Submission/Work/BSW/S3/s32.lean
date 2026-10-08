/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Bender §3.2: the coset count (`Work.BSW.BSWS32Prop`)

Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, §3.2
(`REFS/vision/bender1974_bsw/p0005.md`).

Setting: `G` finite with `BSWHyps2 G t s K`, `x ∉ H^G` (`H = C_G(t)`) inverted by `t`.  With

* `F = C_G(x)`, `M = N_G(F)`, `f = |F|`, `k = |K|`, `n = |K ⊓ M|`, `m = |G : M|`, `I = |G : H|`,

Bender's coset count on `Ω = G ⧸ M` shows that one of the following holds:

* (i)  `I = f(k+1)` and `m = 1 + f(2k/n - 1)`;
* (ii) `I - m ≤ f(k+1) - (1 + f(2k/n - 1))` and `m ≥ f(2k/n) + 1`.

The uniform form of this disjunction, which is what `Work.BSW.BSWS32Prop` states, is the
conjunction

1. `1 + f(2k/n - 1) ≤ m`            — the special cosets (those fixed by an involution of `M`)
   number `f(2k/n - 1)` besides `M` itself;
2. `f ∣ m - (1 + f(2k/n - 1))`      — `F` acts freely on the remaining, non-special cosets;
3. `f(k+1) ≤ I`                     — the involutions commuting with an element of `M` number
   `f(k+1)`;
4. `I - f(k+1) ≤ m - (1 + f(2k/n - 1))` — every non-special coset contains at most one
   involution ("InvertM").

## Contents

The four inequalities above are proved, in the shared vocabulary of the sibling §3.2 development,
as `Work.BSW.Cases.claim1`–`claim4` (`Submission/Work/BSW/Cases/bswS32Count.lean`); this file
states the assembled result for area `Work.BSW.S3` by deriving their auxiliary inputs from the
structural lemmas of `Work.BSW.Cases` (`bswS32Hall`: `F ⊓ M^g = ⊥`; `card_centralizer_eq`:
`|C_G(u)| = 2k` for involutions; `bswS32U`: the count `|U| = f(k+1)`; `bswS32InvertM_local`:
Bender's InvertM).

  * `claim1` : `card_special` + `card_fixSet` + `fixSet_disjoint`;
  * `claim2` : `F` acts freely on the non-special cosets (`nonspecialMulAction`);
  * `claim3`, `claim4` : `bswS32U` (the `fk` involutions in special cosets) and InvertM.
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.s31
import Submission.Work.BSW.Cases.bswS32
import Submission.Work.BSW.Cases.bswS32Count

namespace Work.BSW.S3

open Subgroup Work.GW2

/-- **Bender §3.2** (`Work.BSW.BSWS32Prop`), assembled from the four inequalities
`Work.BSW.Cases.claim1`–`claim4`. -/
theorem s32 : Work.BSW.BSWS32Prop := by
  intro G _ _ t s K x h hx hinv
  -- Bender §3.1(e): `F ⊓ M^g = ⊥` for `g ∉ M`.
  have hHall : ∀ g : G, g ∉ Work.BSW.Cases.NF x →
      Work.BSW.Cases.CF x ⊓ conjSub g (Work.BSW.Cases.NF x) = ⊥ :=
    (Work.BSW.Cases.bswS32Hall h hx hinv).2
  -- `|C_G(u)| = 2k` for every involution `u` (all involutions are conjugate).
  have hcardC : ∀ u : G, orderOf u = 2 → u ∈ Work.BSW.Cases.NF x →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 * Nat.card K :=
    fun u hu _ => Work.BSW.Cases.card_centralizer_eq h hu
  -- the involutions commuting with an involution of `M` number `f(k+1)`.
  have hU := Work.BSW.Cases.bswS32U h hx hinv
  -- Bender's InvertM lemma.
  have hInvertM := Work.BSW.Cases.bswS32InvertM_local h hx hinv
  exact ⟨Work.BSW.Cases.claim1 (x := x) h hx hinv hHall hcardC,
    Work.BSW.Cases.claim2 (x := x) h hx hinv hHall hcardC,
    Work.BSW.Cases.claim3 (x := x) h hx hinv hU,
    Work.BSW.Cases.claim4 (x := x) h hx hinv hHall hcardC hU hInvertM⟩

end Work.BSW.S3
