import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The named black box: Feit's Theorem 1 in the Zassenhaus case

`FeitInequalityProp` is the single character-theoretic input the area consumes: Feit's
inequality (28) of *On a class of doubly transitive permutation groups*, Illinois J. Math. 4
(1960) 170–186, specialised to the rank-one Zassenhaus set-up of this area.  Everything else in
the area is proved (see `Main`), so this file isolates exactly what remains to be formalised
from Feit's §§2–3 / Peterfalvi II App. XII.

Route from Feit's text (vision transcription `REFS/vision/feit1960/`, authoritative):

* `p0011` (Feit p. 179) **Lemma 3.1**: the point stabiliser is `H = M ⋊ D` with `M = Q` the
  Frobenius kernel of order `m`, `|N(M)| = mq`, `N(Q) ≤ 2q`, and `Q` is T.I.  These are the
  `Setting` lemmas of this area (`fpf_on_Q`, `isTI_Q`, `card_H_eq`, `card_quotient_eq`, …).
* `p0011` **Hypothesis III**: `q` odd, no normal subgroup of order `m+1`, `G = ⟨M^G⟩`.
  In this area `G` is simple, so Hypothesis III holds (`q` odd comes from `|D| ∣ |Q|-1` with
  `|Q|` even — `odd_card_twoPoint`, `even_card_Q`, `card_twoPoint_dvd`).
* `p0011`/`p0013` **Lemma 3.2**: it suffices to prove `q ≥ (m-1)/2`, or `M` is a non-abelian
  `p`-group with `[M:M'] < 4q²`.  In this area `|Q| = m` is even, so if `Q` were a `p`-group
  then `p = 2`; hence under the assumption `¬ IsPGroup 2 Q` the second alternative is excluded
  and Lemma 3.2 reduces Feit's Theorem 1 to the inequality stated here.
* `p0011`/`p0012` **Lemma 3.3**: `|N(Q)| = 2q`, `Q` cyclic, no element of `Q ∖ 1` commutes with
  an element outside `Q` (Burnside's transfer theorem).
* `p0012`/`p0013` **Lemma 3.4**: one class of involutions, with `q(m+1)` involutions when `m` is
  even (Brauer–Fowler `[2, Lemma 3A, Corollary 2B]` — external input, *not* available in this
  workspace).
* `p0013` **Lemma 3.5**: at least `q` non-exceptional irreducible characters (Brauer–Fowler
  `[2, Theorem 2J]` — external input).
* `p0013`/`p0014` **(18)–(28)**: the double-coset values of `η_i^* = Ind η_i`, the orthogonality
  `(η_i^*, η_j^*) = δ_ij` (19), the norm computation `‖ζ_1^*‖² = q+1` (20), and the exceptional
  character count giving `2q ≥ m-1`.

So the formal gap is: Feit's §2 (exceptional characters, i.e. Theorem 2 on p. 176 with
Corollaries 2.1–2.4 on pp. 179–180) and §3's Lemmas 3.3–3.5, two of which quote the
Brauer–Fowler counting theorems.  The parts of this chain that the area *does* contain are
`coherent_of_not_isPGroup` (Feit–Sibley ⟹ coherence of `𝓢`) and the exceptional-character
extraction `Exceptional.exceptional_data` with the norm identity
`Exceptional.cfInner_indLin_diff`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- **Feit 1960, Theorem 1, Zassenhaus case** (the area's only black box).

In a finite simple group with rank-one Zassenhaus data `H = Q ⋊ D` in which `Q` is not a
`2`-group, the two-point stabiliser `D = H ∩ H^t` has at most two orbits on `Q#`:
`|Q| - 1 ≤ 2 |D|`.  This is Feit's inequality (28); see the module docstring for its derivation
from Feit's Theorem 2 and Lemmas 3.1–3.5. -/
def FeitInequalityProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (H Q : Subgroup G) (t : G),
    IsSplitRankOne H Q t → IsZassenhaus H → ¬ IsPGroup 2 Q →
      Nat.card Q - 1 ≤ 2 * Nat.card (twoPoint H t)

end Work.ZassenhausTwoGroup
