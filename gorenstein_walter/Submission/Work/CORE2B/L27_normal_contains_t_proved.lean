import Submission.Work.CORE2B.L27_step1_leaf

/-!
# `Work.CORE2B.L27_normal_contains_t` — Bender 1981, Lemma 2.7, p. 221, step 1

Under the hypotheses bundled in `L27Hyp B M` (minimal counterexample `G`, `Ĥ ⇝ M ≠ Ĥ`,
`t ∈ M`, `t ∉ E(M)`, Sylow 2-subgroups of `M` non-cyclic, and the size condition), every
normal subgroup `N ≤ M` with `4 ∣ |N|` contains `t`.

## Why the naive route needs repair, and what the actual proof is

The sketch recorded in `NOTES_CORE2B.md` §3 ("`N` contains a 2-subgroup `T` with `|T| ≥ 4`;
`T ≤ S^g` for some `g`; every subgroup of order `≥ 4` of a dihedral 2-group contains its
central involution, so `t^g ∈ N`; as `t ∈ M` and `N ◁ M`, `t ∈ N`") is **not valid as written**:
`t^g ∈ N` gives only that `N` contains the `M`-conjugacy class of `t^g`, and `t` need not be
`M`-conjugate to `t^g`.  Concretely, in `G = PSL(2,7)` with `M = S₄` a point stabiliser,
`N = F(M) = V₄ ◁ M` and `t` an involution of `M` outside `F(M)`, one has `4 ∣ |N|`, `t ∈ M`,
`t ∉ N`, and `N` does contain a `G`-conjugate `t^g` of `t` — so the step "conjugating back"
fails; only the extra hypotheses of `L27Hyp` (in particular `M ≠ Ĥ`, `Ĥ ⇝ M`) rule out that
configuration.

The correct argument (formalised in `Submission/Work/CORE2B/L27_step1_leaf.lean` and its
supporting modules) splits on the three alternatives `|S ⊓ M| ≥ 8`, `|S| = 4`,
`t ∈ O²(M)` of `L27Hyp.size` and produces, in each case, a Sylow 2-subgroup `P` of `M` with
`t ∈ Z(P)`:

* `8 ≤ |S ⊓ M|` (`sylow_central_of_large_inter`): if `t` were not central in `P ⊇ S ⊓ M`, then
  inside a dihedral group the centraliser of the non-central involution `t` would have order
  `≤ 4`, contradicting `|C_P(t)| ≥ |S ⊓ M| ≥ 8`;
* `|S| = 4` (`card_four_centralizes`): then every 2-subgroup of `G` has order `≤ 4` and is
  abelian;
* `t ∈ O²(M)` (`twoResidual_centralizes`): otherwise Thompson's transfer lemma yields a normal
  subgroup of `M` of index `2` avoiding `t`, contradicting `t ∈ O²(M)`.

Finally `normal_contains_center`: for `P` a Sylow 2-subgroup of `M` — a non-cyclic subgroup of a
dihedral group, hence dihedral — and `N ◁ M` with `4 ∣ |N|`, the intersection `N ⊓ P` is a Sylow
2-subgroup of `N`, so `|N ⊓ P| ≥ 4 ≥ 2` is not the trivial group; in a dihedral 2-group every
subgroup of order `≥ 4` contains the centre, hence `t ∈ N ⊓ P ≤ N`.

The proof of the leaf itself is contributed by the area's own module `L27_step1_leaf`; the
present file records the leaf under the requested name so that colleagues can import it.
-/

namespace Work.CORE2B

theorem L27_normal_contains_t_proved : Work.CORE2B.L27_normal_contains_t := L27_step1_leaf

end Work.CORE2B
