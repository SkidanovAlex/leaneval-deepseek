/-
Copyright (c) 2025. All rights reserved.

# Exactness at `H¹(G, C)`

For a short exact sequence of `G`-modules `0 → A --iota--> B --pi--> C → 0` the sequence

`H¹(G, A) → H¹(G, B) --mapH1 π--> H¹(G, C) --δ¹--> H²(G, A) → H²(G, B)`

is exact: the image of the induced map `mapH1 π` is the kernel of the connecting map `δ¹`.

This is the `H¹(G, C)` step of the long exact sequence in low degrees (compare
`range_mapH0_eq_ker_mapH0`, `range_mapH1_eq_ker_mapH1`, `range_mapH2_eq_ker_mapH2`,
`range_mapH0_eq_ker_delta0H`, `range_delta0H_eq_ker_mapH1` and `range_deltaH1_eq_ker_mapH2`).

The proof lives in the sibling chapter `Submission.Work.Tate` (where the connecting maps of
`Work.GroupCohomology` are developed further); it is stated there for exactly the same
`Work.GroupCohomology.ShortExactSeq` data, so we re-export it here rather than duplicate it.
-/
import Submission.Work.Tate.ker_deltaH1_eq_range_mapH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- **Exactness of the long exact sequence at `H¹(G, C)`**: the image of the induced map
`H¹(G, B) → H¹(G, C)` is the kernel of the connecting map `δ¹ : H¹(G, C) → H²(G, A)` of a short
exact sequence `0 → A → B → C → 0` of `G`-modules. -/
theorem range_mapH1_eq_ker_deltaH1 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : ShortExactSeq G A B C) :
    (mapH1 G S.pi S.pi_equivariant).range = (S.deltaH1).ker :=
  (Work.Tate.ker_deltaH1_eq_range_mapH1 S).symm

end Work.GroupCohomology
