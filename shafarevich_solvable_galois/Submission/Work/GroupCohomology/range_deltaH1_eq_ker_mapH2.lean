/-
Copyright (c) 2025. All rights reserved.

# Exactness at `H²(G, A)`

For a short exact sequence of `G`-modules `0 → A --iota--> B --pi--> C → 0` the sequence

`H¹(G, C) --δ¹--> H²(G, A) --mapH2 iota--> H²(G, B)`

is exact: the image of the connecting map `δ¹` is the kernel of `mapH2 iota`.

This is the `H²(G, A)` step of the long exact sequence in low degrees; the proof lives in the
sibling chapter `Submission.Work.Tate` and is re-exported here (see
`range_mapH1_eq_ker_deltaH1`).
-/
import Submission.Work.Tate.range_deltaH1_eq_ker_mapH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- **Exactness of the long exact sequence at `H²(G, A)`**: the image of the connecting map
`δ¹ : H¹(G, C) → H²(G, A)` is the kernel of `H²(G, A) → H²(G, B)`. -/
theorem range_deltaH1_eq_ker_mapH2 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : ShortExactSeq G A B C) :
    (S.deltaH1).range = (mapH2 G S.iota S.iota_equivariant).ker :=
  Work.Tate.range_deltaH1_eq_ker_mapH2 S

end Work.GroupCohomology
