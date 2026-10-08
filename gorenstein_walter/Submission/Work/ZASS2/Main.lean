/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS2: the Zassenhaus recognition theorem (odd `q`)

This module assembles the leaves of area ZASS2 into

  `Work.ZASS2.zassOdd2 : Work.GW2.ZassOdd2Prop`,

the ZASS contract of `Submission/Work/_design_gw/Core2.lean` as amended by design pass 2: a
simple group `G` acting faithfully and 2-transitively on `q + 1 = p^k + 1` points, with every
non-identity element fixing at most two points and every two-point stabilizer of order
`(q - 1)/2`, is isomorphic to `PSL(2, GaloisField p k)` (HB III.XI Theorems 1.11 + 1.12).

The two assemblies `Work.GW2.zassInvertPK_of_parts` and `Work.GW2.zassWeyl_of_parts` are proved
in `Submission/Work/ZASS/Leaf9.lean`, and `Work.ZASS.zassOdd2_of_weyl` (which adds the Z1-Z4
cardinality computation) in `Submission/Work/ZASS/Main.lean`.  The leaves supplied here are:

| leaf | module |
|---|---|
| `Work.GW2.ZassInvertOddProp` | `Submission.Work.ZASS2.zassInvertOddMain` |
| `Work.GW2.ZassInvertEvenProp` | `Submission.Work.ZASS2.zassInvertEven` |
| `Work.GW2.ZassCyclicOfCommProp` | `Submission.Work.ZASS2.Basic` |
| `Work.GW2.ZassCoordProp` | `Submission.Work.ZASS2.zassCoord` |
| `Work.GW2.ZassGoodSwapProp` | `Submission.Work.ZASS2.Basic` |
| `Work.GW2.ZassReciprocityFieldProp` | `Submission.Work.ZASS2.zassReciprocityField` |
| `Work.GW2.ZassReciprocityProp` | `Submission.Work.ZASS2.zassReciprocity_of_field` |
| `Work.GW2.ZassEndgameProp` | `Submission.Work.ZASS2.zassEndgame` |
-/
import Mathlib
import Submission.Work.ZASS2.Defs
import Submission.Work.ZASS2.Basic
import Submission.Work.ZASS2.zassCoord
import Submission.Work.ZASS2.zassInvertEven
import Submission.Work.ZASS2.zassInvertOddMain
import Submission.Work.ZASS2.zassReciprocityField
import Submission.Work.ZASS2.zassReciprocity_of_field
import Submission.Work.ZASS2.zassEndgame
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Main

namespace Work.ZASS2

/-- **Step Z6.5′ in group form** (`Work.GW2.ZassReciprocityProp`): the group form transported
from the pure field statement `Work.ZASS2.zassReciprocityField` (HB 1.11/1.12). -/
theorem zassReciprocityProp : Work.GW2.ZassReciprocityProp :=
  zassReciprocity_of_field zassReciprocityField

/-- **HB III.XI Theorems 1.11 + 1.12.**  The ZASS contract of design pass 2: a simple
Zassenhaus group of odd degree `q + 1 = p^k + 1` is `PSL(2, GaloisField p k)`.

Assembled from the leaf `Prop`s of design pass 9: `Work.GW2.zassInvertPK_of_parts` (HB 1.5 for
odd `d`, HB 1.8-1.11 for even `d`, plus `ZassCyclicOfCommProp`) and
`Work.GW2.zassWeyl_of_parts` (the coordinate step Z6.0, the choice of the swapping involution,
Z6.5' reciprocity and the Z6.6 endgame), and finally the Z1-Z4 order computation
`Work.ZASS.zassOdd2_of_weyl`. -/
theorem zassOdd2 : Work.GW2.ZassOdd2Prop :=
  Work.ZASS.zassOdd2_of_weyl <|
    Work.GW2.zassWeyl_of_parts
      (Work.GW2.zassInvertPK_of_parts zassInvertOddMain zassInvertEven zassCyclicOfComm
        Work.ZASS.zassInvolutionSwapProp)
      zassCoord zassGoodSwap zassReciprocityProp zassEndgame

end Work.ZASS2
