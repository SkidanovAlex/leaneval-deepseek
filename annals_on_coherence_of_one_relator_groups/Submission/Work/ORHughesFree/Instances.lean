/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Instances and derived objects for the JZLA20 engine

* the ∗-regular closure of a ∗-subring of a ∗-regular ring is ∗-regular (an instance, so that
  `starRegularClosure_le` can be applied with `S = starRegularClosure R`);
* `divisionRank D`, the (unique) Sylvester rank function on a division ring, obtained from
  `exists_sylvesterRank_divisionRing` and made unique by `sylvesterRank_unique_divisionRing`.
-/
import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular
import Submission.Work.ORHughesFree.DivisionRank.exists_sylvesterRank_divisionRing
import Submission.Work.ORHughesFree.DivisionRank.sylvesterRank_unique_divisionRing

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- The ∗-regular closure of a ∗-subring of a ∗-regular ring is ∗-regular
([JZLA20, Proposition 2.2]). -/
instance instIsStarRegularStarRegularClosure {U : Type u} [Ring U] [StarRing U] [IsStarRegular U]
    (R : StarSubring U) : IsStarRegular (starRegularClosure R) :=
  StarRegular.starRegularClosure_isStarRegular R

/-- The (unique) Sylvester rank function on a division ring, i.e. the dimension of the image of the
matrix.  By `SylvesterRank.sylvesterRank_unique_divisionRing` any two such functions agree, so this
is the only rank function on a division ring ([JZLA20, §2.4]). -/
noncomputable def divisionRank (D : Type u) [DivisionRing D] : SylvesterRank D :=
  Classical.choice (DivisionRank.exists_sylvesterRank_divisionRing D)

/-- `divisionRank` is the unique Sylvester rank function on a division ring. -/
theorem divisionRank_unique {D : Type u} [DivisionRing D] (rk : SylvesterRank D) (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) D) : (divisionRank D).rk n m A = rk.rk n m A :=
  DivisionRank.sylvesterRank_unique_divisionRing (divisionRank D) rk n m A

end Work.ORHughesFree
