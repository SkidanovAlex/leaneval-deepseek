import Mathlib
import Submission.Work.DSCOH.Norm.HomoAssembly
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs

/-!
Area DSCOH — the "diagonal" term of the second differential of the degenerate-simplices homotopy.

For a nondecreasing tuple `y : Fin (k+2) → ι` which is not strictly increasing, the `c`-th term
`Hterm P U k y c` of the second differential of the homotopy identity reads, at the tuple obtained
from `y` by duplicating the first repeat and then deleting the `c`-th entry.  Deleting the *first*
copy of the duplicated entry (`c = (frA y).castSucc.castSucc`) reads the tuple `y` back, and the
canonical composite `resDel ≫ isoDup` attached to that read-out is the identity; the scalar
`(-1)^(frA + c) = (-1)^(2·frA)` equals `1`.  Hence this term is exactly the projection onto the
`y`-component:

`Hterm P U k y ((frA y).castSucc.castSucc) = π_y`.

The two auxiliary lemmas below are the two ingredients: `frA` is insensitive to the choice of the
proof terms, and a canonical `P.map`-morphism of sections can be pushed through a projection of the
product `semiTerm` as soon as the two indexing tuples agree.
-/

namespace Work.DSCOH.Pair

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
variable {ι : Type*} [LinearOrder ι]

/-- `frA` depends on its arguments only through the tuple `y`: the choice of the proof terms
witnessing monotonicity and non-strict-monotonicity is irrelevant. -/
lemma frA_congr {k : ℕ} (y : Fin (k + 2) → ι) (hy hy' : Monotone y) (hh hh' : ¬ StrictMono y) :
    Work.DSCOH.Norm.frA y hy hh = Work.DSCOH.Norm.frA y hy' hh' := by
  unfold Work.DSCOH.Norm.frA Work.DSCOH.Norm.firstRepeat
  congr 1

/-- Pushing a canonical morphism of sections through a projection of the product `semiTerm`: if the
indexing tuples `z` and `y` agree, then the projection at `z`, composed with any canonical
`P.map`-morphism into the `y`-component, is the projection at `y`. -/
lemma Pi_π_comp_map_eq [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → Opens X) {k : ℕ} {z y : Work.DSCOH.Norm.SemiIdx ι (k + 1)} (hz : z = y)
    {α : op (Work.DSCOH.Norm.tupleOp U z.val) ⟶ op (Work.DSCOH.Norm.tupleOp U y.val)} :
    Pi.π (fun w : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U w.val) z
        ≫ P.map α
      = Pi.π (fun w : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U w.val) y := by
  subst hz
  erw [Subsingleton.elim α (𝟙 _), P.map_id, Category.comp_id]

theorem Hterm_self {k : Nat} {ι : Type*} [LinearOrder ι] {X : Type*}
    [TopologicalSpace X] {A : Type*} [CommRing A]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X)
    (y : Work.DSCOH.Norm.SemiIdx ι (k + 1)) (hy : Monotone y.val) (hh : Not (StrictMono y.val)) :
    Work.DSCOH.Norm.Hterm P U k y
        ((Work.DSCOH.Norm.frA y.val hy hh).castSucc.castSucc)
      = CategoryTheory.Limits.Pi.π
        (fun w : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U w.val) y := by
  -- Prove the statement for the `frA`-value `frA y.val y.property hh` (the one used inside
  -- `Hterm` itself), where no proof-term mismatch occurs, and transport to `frA y.val hy hh`.
  have H : Work.DSCOH.Norm.Hterm P U k y
        ((Work.DSCOH.Norm.frA y.val y.property hh).castSucc.castSucc)
      = CategoryTheory.Limits.Pi.π
        (fun w : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U w.val) y := by
    rw [Work.DSCOH.Norm.Hterm, dite_eq_right hh]
    simp only [Fin.val_castSucc]
    -- `resDel ≫ isoDup` is `P.map` of a single morphism of `(Opens X)ᵒᵖ`.
    have hβ : Work.DSCOH.Norm.resDel P U
            (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc)
            ((Work.DSCOH.Norm.frA y.val y.property hh).castSucc).castSucc
          ≫ Work.DSCOH.Norm.isoDup P U y.val
              (Work.DSCOH.Norm.frA y.val y.property hh).castSucc
        = P.map ((homOfLE (leOfHom (Work.DSCOH.Norm.opDel U
              (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc)
              ((Work.DSCOH.Norm.frA y.val y.property hh).castSucc).castSucc))).op
            ≫ (Work.DSCOH.Norm.opDup U y.val
                (Work.DSCOH.Norm.frA y.val y.property hh).castSucc).op) := by
      rw [Work.DSCOH.Norm.resDel, Work.DSCOH.Norm.isoDup, ← P.map_comp]
    rw [hβ]
    -- The scalar is `(-1)^(frA + frA) = 1`.
    have hsc : (-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y.val y.property hh : ℕ)
        + (Work.DSCOH.Norm.frA y.val y.property hh : ℕ)) = 1 :=
      Even.neg_one_pow (⟨_, rfl⟩ : Even _)
    rw [hsc, one_smul]
    -- Deleting the first copy of the duplicated entry reads `y` back.
    exact Pi_π_comp_map_eq P U
      (Subtype.ext (Work.DSCOH.Norm.del_dup_castSucc y.val
        (Work.DSCOH.Norm.frA y.val y.property hh).castSucc))
  rw [show (Work.DSCOH.Norm.frA y.val hy hh) = (Work.DSCOH.Norm.frA y.val y.property hh)
    from frA_congr y.val hy y.property hh hh]
  exact H

end Work.DSCOH.Pair
