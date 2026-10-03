/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ring structure on the skew Laurent series ring `A((t;τ))`

Assembles the operation lemmas in `Submission/Work/ORHughesFree/SkewLaurentSeries/` into the
`AddCommGroup` and `Ring` instances on `Work.ORHughesFree.SkewLaurentSeries A`, together with the
`A`-algebra embedding `coeff : A →+* A((t;τ))` and the unit `t`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.add_comm
import Submission.Work.ORHughesFree.SkewLaurentSeries.add_assoc
import Submission.Work.ORHughesFree.SkewLaurentSeries.zero_add
import Submission.Work.ORHughesFree.SkewLaurentSeries.add_zero
import Submission.Work.ORHughesFree.SkewLaurentSeries.neg_add_cancel
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_assoc
import Submission.Work.ORHughesFree.SkewLaurentSeries.one_mul
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_one
import Submission.Work.ORHughesFree.SkewLaurentSeries.left_distrib
import Submission.Work.ORHughesFree.SkewLaurentSeries.right_distrib
import Submission.Work.ORHughesFree.SkewLaurentSeries.zero_mul
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_zero
import Submission.Work.ORHughesFree.SkewLaurentSeries.coeff_ringHom
import Submission.Work.ORHughesFree.SkewLaurentSeries.t_mul_coeff
import Submission.Work.ORHughesFree.SkewLaurentSeries.t_unit

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

noncomputable instance skewLaurentSeriesAddCommGroup (A : Type) [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] : AddCommGroup (SkewLaurentSeries A) where
  add_assoc := SkewLaurentSeries.add_assoc
  zero_add := SkewLaurentSeries.zero_add
  add_zero := SkewLaurentSeries.add_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := SkewLaurentSeries.neg_add_cancel
  add_comm := SkewLaurentSeries.add_comm

noncomputable instance skewLaurentSeriesRing (A : Type) [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] : Ring (SkewLaurentSeries A) where
  mul_assoc := SkewLaurentSeries.mul_assoc
  one_mul := SkewLaurentSeries.one_mul
  mul_one := SkewLaurentSeries.mul_one
  left_distrib := SkewLaurentSeries.left_distrib
  right_distrib := SkewLaurentSeries.right_distrib
  zero_mul := SkewLaurentSeries.zero_mul
  mul_zero := SkewLaurentSeries.mul_zero
  npow := npowRec

/-- The coefficient embedding `A →+* A((t;τ))`. -/
noncomputable def skewLaurentCoeff (A : Type) [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    A →+* SkewLaurentSeries A where
  toFun := SkewLaurentSeries.coeff
  map_one' := (SkewLaurentSeries.coeff_ringHom (1 : A) 1).2.2
  map_mul' a b := (SkewLaurentSeries.coeff_ringHom a b).1
  map_zero' := by
    refine Subtype.ext (funext fun n => ?_)
    rw [SkewLaurentSeries.coeff_apply, SkewLaurentSeries.zero_apply]
    split_ifs with h
    · rfl
    · rfl
  map_add' a b := (SkewLaurentSeries.coeff_ringHom a b).2.1

/-- The unit `t` of `A((t;τ))`. -/
noncomputable def skewLaurentSeriesT (A : Type) [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    (SkewLaurentSeries A)ˣ :=
  let h := SkewLaurentSeries.t_unit (A := A)
  ⟨SkewLaurentSeries.t, Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

theorem skewLaurentSeriesT_coe (A : Type) [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    (skewLaurentSeriesT A : SkewLaurentSeries A) = SkewLaurentSeries.t := rfl

/-- The defining relation `t · a = τ(a) · t` of `A((t;τ))`. -/
theorem skewLaurentSeriesT_mul (A : Type) [Ring A] [MulSemiringAction (Multiplicative ℤ) A] (a : A) :
    (skewLaurentSeriesT A : SkewLaurentSeries A) * skewLaurentCoeff A a =
      skewLaurentCoeff A ((Multiplicative.ofAdd (1 : ℤ)) • a) *
        (skewLaurentSeriesT A : SkewLaurentSeries A) :=
  SkewLaurentSeries.t_mul_coeff a

end Work.ORHughesFree
