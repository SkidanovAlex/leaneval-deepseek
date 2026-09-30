import Mathlib
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.sum_abs_Icc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

theorem sum_eqnIdx_abs (r S T : ℕ) :
    ∑ e : AuxEqnIdx r S T, |((e.1 : ℤ))| = ((Fintype.card (MultIdx r T) * (S * (S + 1)) : ℕ) : ℤ) := by
  rw [Fintype.sum_prod_type]
  trans ∑ x : {s : ℤ // s ∈ Finset.Icc (-(S:ℤ)) S},
      (Fintype.card (MultIdx r T) : ℤ) * |((x : ℤ))|
  · apply Finset.sum_congr rfl
    intro x _
    show (∑ y : MultIdx r T, |(((x : ℤ)))|) = (Fintype.card (MultIdx r T) : ℤ) * |((x : ℤ))|
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · rw [← Finset.mul_sum]
    have hsub : (∑ x : {s : ℤ // s ∈ Finset.Icc (-(S:ℤ)) S}, |((x:ℤ))|)
        = ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), |s| :=
      (Finset.sum_subtype (Finset.Icc (-(S:ℤ)) (S:ℤ)) (fun x => Iff.rfl) (fun a => |a|)).symm
    rw [hsub, sum_abs_Icc]
    push_cast
    ring

end Work.BW
