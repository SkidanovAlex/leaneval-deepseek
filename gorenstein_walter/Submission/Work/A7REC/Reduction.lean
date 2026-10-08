/-
Area A7REC: the reductions of the area.

`A7RecProp` is *equivalent* to the existence of an index-`7` subgroup in a group satisfying the
`A₇` hypotheses, by the already proved `Work.A7.mulEquiv_A7_of_index_seven` (area `A7` of the
project).  This file records that reduction, plus the `|H| = 360` form in which the
character-theoretic argument of Suzuki 1959 §8 delivers the subgroup.
-/
import Submission.Work.A7REC.IndexSeven

open scoped MatrixGroups

namespace Work.A7REC

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- `|G| = 2520`, so a subgroup of order `360` has index `7`. -/
theorem index_eq_seven_of_card_eq_360 (ctx : A7RecCtx G) {H : Subgroup G}
    (hH : Nat.card H = 360) : H.index = 7 := by
  have h := Subgroup.card_mul_index H
  rw [hH, ctx.hcard] at h
  have h7 : 360 * 7 = (2520 : ℕ) := by norm_num
  exact Nat.eq_of_mul_eq_mul_left (show 0 < 360 by norm_num) (by rw [h7]; exact h)

/-- The subgroup-of-order-`360` form of the residual statement implies the index-`7` form. -/
theorem A7IndexSevenProp_of_A7Subgroup360Prop (h : A7Subgroup360Prop) : A7IndexSevenProp := by
  intro G _ _ ctx
  obtain ⟨H, hH⟩ := h G ctx
  exact ⟨H, index_eq_seven_of_card_eq_360 ctx hH⟩

/-- **The Suzuki-reduction of the deliverable.**  If every group satisfying the `A₇` hypotheses
has a subgroup of index `7`, then `A7RecProp` holds. -/
theorem a7RecProp_of_indexSeven (h : A7IndexSevenProp) : A7RecProp := by
  intro G _ _ hsimple hcard S hSdih z U V hzS hz2 hzcen hCz hUcard hUnorm hVdef hV4 hcross
    hNUV hNUcard
  haveI : IsSimpleGroup G := hsimple
  let ctx : A7RecCtx G :=
    { simple := hsimple, hcard := hcard, S := S, hSdih := hSdih, z := z, hzS := hzS, hz2 := hz2,
      hzcen := hzcen, U := U, hCz := hCz, hUcard := hUcard, hUnorm := hUnorm, V := V,
      hVdef := hVdef, hV4 := hV4, hcross := hcross, hNUV := hNUV, hNUcard := hNUcard }
  obtain ⟨H, hH⟩ := h G ctx
  exact mulEquiv_A7_of_index_seven G hcard H hH

/-- `A7RecProp` from the subgroup-of-order-`360` residual statement. -/
theorem a7RecProp_of_subgroup360 (h : A7Subgroup360Prop) : A7RecProp :=
  a7RecProp_of_indexSeven (A7IndexSevenProp_of_A7Subgroup360Prop h)

end Work.A7REC
