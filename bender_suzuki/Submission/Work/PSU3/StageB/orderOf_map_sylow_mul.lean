import Mathlib
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageA.orderOfMapEq
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.PSU3.RankOne.H16

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-
# Step 4 transfer (iii): the structure identity of `F = O^{2'}(C_G(P))` is that of `G`

Ch. V §2 Lemma 1 c) says the order of `s * t` is unchanged when passing to `F/N(F)`.  Here `F` is
carried into `Y` by an epimorphism `φ` with central kernel, so with `x, y ∈ ↥F` mapping to the
distinguished involution `s` and to `t`:

    orderOf (φ x * φ y) = orderOf (s * t).

Consequently `orderOf (s_Y * w_Y) = orderOf (s * t)` for the split rank-one datum of
`Y = F/Z(F)`, which is what makes steps 2–3 (the ambient order `orderOf (s*t) = 3`, the local
trichotomy) meaningful for `Y` as well.

Route: `orderOf x = orderOf s = 2` and `orderOf y = orderOf t = 2` by `Subgroup.orderOf_coe`;
`x * x = 1`, `y * y = 1`; `orderOf (x * y) = orderOf (s * t)` (again `Subgroup.orderOf_coe`), which
is odd by `Work.ThmF.Bender.twoInvolutionsOdd` (from `H` strongly embedded, `s ∈ Q ≤ H`,
`orderOf s = 2`, `t² = 1` (`hS.split.invol`), `t ∉ H`).  Then `Work.PSU3.StageA.orderOfMapEq` —
which needs only `φ.ker ≤ Z(↥F)` plus the two involutions and the odd order — gives
`orderOf (φ (x * y)) = orderOf (x * y)`, and `map_mul` finishes.  (The `r`/structure-identity data
is not needed; the pattern is the one already used at `StageA/lemma2cHig.lean:493`.)
-/
theorem orderOf_map_sylow_mul {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {P : Subgroup G} {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    {Y : Type} [Group Y]
    {φ : ↥(Work.PSU3.StageB.centralizerOddResidual P) →* Y}
    (hker : φ.ker ≤ Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P))
    (x y : ↥(Work.PSU3.StageB.centralizerOddResidual P))
    (hx : (x : G) = s) (hy : (y : G) = t) :
    orderOf (φ x * φ y) = orderOf (s * t) := by
  -- The split rank-one data of `hS`.
  have hH := hS.split.stronglyEmbedded
  have hsH : s ∈ H := hS.split.le hs
  have ht2 : orderOf t = 2 := hS.split.invol
  have htH : t ∉ H := hS.split.not_mem
  -- `s * t` has odd order.
  have hodd_st : Odd (orderOf (s * t)) :=
    Work.ThmF.Bender.twoInvolutionsOdd hH hsH hs2 ht2 htH
  -- `x` and `y` are the lifts of `s` and `t`, hence `x * y` is the lift of `s * t`.
  have hxy : ((x * y : ↥(centralizerOddResidual P)) : G) = s * t := by
    rw [Subgroup.coe_mul, hx, hy]
  have hxy_ord : orderOf (x * y : ↥(centralizerOddResidual P)) = orderOf (s * t) := by
    rw [← hxy, Subgroup.orderOf_coe]
  -- Both `x` and `y` are involutions.
  have hxord : orderOf x = 2 := by rw [← Subgroup.orderOf_coe x, hx, hs2]
  have hyord : orderOf y = 2 := by rw [← Subgroup.orderOf_coe y, hy, ht2]
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hxord] at h
    simpa [pow_two] using h
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hyord] at h
    simpa [pow_two] using h
  have hodd_xy : Odd (orderOf (x * y : ↥(centralizerOddResidual P))) := by
    rw [hxy_ord]; exact hodd_st
  -- `φ` preserves the order of `x * y` because its kernel is central.
  have hmap : orderOf (φ (x * y)) = orderOf (x * y : ↥(centralizerOddResidual P)) :=
    Work.PSU3.StageA.orderOfMapEq (φ := φ) hker hx2 hy2 hodd_xy
  rw [← map_mul, hmap, hxy_ord]

end Work.PSU3.StageB
