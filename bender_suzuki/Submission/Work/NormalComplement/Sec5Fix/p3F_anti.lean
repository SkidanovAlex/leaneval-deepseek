import Mathlib
import Submission.Work.NormalComplement.Sec5Fix.Prelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `p3F_anti` — `X ≤ Y ⟹ O^{2'}(C_G(Y)) ≤ O^{2'}(C_G(X))`

`Work.ThreePoints.p3F X = O^{2'}(C_G(X))`, viewed as a subgroup of the ambient group `G`
(Peterfalvi I Ch. II §4 Prop. 3).  This file proves the antitonicity in `X`: enlarging the
subgroup `X` shrinks its centralizer, hence shrinks the odd residual of the centralizer.

The mathematical content is that `O^{2'}` is monotone under arbitrary homomorphisms: for any
monoid homomorphism `f : G →* H`, the image of `O^{2'}(G)` lies in `O^{2'}(H)`.  The reason is
that if `K = O^{2'}(H) ◁ H` has odd order quotient, then `f⁻¹(K) ◁ G` has odd index, so
minimality of `O^{2'}(G)` gives `O^{2'}(G) ≤ f⁻¹(K)`, i.e. `f(O^{2'}(G)) ≤ K`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.Sec5Fix

/-- `O^{2'}` is monotone with respect to an arbitrary homomorphism: the image of the odd
residual of `G` lies in the odd residual of `H`.

The proof pulls back `O^{2'}(H)`: its preimage is a normal subgroup of `G` of odd index
(the index divides the odd index of `O^{2'}(H)`), so it contains `O^{2'}(G)`. -/
theorem oddResidual_map_le {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) : (oddResidual G).map f ≤ oddResidual H := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hH := Work.Reductions.oddResidual_basic (G := H)
  haveI : (oddResidual H).Normal := hH.1
  have hcomap_normal : (Subgroup.comap f (oddResidual H)).Normal := hH.1.comap f
  have hcomap_odd : Odd (Subgroup.comap f (oddResidual H)).index := by
    rw [Subgroup.index_comap]
    exact Odd.of_dvd_nat hH.2.1
      (Subgroup.relIndex_dvd_index_of_normal (oddResidual H) f.range)
  exact (Work.Reductions.oddResidual_basic (G := G)).2.2.1
    (Subgroup.comap f (oddResidual H)) hcomap_normal hcomap_odd hy

/-- `p3F X = O^{2'}(C_G(X))` is antitone in `X`: if `X ≤ Y` then `p3F Y ≤ p3F X`. -/
theorem p3F_anti {G : Type} [Group G] [Finite G] {X Y : Subgroup G} (h : X ≤ Y) :
    Work.ThreePoints.p3F Y ≤ Work.ThreePoints.p3F X := by
  intro g hg
  rw [Work.ThreePoints.mem_p3F] at hg ⊢
  obtain ⟨c, hc, hcg⟩ := hg
  have hC : Subgroup.centralizer (Y : Set G) ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.centralizer_le h
  have hmap := oddResidual_map_le (Subgroup.inclusion hC)
  have hc' : Subgroup.inclusion hC c ∈ oddResidual ↥(Subgroup.centralizer (X : Set G)) :=
    hmap (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
  exact ⟨Subgroup.inclusion hC c, hc', by rw [Subgroup.coe_inclusion, hcg]⟩

end Work.NormalComplement.Sec5Fix
