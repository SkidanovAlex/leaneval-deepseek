/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `G`-equivariance of the induced map `F(m)/F(m)² → F(n)/F(n)²`

The map `quotMapAdd p G ψ hψ : F(m)/F(m)² → F(n)/F(n)²` induced by a surjective `G`-operator
homomorphism `ψ : F(m) → F(n)` is `G`-equivariant.  This is the `F(d)/F(d)²` case of the
naturality of the refined filtration (Proposition 5 of Schmidt–Wingberg), and is used when the
shrinking procedure transports obstructions along `ψ`.

The proof reduces the statement to the general fact that `QuotientGroup.map` is natural with
respect to the automorphisms `quotAut` induced by an action of `G` on the ambient groups.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.functorial

open Work.Shrinking

set_option maxHeartbeats 800000

/-! ## Naturality of the descended action on a subquotient

Let `G` act on `P` and `Q` by automorphisms and let `f : H →* H'` be a homomorphism between
invariant subgroups.  If `f` intertwines the actions (through `subAut`), then the induced map
`H/K → H'/K'` between subquotients intertwines the descended actions (`quotAut`). -/

theorem quotAut_map {G P Q : Type*} [Group G] [Group P] [Group Q]
    [MulDistribMulAction G P] [MulDistribMulAction G Q]
    (H : Subgroup P) (K : Subgroup P) [K.Normal]
    (H' : Subgroup Q) (K' : Subgroup Q) [K'.Normal]
    (f : H →* H')
    (hH : ∀ g, H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H)
    (hK : ∀ g, K.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = K)
    (hH' : ∀ g, H'.map (MulDistribMulAction.toMulAut G Q g).toMonoidHom = H')
    (hK' : ∀ g, K'.map (MulDistribMulAction.toMulAut G Q g).toMonoidHom = K')
    (hfK : K.subgroupOf H ≤ (K'.subgroupOf H').comap f)
    (hf : ∀ (g : G) (x : H), f (subAut H g (hH g) x) = subAut H' g (hH' g) (f x))
    (g : G) (x : H ⧸ K.subgroupOf H) :
    QuotientGroup.map (K.subgroupOf H) (K'.subgroupOf H') f hfK
        (quotAut H K g (hH g) (hK g) x)
      = quotAut H' K' g (hH' g) (hK' g)
        (QuotientGroup.map (K.subgroupOf H) (K'.subgroupOf H') f hfK x) := by
  refine QuotientGroup.induction_on x ?_
  intro y
  change QuotientGroup.map (K.subgroupOf H) (K'.subgroupOf H') f hfK
      (quotAut H K g (hH g) (hK g) (QuotientGroup.mk' (K.subgroupOf H) y))
    = quotAut H' K' g (hH' g) (hK' g)
      (QuotientGroup.map (K.subgroupOf H) (K'.subgroupOf H') f hfK
        (QuotientGroup.mk' (K.subgroupOf H) y))
  simp only [quotAut_mk, QuotientGroup.map_mk']
  exact congrArg (QuotientGroup.mk' (K'.subgroupOf H')) (hf g y)

/-! ## Equivariance of the map on the `p`-central series -/

/-- The map on the terms of the descending `p`-central series induced by a surjective
homomorphism `ψ : P →* Q`, written out explicitly (it is the `let`-bound map inside
`pCentralMapMul`). -/
noncomputable def pCentralSeriesMap {P Q : Type*} [Group P] [Group Q]
    (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) (n : ℕ) :
    ↥(pCentralSeries p P n) →* ↥(pCentralSeries p Q n) where
  toFun x := ⟨ψ (x : P), by
    rw [← map_pCentralSeries_surjective p ψ hψ n]
    exact Subgroup.mem_map_of_mem ψ x.2⟩
  map_one' := Subtype.ext (map_one ψ)
  map_mul' x y := Subtype.ext (map_mul ψ (x : P) (y : P))

/-- The map `P_n/P_{n+1} → Q_n/Q_{n+1}` induced by a surjective `G`-equivariant homomorphism
`ψ : P →* Q` is `G`-equivariant. -/
theorem pCentralMapMul_smul (p : ℕ) {G P Q : Type*} [Group G] [Group P] [Group Q]
    [MulDistribMulAction G P] [MulDistribMulAction G Q]
    (ψ : P →* Q) (hψ : Function.Surjective ψ)
    (hψG : ∀ (g : G) (x : P), ψ (g • x) = g • ψ x) (n : ℕ) (g : G)
    (x : pCentralQuotient p P n) :
    pCentralMapMul p ψ hψ n (g • x) = g • pCentralMapMul p ψ hψ n x := by
  show pCentralMapMul p ψ hψ n
      (quotAut (pCentralSeries p P n) (pCentralSeries p P (n+1)) g
        (map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) n)
        (map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) (n+1)) x)
    = quotAut (pCentralSeries p Q n) (pCentralSeries p Q (n+1)) g
        (map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G Q g) n)
        (map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G Q g) (n+1))
        (pCentralMapMul p ψ hψ n x)
  refine quotAut_map (pCentralSeries p P n) (pCentralSeries p P (n+1))
    (pCentralSeries p Q n) (pCentralSeries p Q (n+1))
    (pCentralSeriesMap p ψ hψ n)
    (fun g => map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) n)
    (fun g => map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) (n+1))
    (fun g => map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G Q g) n)
    (fun g => map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G Q g) (n+1))
    ?_ ?_ g x
  · intro y hy
    change pCentralSeriesMap p ψ hψ n y ∈
      (pCentralSeries p Q (n + 1)).subgroupOf (pCentralSeries p Q n)
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hy
    show ψ (y : P) ∈ pCentralSeries p Q (n + 1)
    rw [← map_pCentralSeries_surjective p ψ hψ (n + 1)]
    exact Subgroup.mem_map_of_mem ψ hy
  · intro h y
    refine Subtype.ext ?_
    change ψ (h • (y : P)) = h • ψ (y : P)
    exact hψG h (y : P)

/-! ## The target lemma -/

/-- The induced map `F(m)/F(m)² → F(n)/F(n)²` commutes with the action of `G`. -/
theorem quotMapAdd_smul (p : ℕ) {G : Type*} [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ)
    (hψG : ∀ (g : G) (x : Work.Shrinking.freeOperatorGroup G m), ψ (g • x) = g • ψ x)
    (g : G) (z : squareQuotient p G m) :
    quotMapAdd p G ψ hψ (g • z) = g • quotMapAdd p G ψ hψ z := by
  change Additive.ofMul
      (pCentralMapMul p ψ hψ 0 (g • Additive.toMul z))
    = Additive.ofMul
      (g • pCentralMapMul p ψ hψ 0 (Additive.toMul z))
  rw [pCentralMapMul_smul p ψ hψ hψG 0 g (Additive.toMul z)]

end Work.CohomologicalShrinking.functorial
