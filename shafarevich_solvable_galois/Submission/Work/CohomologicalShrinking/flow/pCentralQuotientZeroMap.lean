/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Functoriality of the bottom graded piece `P/P^p[P,P]`

For an *arbitrary* group homomorphism `ψ : P →* Q` the descending `p`-central series of `P`
is carried into that of `Q`: `ψ(P_n) ≤ Q_n`.  The reason is that on the first step
`pCentralStep p ⊤ = (⊤)^p [⊤, ⊤]` the `p`-th power subgroup and the commutator subgroup are
both mapped inside the corresponding subgroups of `Q`, and then one proceeds by induction,
so that no surjectivity hypothesis on `ψ` is needed.

In particular the induced map `P/P_1 → Q/Q_1` on the bottom graded piece -- the `n = 0` case
`φ : F/P^p[P,P] → F'/P'^p[P',P']` -- exists for every `ψ`, and we record that it is computed by
`ψ` on representatives.  This is the raw functoriality statement underlying the naturality of
the maps used in the shrinking procedure.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Shrinking
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.flow

open Work.Shrinking

/-! ## The `p`-th powers and the commutators are functorial -/

/-- The `p`-th power subgroup of `H` is mapped into the `p`-th power subgroup of the image of
`H`. -/
theorem map_powSubgroup_le (p : ℕ) {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q)
    (H : Subgroup P) : (powSubgroup p H).map ψ ≤ powSubgroup p (H.map ψ) := by
  unfold powSubgroup
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨ψ z, Subgroup.mem_map_of_mem ψ hz, by rw [map_pow]⟩

/-- The `p`-th power subgroup is monotone. -/
theorem powSubgroup_mono (p : ℕ) {P : Type*} [Group P] {H K : Subgroup P} (h : H ≤ K) :
    powSubgroup p H ≤ powSubgroup p K := by
  unfold powSubgroup
  exact Subgroup.closure_mono (Set.image_mono h)

/-- The commutator subgroup `[H, ⊤]` is mapped into `[ψ(H), ⊤]`. -/
theorem map_commutator_top_le {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q)
    (H : Subgroup P) : (⁅H, ⊤⁆ : Subgroup P).map ψ ≤ ⁅H.map ψ, ⊤⁆ := by
  rw [Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_rfl le_top

/-! ## An arbitrary homomorphism preserves the descending `p`-central series -/

/-- The descending `p`-central series of `P` is carried into that of `Q` by an arbitrary group
homomorphism.  No surjectivity is required. -/
theorem map_pCentralSeries_le (p : ℕ) {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q) (n : ℕ) :
    (pCentralSeries p P n).map ψ ≤ pCentralSeries p Q n := by
  induction n with
  | zero =>
      rw [pCentralSeries_zero, pCentralSeries_zero]
      exact le_top
  | succ n ih =>
      rw [pCentralSeries_succ, pCentralSeries_succ, pCentralStep, pCentralStep,
        Subgroup.map_sup]
      refine sup_le ?_ ?_
      · exact (map_powSubgroup_le p ψ (pCentralSeries p P n)).trans
          ((powSubgroup_mono p ih).trans le_sup_left)
      · exact (map_commutator_top_le ψ (pCentralSeries p P n)).trans
          ((Subgroup.commutator_mono ih le_rfl).trans le_sup_right)

/-! ## The induced map on `P/P^p[P,P]` -/

/-- For every group homomorphism `ψ : P →* Q` there is a homomorphism of the bottom graded
pieces `P/P^p[P,P] → Q/Q^p[Q,Q]` sending the class of `x` to the class of `ψ x`. -/
theorem pCentralQuotientZeroMap (p : ℕ) {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q) :
    ∃ φ : Work.Shrinking.pCentralQuotient p P 0 →* Work.Shrinking.pCentralQuotient p Q 0,
      ∀ x : Work.Shrinking.pCentralSeries p P 0,
        φ (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ ⟨ψ x, Subgroup.mem_top x⟩ := by
  let f : pCentralSeries p P 0 →* pCentralSeries p Q 0 :=
    { toFun := fun x => ⟨ψ x, Subgroup.mem_top x⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (map_mul ψ (x : P) (y : P)) }
  refine ⟨QuotientGroup.map
    ((pCentralSeries p P 1).subgroupOf (pCentralSeries p P 0))
    ((pCentralSeries p Q 1).subgroupOf (pCentralSeries p Q 0)) f ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    exact map_pCentralSeries_le p ψ 1 (Subgroup.mem_map_of_mem ψ hx)
  · intro x
    rw [QuotientGroup.map_mk']
    rfl

end Work.CohomologicalShrinking.flow
