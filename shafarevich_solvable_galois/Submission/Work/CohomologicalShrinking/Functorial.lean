/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Functoriality of the refined filtration and its graded pieces

Schmidt–Wingberg's Proposition 5 says that the canonical maps
`θ_τ(d) : (F(d)/F(d)^2)^{⊗j} ↠ E(d,τ)` are *natural in `d`*: for a **surjective** `G`-operator
homomorphism `ψ : F(m) → F(n)` the induced map on the graded pieces satisfies
`θ_τ(m) ≫ ψ_* = (ψ̄^{⊗j}) ≫ θ_τ(n)`.  This file provides the induced maps `ψ_*`
(`gradedMap`) and `ψ̄` (`quotMap`).

Only *surjective* homomorphisms of groups are treated (that is the case used by the shrinking
procedure); then `ψ(P_{(i,j)}) = Q_{(i,j)}`, because the descending `p`-central series and the
descending central series are both preserved by surjections.

## Main results

* `Work.CohomologicalShrinking.map_refinedTerm_eq_of_surjective` :
  `ψ(P_{(i,j)}) = Q_{(i,j)}` for surjective `ψ`.
* `Work.CohomologicalShrinking.gradedMapMul` / `gradedMapAdd` / `gradedMapLin` : the induced
  maps on the graded pieces (`→*`, `→+`, `→ₗ[𝔽_p]`).
* `Work.CohomologicalShrinking.pCentralMapMul` / `quotMapMul` and the `𝔽_p`-linear
  `quotMapLin` : the induced maps `F(m)/F(m)^2 → F(n)/F(n)^2`.
* `Work.CohomologicalShrinking.gradedMapMul_smul`, `gradedMapAdd_smul` : these maps commute with
  the actions of `G` when `ψ` does.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Defs
import Submission.Work.CohomologicalShrinking.ModSquare
import Submission.Work.CohomologicalShrinking.Refined
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-! ## Surjections preserve the two series -/

section MapLe

variable {P Q : Type*} [Group P] [Group Q]

/-- A surjective homomorphism maps the descending central series onto the descending central
series of the target. -/
theorem map_centralSeries_eq_of_surjective (ψ : P →* Q) (hψ : Function.Surjective ψ) (j : ℕ) :
    (centralSeries P j).map ψ = centralSeries Q j := by
  rw [centralSeries, centralSeries, Subgroup.map_lowerCentralSeries,
    Subgroup.map_top_of_surjective ψ hψ]

theorem map_refinedTerm_le_of_surjective (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ)
    (i j : ℕ) : (refinedTerm p P i j).map ψ ≤ refinedTerm p Q i j := by
  have h1 : (pSeries p P i).map ψ = pSeries p Q i :=
    Work.Shrinking.map_pCentralSeries_surjective p ψ hψ (i - 1)
  have h2 : (pSeries p P (i + 1)).map ψ = pSeries p Q (i + 1) :=
    Work.Shrinking.map_pCentralSeries_surjective p ψ hψ i
  have h3 : (centralSeries P j).map ψ = centralSeries Q j :=
    map_centralSeries_eq_of_surjective ψ hψ j
  have h4 : ((pSeries p P i ⊓ centralSeries P j) ⊔ pSeries p P (i + 1)).map ψ
      ≤ (pSeries p Q i ⊓ centralSeries Q j) ⊔ pSeries p Q (i + 1) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · refine le_trans (Subgroup.map_inf_le _ _ _) ?_
      rw [h1, h3]
      exact le_sup_left
    · rw [h2]
      exact le_sup_right
  rw [refinedTerm, refinedTerm]
  exact h4

end MapLe

/-! ## The induced maps on the graded pieces -/

section Induced

variable {P Q : Type*} [Group P] [Group Q]

/-- The homomorphism `refinedTerm p P i j →* refinedTerm p Q i j` induced by a surjective
homomorphism `ψ : P →* Q`. -/
noncomputable def refinedMap (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) (i j : ℕ) :
    refinedTerm p P i j →* refinedTerm p Q i j :=
  (ψ.comp (refinedTerm p P i j).subtype).codRestrict (refinedTerm p Q i j)
    (fun x => map_refinedTerm_le_of_surjective p ψ hψ i j (Subgroup.mem_map_of_mem ψ x.2))

@[simp] theorem refinedMap_coe (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) (i j : ℕ)
    (x : refinedTerm p P i j) :
    ((refinedMap p ψ hψ i j x : refinedTerm p Q i j) : Q) = ψ x := rfl

/-- The homomorphism of the graded pieces induced by a surjective `ψ`. -/
noncomputable def gradedMapMul (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) (i j : ℕ) :
    refinedQuotient p P i j →* refinedQuotient p Q i j :=
  QuotientGroup.map _
    ((refinedTerm p Q (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p Q i j))
    (refinedMap p ψ hψ i j) (by
      intro x hx
      change refinedMap p ψ hψ i j x ∈
        (refinedTerm p Q (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p Q i j)
      rw [Subgroup.mem_subgroupOf, refinedMap_coe]
      rw [Subgroup.mem_subgroupOf] at hx
      exact map_refinedTerm_le_of_surjective p ψ hψ (tauSucc i j).1 (tauSucc i j).2
        (Subgroup.mem_map_of_mem ψ hx))

@[simp] theorem gradedMapMul_of (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) (i j : ℕ)
    (x : refinedTerm p P i j) :
    gradedMapMul p ψ hψ i j (QuotientGroup.mk'
      ((refinedTerm p P (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p P i j)) x)
      = QuotientGroup.mk' _ (refinedMap p ψ hψ i j x) :=
  QuotientGroup.map_mk' _ _ (refinedMap p ψ hψ i j) _ x

/-- The homomorphism of the quotients of the descending `p`-central series induced by a
surjective homomorphism of groups. -/
noncomputable def pCentralMapMul (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) (n : ℕ) :
    Work.Shrinking.pCentralQuotient p P n →* Work.Shrinking.pCentralQuotient p Q n :=
  let f : ↥(Work.Shrinking.pCentralSeries p P n) →* ↥(Work.Shrinking.pCentralSeries p Q n) :=
    { toFun := fun x => ⟨ψ (x : P), by
        rw [← Work.Shrinking.map_pCentralSeries_surjective p ψ hψ n]
        exact Subgroup.mem_map_of_mem ψ x.2⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (map_mul ψ (x : P) (y : P)) }
  QuotientGroup.map _
    ((Work.Shrinking.pCentralSeries p Q (n + 1)).subgroupOf (Work.Shrinking.pCentralSeries p Q n))
    f (by
      intro x hx
      change f x ∈ (Work.Shrinking.pCentralSeries p Q (n + 1)).subgroupOf
        (Work.Shrinking.pCentralSeries p Q n)
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hx
      show ψ (x : P) ∈ Work.Shrinking.pCentralSeries p Q (n + 1)
      rw [← Work.Shrinking.map_pCentralSeries_surjective p ψ hψ (n + 1)]
      exact Subgroup.mem_map_of_mem ψ hx)

/-- The homomorphism `F(m)/F(m)^2 → F(n)/F(n)^2` induced by a surjective homomorphism of
operator groups. -/
noncomputable def quotMapMul (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) :
    Work.Shrinking.pCentralQuotient p P 0 →* Work.Shrinking.pCentralQuotient p Q 0 :=
  pCentralMapMul p ψ hψ 0

/-- The additive form of the induced map on the graded pieces. -/
noncomputable def gradedMapAdd (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) (i j : ℕ) :
    Additive (refinedQuotient p P i j) →+ Additive (refinedQuotient p Q i j) where
  toFun x := Additive.ofMul (gradedMapMul p ψ hψ i j (Additive.toMul x))
  map_zero' := by rw [toMul_zero, map_one, ofMul_one]
  map_add' := by intro a b; rw [toMul_add, map_mul, ofMul_mul]

/-- The `𝔽_p`-linear map on the graded pieces induced by a surjective homomorphism. -/
noncomputable def gradedMapLin (p : ℕ) (ψ : P →* Q) (hψ : Function.Surjective ψ) (i j : ℕ) :
    Additive (refinedQuotient p P i j) →ₗ[ZMod p] Additive (refinedQuotient p Q i j) :=
  AddMonoidHom.toZModLinearMap p (gradedMapAdd p ψ hψ i j)

/-- The additive form of the induced map `F(m)/F(m)^2 → F(n)/F(n)^2`. -/
noncomputable def quotMapAdd (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) : squareQuotient p G m →+ squareQuotient p G n where
  toFun x := Additive.ofMul (pCentralMapMul p ψ hψ 0 (Additive.toMul x))
  map_zero' := by rw [toMul_zero, map_one, ofMul_one]
  map_add' := by intro a b; rw [toMul_add, map_mul, ofMul_mul]

/-- The `𝔽_p`-linear form of the induced map `F(m)/F(m)^2 → F(n)/F(n)^2`. -/
noncomputable def quotMapLin (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) : squareQuotient p G m →ₗ[ZMod p] squareQuotient p G n :=
  AddMonoidHom.toZModLinearMap p (quotMapAdd p G ψ hψ)

end Induced

end Work.CohomologicalShrinking
