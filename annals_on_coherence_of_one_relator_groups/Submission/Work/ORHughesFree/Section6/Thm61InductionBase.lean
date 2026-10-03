/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The induction of [JZLA20, Theorem 6.1] — first steps

The main induction proving that every non-zero element of the division closure `D_{K[G],U}` is a
unit (see `PlanInduction.md` for the design) is `isUnit_of_mem_divisionClosure` in
`Section6/Thm61InductionMain.lean`.  This file contains the two elementary steps it uses:

* `treeG_eq_zero_iff` : `Tree_G(a) = 0` iff `a = 0`;
* `isUnit_of_treeG_eq_one` : an element of `G`-complexity `1` is `φ (unitOf u)` for some group
  element `u`, hence a unit of `D_{K[G],U}`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.TreeG
import Submission.Work.ORHughesFree.Section6.imElem_mul
import Submission.Work.ORHughesFree.Section6.imElem_isUnit
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Tree.order_alg

set_option autoImplicit false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- **`Tree_G(a) = 0` if and only if `a = 0`** ([JZLA20, Lemma 4.3(i)] transported to the
`G`-complexity): the complexity is realisable, and a realiser of complexity `0` is `0`
(`Rat.treeOfRat_eq_zero_iff`); conversely `0` has a realiser of complexity `0`. -/
theorem treeG_eq_zero_iff (φ : MonoidAlgebra K G →+* U)
    (a : ↥(divisionClosure (Set.range φ))) : treeG φ a = 0 ↔ a = 0 := by
  constructor
  · intro h
    obtain ⟨α, hα, ht⟩ := (treeG_spec φ a).1
    rw [h] at ht
    rw [← hα, (Rat.treeOfRat_eq_zero_iff (Kˣ × G) α).mp ht, map_zero]
  · rintro rfl
    refine Tree.le_antisymm ?_ (Tree.le_zero (treeG φ 0))
    have h := (treeG_spec φ (0 : ↥(divisionClosure (Set.range φ)))).2 (0 : RatU (Kˣ × G))
      (map_zero (Phi φ))
    rwa [Rat.treeOfRat_zero] at h

/-- **An element of `G`-complexity `1` is a unit.**  By `treeG_spec` such an element has a realiser
of complexity `1`, which by `Rat.treeOfRat_eq_one_iff` is `ofGroup u`; its image is
`imElem φ u = φ (unitOf u)`, with inverse `imElem φ u⁻¹`. -/
theorem isUnit_of_treeG_eq_one (φ : MonoidAlgebra K G →+* U)
    (a : ↥(divisionClosure (Set.range φ))) (h : treeG φ a = 1) :
    ∃ y : ↥(divisionClosure (Set.range φ)), a * y = 1 ∧ y * a = 1 := by
  obtain ⟨α, hα, ht⟩ := (treeG_spec φ a).1
  rw [h] at ht
  obtain ⟨u, rfl⟩ := (Rat.treeOfRat_eq_one_iff α).mp ht
  have ha : a = imElem φ u := by
    rw [← hα, Phi_ofGroup]
  have hone : imElem φ (1 : Kˣ × G) = 1 := by
    apply Subtype.ext
    show φ (unitOf (1 : Kˣ × G)) = 1
    rw [unitOf_one, map_one]
  refine ⟨imElem φ u⁻¹, ?_, ?_⟩
  · rw [ha, ← imElem_mul, mul_inv_cancel, hone]
  · rw [ha, ← imElem_mul, inv_mul_cancel, hone]

end Work.ORHughesFree.Section6
