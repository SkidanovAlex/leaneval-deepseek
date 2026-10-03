/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The rational operation on a division closure, and the image of `Kˣ × G`

[JZLA20, §4.3]: on the division closure `D_{R,S}` of a subring `R` of a ring `S` the rational
operation is `a⋄ = a⁻¹` if `a` is invertible in `D_{R,S}`, and `a⋄ = 0` otherwise.  This file
contains the definitions of that operation (`ratOpClosure`) and of the image `imElem φ u` in
`divisionClosure (Set.range φ)` of the group-like unit `λ·g = unitOf (λ, g)` of `K[G]`
(`Section6/UnitOf.lean`).

Their API lives in the files `Section6/ratOpClosure_smul.lean`, `Section6/ratOpClosure_spec.lean`
and `Section6/imElem.lean`, and is consumed by `Section6/RatStruct.lean` (the rational
`Kˣ × G`-semiring structure on `D_{R,S}` together with the universal morphism `Φ` of
[JZLA20, Lemma 4.2] and its surjectivity).
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.UnitOf
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.Rat.RTerm

set_option autoImplicit false

namespace Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- **The rational operation on a subring** `D ≤ U`: the inverse of `x` if `x` is a unit of `D`,
and `0` otherwise ([JZLA20, §4.3]). -/
noncomputable def ratOpClosure (D : Subring U) (x : ↥D) : ↥D := by
  classical
  exact if h : IsUnit x then ↑h.unit⁻¹ else 0

/-- **`⋄ 0 = 0`** for the rational operation of a subring — the axiom
`RationalUSemiring.ratOp_zero`.  No non-triviality is needed: either `0` is not a unit, or the ring
is trivial. -/
theorem ratOpClosure_zero (D : Subring U) : ratOpClosure D 0 = 0 := by
  classical
  unfold ratOpClosure
  by_cases h : IsUnit (0 : ↥D)
  · rw [dif_pos h]
    have h01 : (1 : ↥D) = 0 := by
      have h1 := Units.mul_inv h.unit
      rw [show (h.unit : ↥D) = 0 from h.unit_spec, zero_mul] at h1
      exact h1.symm
    haveI : Subsingleton ↥D := ⟨fun a b => by
      have ha : a = 0 := by
        rw [← mul_one a, h01, mul_zero]
      have hb : b = 0 := by
        rw [← mul_one b, h01, mul_zero]
      rw [ha, hb]⟩
    exact Subsingleton.elim _ _
  · rw [dif_neg h]

/-- The image in `divisionClosure (Set.range φ)` of the group-like unit `λ · g` of `K[G]`. -/
noncomputable def imElem (φ : MonoidAlgebra K G →+* U) (u : Kˣ × G) :
    ↥(divisionClosure (Set.range φ)) :=
  ⟨φ (unitOf u), subset_divisionClosure _ ⟨unitOf u, rfl⟩⟩

end Work.ORHughesFree
