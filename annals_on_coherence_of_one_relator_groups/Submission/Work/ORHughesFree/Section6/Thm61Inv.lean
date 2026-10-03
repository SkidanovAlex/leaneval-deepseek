/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The induction hypothesis of [JZLA20, Proposition 5.1] from the induction on `Tree_G`

This file isolates one step of the induction of [JZLA20, Theorem 6.1]: the verification of
[JZLA20, Proposition 5.1]'s hypothesis `Prop51Inv` at the element `e aH ∈ D_{H,P}`.

The mathematical content is the comparison of complexities: for `c ∈ D_{H,P}` with
`Tree_H(c) ≤ Tree_H(e aH)` and `Tree_H(c) ≠ Tree_H(e aH)`, the element `b = e⁻¹ c ∈ D_{H,U}` has
`Tree_G(incl b) < Tree_G a`, because

  `Tree_G(incl b) ≤ Tree_H(b) = Tree_H(c) < Tree_H(e aH) = Tree_G a`,

using `treeG_le_treeG_of_subgroup`, the identification `Thm61Step.e_tree_local`
(`Tree_H(c) = Tree_{K[↥H]}(b)`) and the hypothesis `hTHeq : Tree_H(e aH) = Tree_G a`.  The
induction hypothesis then makes `incl b` a unit of `D_{K[G],U}`, and its inverse lies in
`D_{K[↥H],U}` by `DivisionClosure.inverse_mem_divisionClosure`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.Thm61Step
import Submission.Work.ORHughesFree.Section6.Thm61InductionAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- **`Prop51Inv` at `e aH` from the induction hypothesis on `Tree_G`.** -/
theorem prop51Inv_of_stepData
    (φ : MonoidAlgebra K G →+* U) {H : Subgroup G}
    {P : Type} [Ring P] {DN : Subring P} [MulSemiringAction (Multiplicative ℤ) ↥DN]
    (data : Prop51Data (Kˣ × H) P DN)
    (e : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) ≃+* ↥data.DH)
    (e_Phi : ∀ β : RatU (Kˣ × H),
      e ((Phi (φ.comp (inducedMapRing (K := K) H))) β) = ⟨data.Φ β, data.map_mem β⟩)
    (aH : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))))
    (a : ↥(divisionClosure (Set.range φ)))
    (hTHeq : data.treeH (e aH) = treeG φ a)
    (ih : ∀ b : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))),
        b ≠ 0 → Tree.lt (treeG φ (inclSub φ H b)) (treeG φ a) → IsUnit (inclSub φ H b)) :
    Prop51Inv data (e aH) := by
  intro c hc hc0 hle hne
  set b : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) :=
    e.symm ⟨c, hc⟩ with hbdef
  have he_b : e b = ⟨c, hc⟩ := e.apply_symm_apply ⟨c, hc⟩
  have hc_eq : ((e b : ↥data.DH) : P) = c := by rw [he_b]
  have hb_tree : data.treeH c = treeG (φ.comp (inducedMapRing (K := K) H)) b := by
    rw [← hc_eq]
    exact Thm61Step.e_tree_local e_Phi b
  have hb0 : b ≠ 0 := by
    intro h0
    refine hc0 ?_
    rw [← hc_eq, h0]
    simp
  have hltT : Tree.lt (treeG φ (inclSub φ H b)) (treeG φ a) := by
    have h1 : Tree.le (treeG φ (inclSub φ H b))
        (treeG (φ.comp (inducedMapRing (K := K) H)) b) :=
      treeG_le_treeG_of_subgroup φ H b
    have h2 : Tree.lt (treeG (φ.comp (inducedMapRing (K := K) H)) b) (data.treeH (e aH)) := by
      rw [← hb_tree]
      exact Tree.lt_of_le_of_ne hle hne
    exact Tree.lt_of_lt_of_le (Tree.lt_of_le_of_lt h1 h2) (Or.inl hTHeq)
  obtain ⟨v, hv⟩ := ih b hb0 hltT
  set yinv : ↥(divisionClosure (Set.range φ)) :=
    ((v⁻¹ : (↥(divisionClosure (Set.range φ)))ˣ) : ↥(divisionClosure (Set.range φ)))
    with hyinvdef
  have hprod : inclSub φ H b * yinv = 1 := by
    rw [← hv, hyinvdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (b : U) * (yinv : U) = 1 := by
    have hh : ((inclSub φ H b * yinv : ↥(divisionClosure (Set.range φ))) : U) = 1 := by
      rw [hprod, Subring.coe_one]
    rw [Subring.coe_mul, inclSub_apply] at hh
    exact hh
  have hprod' : yinv * inclSub φ H b = 1 := by
    rw [hyinvdef, ← hv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (yinv : U) * (b : U) = 1 := by
    have hh : ((yinv * inclSub φ H b : ↥(divisionClosure (Set.range φ))) : U) = 1 := by
      rw [hprod', Subring.coe_one]
    rw [Subring.coe_mul, inclSub_apply] at hh
    exact hh
  have hyinv_mem : (yinv : U) ∈ (divisionClosure
      (Set.range (φ.comp (inducedMapRing (K := K) H))) : Subring U) :=
    DivisionClosure.inverse_mem_divisionClosure
      (R := Set.range (φ.comp (inducedMapRing (K := K) H))) b.2 h1 h2
  refine ⟨(e ⟨(yinv : U), hyinv_mem⟩ : P), (e ⟨(yinv : U), hyinv_mem⟩).2, ?_, ?_⟩
  · have hh : e b * e ⟨(yinv : U), hyinv_mem⟩ = 1 := by
      rw [← map_mul, show b * ⟨(yinv : U), hyinv_mem⟩ = 1 from Subtype.ext h1, map_one]
    have hh' : (e b : P) * (e ⟨(yinv : U), hyinv_mem⟩ : P) = 1 := by
      rw [← Subring.coe_mul, hh, Subring.coe_one]
    rw [hc_eq] at hh'
    exact hh'
  · have hh : e ⟨(yinv : U), hyinv_mem⟩ * e b = 1 := by
      rw [← map_mul, show ⟨(yinv : U), hyinv_mem⟩ * b = 1 from Subtype.ext h2, map_one]
    have hh' : (e ⟨(yinv : U), hyinv_mem⟩ : P) * (e b : P) = 1 := by
      rw [← Subring.coe_mul, hh, Subring.coe_one]
    rw [hc_eq] at hh'
    exact hh'

end Work.ORHughesFree.Section6
