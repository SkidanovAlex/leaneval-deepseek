import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.nat_card_involutions_dihedral_four

/-!
# CORE3: an involution of a dihedral group of order `8` that avoids a four-subgroup

`Work.CORE3.InvolutionNotMemOfCardEightDihedral`.

Let `S ≤ X` with `S ≃* DihedralGroup 4` (the dihedral group of order `8`) and let `V ≤ S` be a
four-group (`Work.GW2.IsFourGroup V`, i.e. `|V| = 4` and every element of `V` is an involution).
Then `S` contains an involution outside `V`.

The mathematics is a counting argument.  `DihedralGroup 4` has exactly five involutions (the four
reflections together with the central rotation `r 2`) — this is
`Work.CORE3.nat_card_involutions_dihedral_four`.  A subgroup of order `4` has at most `4`
elements, so it cannot contain all five involutions.  Then `V` is transported into
`DihedralGroup 4` along the isomorphism (`V.subgroupOf S` mapped by `e`), the counting lemma
produces `t` of order two outside it, and `e.symm t` is the required involution.

The hypothesis `Nat.card S = 8` is not needed: it follows from `S ≃* DihedralGroup 4`.
-/

namespace Work.CORE3

/-- **Counting in `DihedralGroup 4`.**  A subgroup of `DihedralGroup 4` of order `4` never
contains all involutions: since `DihedralGroup 4` has `5` involutions, one of them lies outside
every subgroup of order `4`. -/
lemma exists_involution_notMem_of_card_four_dih4 (W : Subgroup (DihedralGroup 4))
    (hW : Nat.card W = 4) :
    ∃ t : DihedralGroup 4, orderOf t = 2 ∧ t ∉ W := by
  by_contra h
  push Not at h
  -- Assuming every involution lies in `W`, the involution subtype injects into `W`, so
  -- `5 = |involutions| ≤ |W| = 4`, a contradiction.
  have hinj : Function.Injective (fun x : {x : DihedralGroup 4 // orderOf x = 2} =>
      (⟨x.1, h x.1 x.2⟩ : W)) := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : W => (z : DihedralGroup 4)) hab
  have hle : Nat.card {x : DihedralGroup 4 // orderOf x = 2} ≤ Nat.card W :=
    Nat.card_le_card_of_injective _ hinj
  rw [nat_card_involutions_dihedral_four, hW] at hle
  omega

theorem InvolutionNotMemOfCardEightDihedral {X : Type*} [Group X] [Finite X]
    (S V : Subgroup X) (hcard : Nat.card S = 8) (hdih : Nonempty (S ≃* DihedralGroup 4))
    (hV : Work.GW2.IsFourGroup V) (hVS : V ≤ S) :
    ∃ s ∈ S, orderOf s = 2 ∧ s ∉ V := by
  obtain ⟨e⟩ := hdih
  -- Transport `V` into `DihedralGroup 4`: `W = e '' (V.subgroupOf S)` has order `4`.
  let VT : Subgroup S := V.subgroupOf S
  let W : Subgroup (DihedralGroup 4) := VT.map e.toMonoidHom
  have hVT : Nat.card VT = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv, hV.1]
  have hWc : Nat.card W = 4 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hVT]
  obtain ⟨t, ht2, htW⟩ := exists_involution_notMem_of_card_four_dih4 W hWc
  refine ⟨(e.symm t : S), (e.symm t : S).2, ?_, ?_⟩
  · -- `orderOf (e.symm t) = orderOf t = 2` (`orderOf` is preserved by `e` and by the
    -- coercion from the subgroup `S` to `X`).
    have h1 : orderOf ((e.symm t : S) : X) = orderOf (e.symm t : S) := Subgroup.orderOf_coe _
    have h2 : orderOf (e.symm t : S) = orderOf (e (e.symm t)) :=
      (MulEquiv.orderOf_eq e (e.symm t)).symm
    have h3 : e (e.symm t) = t := MulEquiv.apply_symm_apply e t
    rw [h1, h2, h3]
    exact ht2
  · -- If `e.symm t ∈ V` then `t = e (e.symm t) ∈ W`, contradicting `htW`.
    intro hs
    apply htW
    have hv : (e.symm t : S) ∈ VT := by
      rw [Subgroup.mem_subgroupOf]
      exact hs
    have hmem : e (e.symm t) ∈ W := Subgroup.mem_map_of_mem e.toMonoidHom hv
    rw [MulEquiv.apply_symm_apply e t] at hmem
    exact hmem

end Work.CORE3
