/-
Area CORE4 of the Gorenstein--Walter project.

# `O₂(C_{A₇}(t))` is a four-group for every involution `t` of `A₇`

The `A₇` model fact used to build the CORE4 copy of `Work.GW2.A7ModelProp`: for every element `t`
of order `2` of `A₇`, the `2`-core of the centralizer `C_{A₇}(t)` is a Klein four-group.

**Proof.**  All involutions of `A₇` are conjugate (`Work.AUTA7.A7.InvolutionsConjugate`), so it
suffices to prove the statement for the model involution `a7Invol = (0 1)(2 3)` and transport
along a conjugating element `g` with `g * a7Invol * g⁻¹ = t`:

* `C_{A₇}(t) = C_{A₇}(a7Invol).map (MulAut.conj g)` (`Work.CORE4.CentralizerConjMap`);
* `pCoreIn` is carried by an isomorphism (`Work.CORE4.PcoreInMapMulEquiv`), so
  `O₂(C_{A₇}(t)) = O₂(C_{A₇}(a7Invol)).map (MulAut.conj g)`;
* for the model involution, `O₂(C_{A₇}(a7Invol)) = a7V1 = ⟨t, (0 2)(1 3)⟩`
  (`Work.A7F.pCore_two_centralizer`), and `a7V1` is a four-group
  (`Work.A7F.isFourGroup_V1_V2`); isomorphism carries four-groups to four-groups
  (`isFourGroup_map_aux`).

The model computation `pCore_two_centralizer` lives in the `CORE4` sub-area
`Submission/Work/CORE4/A7M/` — a copy of the `A7F` area's files with the import list adapted, since
the `A7F` area re-declares the `Work.GW2` vocabulary and cannot be imported next to
`Submission.Work.CORE4.Defs` (`environment already contains 'Work.GW2.A7ModelProp'`).
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.A7M.PCoreTwo
import Submission.Work.CORE4.CentralizerConjMap
import Submission.Work.CORE4.PcoreInMapMulEquiv
import Submission.Work.AUTA7.A7.InvolutionsConjugate

namespace Work.CORE4

open Subgroup

/-! ## Generic transport lemmas -/

/-- An isomorphism carries four-groups to four-groups. -/
theorem isFourGroup_map_aux {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {V : Subgroup G}
    (h : Work.GW2.IsFourGroup V) : Work.GW2.IsFourGroup (V.map φ.toMonoidHom) := by
  constructor
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact h.1
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    show φ w ^ 2 = 1
    rw [← map_pow, h.2 w hw, map_one]

/-! ## The model fact -/

theorem A7ModelO2 (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    Work.GW2.IsFourGroup
      (Work.GW2.pCoreIn 2 (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7))))) := by
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; omega
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (Work.AUTA7.A7.InvolutionsConjugate (x := Work.A7.a7Invol) (y := t)
      Work.A7.a7Invol_mul_self htt Work.A7.a7Invol_ne_one ht1)
  have hC : Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7))) =
      (Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7)))).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Work.CORE4.CentralizerConjMap g Work.A7.a7Invol
  rw [hC, Work.CORE4.PcoreInMapMulEquiv (MulAut.conj g) 2,
    Work.A7F.pCore_two_centralizer]
  exact isFourGroup_map_aux (MulAut.conj g) Work.A7F.isFourGroup_V1_V2.1

end Work.CORE4
