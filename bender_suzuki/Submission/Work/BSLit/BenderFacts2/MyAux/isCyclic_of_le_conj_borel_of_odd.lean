import Mathlib
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.Weyl
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.ModelData.szModelData
import Submission.Work.BSLit.BenderFacts2.MyAux.isCyclic_of_le_sup_of_isPGroup_of_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2.MyAux

/-- An odd-order subgroup of a conjugate of the Suzuki Borel subgroup `B = U ⋊ T` is cyclic:
reduce to `A ≤ B` by conjugating with `g⁻¹`, then use that `A` embeds into `(U ⊔ T)/U ≅ T` with
`T` cyclic (the general lemma `isCyclic_of_le_sup_of_isPGroup_of_isCyclic`). -/
theorem isCyclic_of_le_conj_borel_of_odd (n : ℕ) {A : Subgroup (LeanEval.GroupTheory.Defs.SzModel n)}
    {g : LeanEval.GroupTheory.Defs.SzModel n}
    (hA : A ≤ (Submission.Sz.szBorelS n).map (MulAut.conj g).toMonoidHom)
    (hodd : Odd (Nat.card ↥A)) : IsCyclic ↥A := by
  set A' : Subgroup (LeanEval.GroupTheory.Defs.SzModel n) :=
    A.map (MulAut.conj g⁻¹).toMonoidHom with hA'def
  -- `A' = A^(g⁻¹)` lies in `B`.
  have hA'le : A' ≤ Submission.Sz.szBorelS n := by
    intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨x, hxA, hxa⟩ := ha
    have hx : x ∈ (Submission.Sz.szBorelS n).map (MulAut.conj g).toMonoidHom := hA hxA
    rw [Subgroup.mem_map] at hx
    obtain ⟨b, hbB, hba⟩ := hx
    have hab : a = b := by
      rw [← hxa, ← hba]
      show (MulAut.conj g⁻¹) ((MulAut.conj g) b) = b
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hab]
    exact hbB
  have hA'odd : Odd (Nat.card ↥A') := by
    rw [hA'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hodd
  have hcop : ¬ 2 ∣ Nat.card ↥A' :=
    fun h => (Nat.not_even_iff_odd.mpr hA'odd) (even_iff_two_dvd.mpr h)
  have hcyc' : IsCyclic ↥A' :=
    isCyclic_of_le_sup_of_isPGroup_of_isCyclic Nat.prime_two
      (Submission.Sz.szTwoGroupS_isPGroup n)
      (Work.Models.ModelData.isCyclic_szTS n)
      (Submission.Sz.szTS_le_normalizer_szTwoGroupS n)
      (Submission.Sz.szTS_inf_szTwoGroupS n)
      (hA'le.trans (le_of_eq (Submission.Sz.szBorelS_eq_sup n)))
      hcop
  have e := Subgroup.equivMapOfInjective A (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective
  exact e.isCyclic.mpr hcyc'

end Work.BSLit.BenderFacts2.MyAux
