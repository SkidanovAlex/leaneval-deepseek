import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

theorem exists_pair_of_subset {ι : Type*} (R : ι → ι → Prop) (K : ℕ)
    (h : ∀ (M : ℕ) (e : Fin M → ι), Function.Injective e → K ≤ M →
      ∃ i j : Fin M, i ≠ j ∧ R (e i) (e j))
    (A : Finset ι) (hA : K ≤ A.card) : ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ R i j := by
  obtain ⟨i, j, hij, hR⟩ :=
    h A.card (fun k => (A.equivFin.symm k : {x // x ∈ A}).val)
      (fun a b hab => A.equivFin.symm.injective (Subtype.ext hab)) hA
  exact ⟨_, (A.equivFin.symm i).prop, _, (A.equivFin.symm j).prop,
    fun hh => hij (A.equivFin.symm.injective (Subtype.ext hh)), hR⟩

end Work.BMF.SD
