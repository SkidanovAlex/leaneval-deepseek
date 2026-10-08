import Mathlib

namespace Work.CORE4

/-- An element of order two lying in the centre of a subgroup whose centre has odd order is
impossible.  (Public form of the private lemma `false_of_quasisimple_involution` of
`Submission/Work/CORE4/Case2NotHLeM.lean`, lines 114–132.) -/
theorem false_of_center_involution_of_odd_center {X : Type} [Group X] (E : Subgroup X)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥E))) {t : X} (htE : t ∈ E)
    (ht2 : orderOf t = 2) (hcen : ∀ x ∈ E, x * t = t * x) : False := by
  have hcenter : (⟨t, htE⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcen (y : X) y.2
  have hdvd : orderOf (⟨t, htE⟩ : ↥E) ∣ Nat.card ↥(Subgroup.center ↥E) :=
    Subgroup.orderOf_dvd_natCard _ hcenter
  have hord : orderOf (⟨t, htE⟩ : ↥E) = 2 := by
    have h1 : orderOf ((⟨t, htE⟩ : ↥E) : X) = orderOf (⟨t, htE⟩ : ↥E) :=
      Subgroup.orderOf_coe _
    rw [show ((⟨t, htE⟩ : ↥E) : X) = t from rfl, ht2] at h1
    exact h1.symm
  rw [hord] at hdvd
  exact Odd.not_two_dvd_nat hodd hdvd

end Work.CORE4
