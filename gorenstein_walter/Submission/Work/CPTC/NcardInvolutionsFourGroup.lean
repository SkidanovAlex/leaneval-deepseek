import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CPTC

/-- In a subgroup all of whose elements satisfy `x ^ 2 = 1`, an element lies in
`involutionSet W` exactly when it is different from `1`. -/
lemma involutionSet_eq_sdiff_singleton {G : Type} [Group G] (W : Subgroup G)
    (hsq : ∀ v ∈ W, v ^ 2 = 1) :
    Work.GW2.involutionSet W = (W : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨hxW, hx2⟩
    refine ⟨hxW, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hx1
    rw [hx1, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  · rintro ⟨hxW, hx1⟩
    have hx1' : x ≠ 1 := by simpa using hx1
    refine ⟨hxW, ?_⟩
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (hsq x hxW)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1'
    · exact h

theorem NcardInvolutionsFourGroup {G : Type} [Group G] [Finite G] (W : Subgroup G)
    (h4 : Work.GW2.IsFourGroup W) :
    (Work.GW2.involutionSet W).ncard = 3 := by
  rw [involutionSet_eq_sdiff_singleton W h4.2]
  rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem W)]
  have hWncard : (W : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h4.1
  rw [hWncard]

end Work.CPTC
