import Mathlib
import Submission.Work.BrauerSuzuki.Group.central_involution_of_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Group

universe u

/-- Every nontrivial finite `2`-group has a subgroup of index `2`. -/
private theorem exists_index_two_subgroup_aux (P : Type u) [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hnt : Nontrivial P) : ∃ M : Subgroup P, M.index = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  suffices h : ∀ n : ℕ, ∀ (Q : Type u) [Group Q] [Finite Q], Nat.card Q = n →
      Nontrivial Q → IsPGroup 2 Q → ∃ M : Subgroup Q, M.index = 2 by
    exact h (Nat.card P) P rfl hnt hP
  intro n
  exact Nat.strong_induction_on n fun m ih =>
    fun Q _ _ hcard hnt hP => by
    obtain ⟨k, hkpos, hk⟩ := (IsPGroup.nontrivial_iff_card hP).mp hnt
    rcases k with _ | k'
    · exact absurd hkpos (Nat.lt_irrefl 0)
    rcases k' with _ | k''
    · -- `|Q| = 2`: the trivial subgroup has index `2`.
      refine ⟨⊥, ?_⟩
      rw [Subgroup.index_bot, hk]
      norm_num
    · -- `|Q| = 2 ^ (k'' + 2)`: quotient out a central involution.
      obtain ⟨z, hzc, hzord⟩ := central_involution_of_isPGroup hP hnt
      let N : Subgroup Q := Subgroup.zpowers z
      have hNnorm : N.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
      haveI : N.Normal := hNnorm
      have hNcard : Nat.card N = 2 := by
        show Nat.card ↥(Subgroup.zpowers z) = 2
        rw [Nat.card_zpowers, hzord]
      have hQcard : Nat.card (Q ⧸ N) = 2 ^ (k'' + 1) := by
        have h1 : Nat.card (Q ⧸ N) = 2 ^ (k'' + 1 + 1) / 2 := by
          rw [← Subgroup.index_eq_card N, Subgroup.index_eq_card_div, hNcard, hk]
        rw [h1, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      have hQnt : Nontrivial (Q ⧸ N) := by
        rw [← Finite.one_lt_card_iff_nontrivial, hQcard]
        exact one_lt_pow₀ (by norm_num) (by omega)
      have hQlt : Nat.card (Q ⧸ N) < m := by
        rw [hQcard, ← hcard, hk]
        exact Nat.pow_lt_pow_right (a := 2) (by norm_num) (by omega)
      obtain ⟨K, hK⟩ := ih (Nat.card (Q ⧸ N)) hQlt (Q ⧸ N) rfl hQnt (hP.to_quotient N)
      exact ⟨K.comap (QuotientGroup.mk' N),
        by rw [Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective N), hK]⟩

theorem exists_index_two_subgroup (P : Type*) [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnc : ¬ IsMulCommutative P) : ∃ M : Subgroup P, M.index = 2 := by
  have hnt : Nontrivial P := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    haveI := hsub
    exact hnc inferInstance
  exact exists_index_two_subgroup_aux P hP hnt

end Work.BrauerSuzuki.Group
