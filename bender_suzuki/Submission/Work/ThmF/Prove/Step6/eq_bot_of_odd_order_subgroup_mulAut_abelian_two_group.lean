import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.Frobenius.Complement.isCyclic_of_commutative_unique_order_p

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped IsMulCommutative

set_option linter.style.haveILetI false

namespace Work.ThmF.Prove.Step6

/-- A finite abelian `2`-group without a four-group is cyclic: it has at most one involution,
hence a unique subgroup of order `2`, and a finite commutative `p`-group with a unique subgroup
of order `p` is cyclic (`Work.Frobenius.Complement.isCyclic_of_commutative_unique_order_p`). -/
theorem isCyclic_of_not_hasFourGroup {P : Type} [Group P] [Finite P]
    (hab : IsMulCommutative P) (h2 : IsPGroup 2 P)
    (hnf : ¬ Submission.Blueprint.HasFourGroup P) : IsCyclic P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- There is at most one involution in `P`.
  have hinv : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y := by
    intro x y hx hy
    by_contra hxy
    exact hnf ⟨x, y, hx, hy, hxy, mul_comm x y⟩
  rcases eq_or_ne (Nat.card P) 1 with h1 | h1
  · haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · have hdvd : 2 ∣ Nat.card P := by
      rcases h2.card_eq_or_dvd with h | h
      · exact absurd h h1
      · exact h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    -- `⟨z⟩` is the unique subgroup of order `2`.
    refine Work.Frobenius.Complement.isCyclic_of_commutative_unique_order_p Nat.prime_two hab h2
      (Subgroup.zpowers z) ?_ ?_
    · rw [Nat.card_zpowers, hz]
    · intro Q hQ
      have hQle : Q ≤ Subgroup.zpowers z := by
        intro x hx
        rw [Subgroup.mem_zpowers_iff]
        by_cases hx1 : x = 1
        · exact ⟨0, by simp [hx1]⟩
        · have hd : orderOf x ∣ 2 := by
            have hd' : orderOf (⟨x, hx⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
            rw [Subgroup.orderOf_mk x hx, hQ] at hd'
            exact hd'
          have hxord : orderOf x = 2 := by
            rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
            · exact absurd (orderOf_eq_one_iff.mp h) hx1
            · exact h
          exact ⟨1, by simpa using (hinv x z hxord hz).symm⟩
      refine Subgroup.eq_of_le_of_card_ge hQle ?_
      rw [Nat.card_zpowers, hz, hQ]

/-- **Bender–Suzuki Step 6, abelian case.**  In a finite abelian `2`-group `P` without a
four-group, every subgroup of `MulAut P` of odd order is trivial: `P` is cyclic, so
`|MulAut P| = φ(|P|) = 2 ^ (n - 1)`, a power of `2`. -/
theorem eq_bot_of_odd_order_subgroup_mulAut_abelian_two_group {P : Type} [Group P] [Finite P] (hab : IsMulCommutative P) (h2 : IsPGroup 2 P) (hnf : ¬ Submission.Blueprint.HasFourGroup P) (A : Subgroup (MulAut P)) (hodd : Odd (Nat.card A)) : A = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic P := isCyclic_of_not_hasFourGroup hab h2 hnf
  haveI : IsCyclic P := hcyc
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  -- The automorphism group of a cyclic group has `Nat.totient` many elements.
  have hcard : Nat.card (MulAut P) = Nat.totient (Nat.card P) := IsCyclic.card_mulAut P
  rw [hn] at hcard
  -- Hence it is a power of `2`.
  have hpow : ∃ k, Nat.card (MulAut P) = 2 ^ k := by
    rcases n with _ | m
    · exact ⟨0, by rw [hcard]; simp⟩
    · refine ⟨m, ?_⟩
      rw [hcard, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m), Nat.succ_sub_one]
      norm_num
  obtain ⟨k, hk⟩ := hpow
  have hP : IsPGroup 2 (MulAut P) := IsPGroup.iff_card.mpr ⟨k, hk⟩
  have hA : IsPGroup 2 ↥A := hP.to_subgroup A
  rcases hA.card_eq_or_dvd with hA1 | hAdvd
  · exact Subgroup.card_eq_one.mp hA1
  · exact absurd hAdvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd))

end Work.ThmF.Prove.Step6
