import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.isCyclic_of_comm_uniqueInvolution
import Submission.Work.BrauerSuzuki.Group.exists_cyclic_index_two
import Submission.Work.BrauerSuzuki.Group.genQuaternion_of_index_two_cyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Huppert III.8.2: a finite `2`-group with a unique involution is cyclic or generalized
quaternion

This file assembles the classification of finite `2`-groups with a unique involution
(Huppert, *Endliche Gruppen I*, III.8.2; Gorenstein, *Finite Groups*, 5.4.10):

`Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution`.

The argument is the internal strong induction on `Nat.card P`.  If `P` is commutative then
`isCyclic_of_comm_uniqueInvolution` gives `IsCyclic P`.  Otherwise `exists_cyclic_index_two`
(the induction step, using the induction hypothesis for all proper subgroups) produces a cyclic
subgroup of index two, and `genQuaternion_of_index_two_cyclic` upgrades that to a generalized
quaternion presentation.
-/

namespace Work.BrauerSuzuki.Group

open Work.BrauerSuzuki

/-- A nontrivial subgroup of a finite `2`-group with a unique involution again has a unique
involution: it is a nontrivial `2`-group, hence contains an involution, which must be the unique
involution of the ambient group. -/
private theorem hasUniqueInvolution_subgroup {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hu : Work.BrauerSuzuki.HasUniqueInvolution P) {K : Subgroup P}
    (hKb : K ≠ ⊥) : Work.BrauerSuzuki.HasUniqueInvolution ↥K := by
  obtain ⟨z, hz2, hzuniq⟩ := hu
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (hP.to_subgroup K).card_eq_or_dvd with h | h
  · exact absurd ((Subgroup.card_eq_one (H := K)).mp h) hKb
  · obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h
    have hw2 : orderOf (w : P) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
    have hwz : (w : P) = z := hzuniq _ hw2
    refine ⟨⟨z, hwz ▸ w.2⟩, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe]; exact hz2
    · intro u hu2
      apply Subtype.ext
      exact hzuniq (u : P) (by rw [Subgroup.orderOf_coe u]; exact hu2)

/-- Huppert III.8.2, by strong induction on `Nat.card P`. -/
private theorem classify_aux :
    ∀ n : ℕ, ∀ (P : Type*) [Group P] [Finite P], Nat.card P = n →
      IsPGroup 2 P → Work.BrauerSuzuki.HasUniqueInvolution P →
        Work.BrauerSuzuki.IsCyclicOrGenQuaternion P := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P _ _ hcard hP hu
    by_cases hcomm : IsMulCommutative P
    · exact Or.inl (Work.BrauerSuzuki.Quaternion.isCyclic_of_comm_uniqueInvolution hcomm hP hu)
    · have ihK : ∀ K : Subgroup P, K ≠ ⊤ → Work.BrauerSuzuki.IsCyclicOrGenQuaternion ↥K := by
        intro K hK
        by_cases hKb : K = ⊥
        · rw [hKb]
          haveI : Subsingleton ↥(⊥ : Subgroup P) :=
            ⟨fun a b => Subtype.ext
              (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
          exact Or.inl inferInstance
        · have hlt : Nat.card ↥K < n := by
            have := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hK)
            rw [Subgroup.card_top] at this
            rwa [← hcard]
          exact ih (Nat.card ↥K) hlt ↥K rfl (hP.to_subgroup K)
            (hasUniqueInvolution_subgroup hP hu hKb)
      obtain ⟨A, hAcyc, hAidx⟩ := exists_cyclic_index_two hP hu hcomm ihK
      exact Or.inr (genQuaternion_of_index_two_cyclic hP hu hcomm hAcyc hAidx)

theorem isCyclicOrGenQuaternion_of_uniqueInvolution {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (h : Work.BrauerSuzuki.HasUniqueInvolution P) :
    Work.BrauerSuzuki.IsCyclicOrGenQuaternion P :=
  classify_aux (Nat.card P) P rfl hP h

end Work.BrauerSuzuki.Group
