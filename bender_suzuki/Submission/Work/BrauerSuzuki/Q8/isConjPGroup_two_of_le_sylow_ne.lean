import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Quaternion.isCyclic_of_comm_uniqueInvolution
import Submission.Work.BrauerSuzuki.Q8.hasUniqueInvolution_of_le_of_two_dvd_card
import Submission.Work.BrauerSuzuki.Q8.sylow_two_structure_and_centralizer
import Submission.Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow
import Submission.Work.BrauerSuzuki.Sylow.isConjPGroup_two_of_isCyclic_of_isPGroup
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `IsConjPGroup 2 Q` for a proper subgroup `Q` of a `Q₈` Sylow `2`-subgroup

Let `G` be a finite group with a Sylow `2`-subgroup `S` that is a generalized quaternion group
in Dade's normal form `d` with `d.n = 2` (so `S ≅ Q₈`, of order `8`).  Then every proper
non-trivial subgroup `Q ≤ S` satisfies Frobenius' condition at `p = 2`: the quotient
`N_G(Q)/C_G(Q)` is a `2`-group.

Indeed such a `Q` is a proper subgroup of `Q₈`, hence has order `2` or `4`, hence is cyclic;
and a cyclic `2`-subgroup always satisfies Frobenius' condition at `2` because the quotient
`N_G(Q)/C_G(Q)` embeds into `Aut(Q)`, which for `Q` cyclic of order `2^k` is the group
`(ℤ/2^k)^*` of order `2^(k-1)`.
-/

namespace Work.BrauerSuzuki.Q8

open Work.BrauerSuzuki

/-- A subgroup of a `p`-group is a `p`-group (via the injective inclusion homomorphism). -/
private lemma isPGroup_of_le {p : ℕ} {G : Type*} [Group G] {S Q : Subgroup G}
    (hS : IsPGroup p ↥S) (hQle : Q ≤ S) : IsPGroup p ↥Q :=
  IsPGroup.of_injective hS
    { toFun := fun x => ⟨(x : G), hQle x.2⟩
      map_one' := by ext; rfl
      map_mul' := fun a b => by ext; rfl }
    (fun a b h => Subtype.ext (by simpa using congrArg (fun z : ↥S => (z : G)) h))

theorem isConjPGroup_two_of_le_sylow_ne {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    (Q : Subgroup G) (hQle : Q ≤ (S : Subgroup G)) (hQbot : Q ≠ ⊥)
    (hQne : Q ≠ (S : Subgroup G)) : Work.NPC.IsConjPGroup 2 Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSdata := Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d
  have hS8 : Nat.card ↥S = 8 := by
    have h := hSdata.1
    rw [h2] at h
    norm_num at h
    exact h
  have hQ2 : IsPGroup 2 ↥Q := isPGroup_of_le hSdata.2.1 hQle
  have hle8 : Nat.card ↥Q ≤ 8 := (Subgroup.card_le_of_le hQle).trans_eq hS8
  have hne8 : Nat.card ↥Q ≠ 8 := by
    intro h
    exact hQne (Subgroup.eq_of_le_of_card_ge hQle (by rw [h]; exact hS8.le))
  have hne1 : Nat.card ↥Q ≠ 1 := fun h => hQbot ((Subgroup.card_eq_one).mp h)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
  have hk3 : k ≤ 3 := by
    have h2' : (2 : ℕ) ^ k ≤ (2 : ℕ) ^ 3 := by
      rw [← hk]; norm_num; exact hle8
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h2'
  have hk0 : k ≠ 0 := fun h => hne1 (by rw [hk, h]; norm_num)
  have hk3' : k ≠ 3 := fun h => hne8 (by rw [hk, h]; norm_num)
  have hcard : Nat.card ↥Q = 2 ∨ Nat.card ↥Q = 4 := by
    have : k = 1 ∨ k = 2 := by omega
    rcases this with h | h <;> rw [hk, h] <;> norm_num
  have hSuniq : HasUniqueInvolution ↥S :=
    ⟨d.tau ^ 2 ^ (d.n - 1), hSdata.2.2.1, hSdata.2.2.2.1⟩
  have hdiv : 2 ∣ Nat.card ↥Q := by rcases hcard with h | h <;> rw [h] <;> norm_num
  have hQuniq : HasUniqueInvolution ↥Q :=
    hasUniqueInvolution_of_le_of_two_dvd_card hSuniq hQle hdiv
  have hcyc : IsCyclic ↥Q := by
    rcases hcard with h2' | h4
    · exact isCyclic_of_prime_card h2'
    · exact Work.BrauerSuzuki.Quaternion.isCyclic_of_comm_uniqueInvolution
        (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥Q) (by rw [h4]; norm_num))
        hQ2 hQuniq
  exact Work.BrauerSuzuki.Sylow.isConjPGroup_two_of_isCyclic_of_isPGroup Q hcyc hQ2

end Work.BrauerSuzuki.Q8
