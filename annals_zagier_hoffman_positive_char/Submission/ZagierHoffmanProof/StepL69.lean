import Submission.ZagierHoffmanProof.StepL68
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L69: member front-bounds at the Q level (k = 2, j = 1)

With StepL68's weight bound (no member is the depth-1 (q)-form), each member's
1-admissibility reduces (kAdm_one_iff_front) to its front pad0 (member) 0 ≤ q:
  ★ q_type1_member_front_le : ∀ i₀ : R0.ιA,
      pad0 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 0 ≤ q
      [q_type1_member_head (head = s₁) + pad0 s 0 ≤ q from 1-adm];
  ★ q_type2_member_front_le : ∀ i : D.ιB,
      pad0 (Q.c (Sum.inr (Sum.inl i))) 0 ≤ q  [same template];
  (type-3 front ≤ q already committed as StepL65's q_type3_member_head_le).
These are the kAdm_one_iff_front inputs for the per-member e dispatch in
main2_case1_j1 (the depth-1 exclusion is discharged by case1_weight_ge_q_add_two:
members have weight w ≥ q+2 > q).  NEXT: the per-member e dispatch — by_cases
2-adm (admExp_self) / ¬2-adm (kAdm_one_iff_front + l2μ < l2μ s via the StepL57/58
dispatch lemmas → ih).  Named gates unchanged.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Type-1 member front ≤ q at the Q level (head s₁, ≤ q by 1-adm). -/
lemma q_type1_member_front_le (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1)
    (R0 : BinaryRel F) (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i₀ : R0.ιA, pad0 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 0 ≤ Nat.card F := by
  classical
  intro D Bs Q
  intro i₀
  have hv := q_type1_member_head F r s hcase hs1v R0 hbhd i₀
  rw [hv]
  have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
  rw [← hp]
  exact h1.1 0 (by omega : 0 < 1)

/-- Type-2 member front ≤ q at the Q level (head s₁, ≤ q by 1-adm). -/
lemma q_type2_member_front_le (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1)
    (R0 : BinaryRel F) (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, pad0 (Q.c (Sum.inr (Sum.inl i))) 0 ≤ Nat.card F := by
  classical
  intro D Bs Q
  intro i
  have hv := q_type2_member_head F r s hcase hs1v R0 hbhd i
  rw [hv]
  have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
  rw [← hp]
  exact h1.1 0 (by omega : 0 < 1)
end ZagierHoffmanPositiveChar
