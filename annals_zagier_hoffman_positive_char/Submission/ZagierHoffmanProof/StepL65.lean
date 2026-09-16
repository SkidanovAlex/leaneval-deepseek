import Submission.ZagierHoffmanProof.StepL64
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L65: type-3 member head at Q (k = 2, j = 1)

The last member-head component of main2_case1_j1's dispatch (PLAN SESSION 215
NEXT): the type-3 member's head at index 0 is the FRONT GROWTH s₁ → s₁+1:
  ★ q_type3_member_head (r s hcase hbigv hsj R0 hbhd) : ∀ i : D.ιB,
      pad0 (Q.c (Sum.inr (Sum.inr i))) 0 = (s⟨0⟩ : ℕ) + 1
      [pad0_of_lt at hm : 0 < Q.dep (from Q_dep_inr_inr's 1 ≤ Q.dep), then
       type3_sjadd_one_at at k=2, j=1, index 0, dsimp, simpa];
  ★ q_type3_member_head_le : pad0 (Q.c (Sum.inr (Sum.inr i))) 0 ≤ q [head + omega].
Together with StepL64's type-1/type-2 heads, EVERY CASE-1 j=1 member now has its
front ≤ q (type-1/2: s₁ ≤ q by 1-adm; type-3: s₁+1 ≤ q) — the kAdm_one_iff_front
input for the per-member 1-admissibility in the ih-dispatch of main2_case1_j1.
NEXT: the hid fold (S1–S3, all committed) and the admExp_combine splice of
main2_case1_j1.  Named gates unchanged: j=0 G5 chains, m≥3 hierarchy, theorem_B/D.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Q-level type-3 member head at k=2, j=1: pad0 at index 0 is s₁ + 1 (the front
growth s₁ → s₁+1 at position 0) — type3_sjadd_one_at at position 0. -/
lemma q_type3_member_head (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hsj : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB,
      pad0 (Q.c (Sum.inr (Sum.inr i))) 0 = (s ⟨0, by omega⟩ : ℕ) + 1 := by
  classical
  intro D Bs Q
  intro i
  have hdep : 1 ≤ Q.dep (Sum.inr (Sum.inr i)) :=
    Q_dep_inr_inr F r s 2 1 (by omega : 1 ≤ 2) hcase (by omega : 1 ≤ 1)
      (by omega : 1 ≤ 2 - 1) hsj R0 hbhd i
  have hm : 0 < Q.dep (Sum.inr (Sum.inr i)) := by omega
  have h := type3_sjadd_one_at F r s 2 1 (by omega : 1 ≤ 2) hcase (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 2 - 1) hbigv hsj R0 hbhd i hm
  rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hm]
  dsimp at h
  simpa using h
/-- Type-3 member head ≤ q (via s₁+1 ≤ q) — the kAdm_one_iff_front input. -/
lemma q_type3_member_head_le (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hsj : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, pad0 (Q.c (Sum.inr (Sum.inr i))) 0 ≤ Nat.card F := by
  classical
  intro D Bs Q i
  have hv := q_type3_member_head F r s hcase hbigv hsj R0 hbhd i
  rw [hv]
  omega

end ZagierHoffmanPositiveChar
