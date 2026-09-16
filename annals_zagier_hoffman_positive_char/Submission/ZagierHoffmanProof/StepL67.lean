import Submission.ZagierHoffmanProof.StepL66
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L67: Q-level type-3 member depth (k = 2, j = 1, empty prefix)

  ★ q_type3_member_dep (r s hcase hs1v R0 hbhd) : ∀ i : D.ιB,
      Q.dep (Sum.inr (Sum.inr i)) = D.depB i
  — with the empty sPrefix (j=1), Q = Bs and the bstar-level definitional fact
  bstar_c_inr_inr_dep (StepL66) applies directly (dsimp [Q, Bs, D]; sPrefix r s 1
  = [] by simp [sPrefix]; rw; exact bstar_c_inr_inr_dep).  Combined with
  q_type3_member_head (StepL65) this pins the type-3 member's full local shape at
  the Q level: depth D.depB i, head s₁+1 — the clean input for the per-member
  `e` dispatch of main2_case1_j1 (kAdm_one_iff_front needs the depth-1 exclusion:
  a depth-1 type-3 member (D.depB i = 1) with head q (s₁ = q−1) is ¬1-adm — a
  genuine dispatch case, now with all its facts committed).
NEXT: the per-member `e` dispatch in main2_case1_j1 (one family at a time).
Named gates unchanged: j=0 G5 chains, m≥3 hierarchy, theorem_B/D.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Q-level type-3 member depth at k=2, j=1: with the empty sPrefix, Q = Bs and
Q.dep (Sum.inr (Sum.inr i)) = D.depB i (bstar_c_inr_inr_dep). -/
lemma q_type3_member_dep (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (R0 : BinaryRel F) (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, Q.dep (Sum.inr (Sum.inr i)) = D.depB i := by
  classical
  intro D Bs Q
  intro i
  dsimp [Q, Bs, D]
  have hpre : sPrefix r s 1 (by omega : 1 ≤ r) (by omega : 1 ≤ r) = [] := by
    simp [sPrefix]
  rw [hpre]
  exact bstar_c_inr_inr_dep F (RelData.BCqIter F 0 (toData F R0)) (s ⟨0, by omega⟩)
    (fun e => BCqIter_valid F 0 R0 e)
    (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd) i
end ZagierHoffmanPositiveChar
