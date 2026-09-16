import Submission.ZagierHoffmanProof.StepL69
import Submission.ZagierHoffmanProof.StepL70
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L71: per-member e for the TYPE-3 family (SESSION 223–224 closure)

The CASE-1 j = 1 per-member dispatch of main2_case1_j1, type-3 family:
  ★ q_type3_member_e (w r s hw hcase hbigv hs1v h1 ih) : ∃ R0 hbhd,
      ∀ i : D.ιB, AdmExp F w 2 (Q.c (Sum.inr (Sum.inr i)))
  — per member: by_cases 2-adm (admExp_self) / ¬2-adm (in-domain):
    1-adm via kAdm_one_iff_front: front pad0 (member) 0 = s₁+1 ≤ q
    (q_type3_member_head_le, StepL65); the depth-1 exclusion uses
    weight_dep_one_eq_pad0 (StepL70) + case1_weight_ge_q_add_two (StepL68):
    under dep = 1 the member's weight = pad0 (member) 0 = s₁+1 ≤ q contradicts
    weight = w ≥ q+2 — so NO member is the ¬1-adm depth-1 (q)-form;
    the l2μ drop is the psum ≤ S with front growth at position 0
    (type3_sjadd_one_at / type3_front_le / headVal growth → l2_member_lt).
  Then ih (the MAIN(2) recursion hypothesis at the strictly smaller measure).
The type-1/type-2 analogues follow the same template (front = s₁, StepL69);
then main2_case1_j1's hid fold (S1–S3) + admExp_combine splice.  Named gates
unchanged: j=0 G5 chains, m≥3 hierarchy, theorem_B/D.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Per-member e for the TYPE-3 family: 2-adm → admExp_self; ¬2-adm → in-domain
(1-adm via kAdm_one_iff_front from the front ≤ q, weight > q excludes the depth-1
form) with l2μ < l2μ s (front growth at position 0) → ih. -/
theorem q_type3_member_e (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExp F w 2 m) :
    ∃ (R0 : BinaryRel F)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB, AdmExp F w 2 (Q.c (Sum.inr (Sum.inr i))) := by
  classical
  have hk1 : 1 ≤ 2 := by omega
  have hj1 : 1 ≤ 1 := by omega
  have hjk : 1 ≤ 2 - 1 := by omega
  have hsj : (s ⟨0, by omega⟩ : ℕ) < Nat.card F := by omega
  have hsleq : ∀ x : ℕ, x < 2 - 1 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx0 : x = 0 := by omega
    subst x
    exact h1.1 0 (by omega)
  have hP := prop212_step1 F r s 2 1 hk1 hcase hj1 hjk hbigv hsj
    (fun i hi1 hi0 => by omega) hsleq
  rcases hP with ⟨R0, u, hbhd, haa, hdepu, hbstar, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, hbhd, ?_⟩
  intro D Bs Q
  intro i
  let m : Fin (Q.dep (Sum.inr (Sum.inr i))) → ℕ+ := Q.c (Sum.inr (Sum.inr i))
  have hwm : weight (Q.dep (Sum.inr (Sum.inr i))) m = weight r s := by
    simpa [m] using (ht3 i).1
  by_cases h2 : kAdmissible (Nat.card F) m 2
  · have hd : 0 < Q.dep (Sum.inr (Sum.inr i)) := Q.hdep (Sum.inr (Sum.inr i))
    have h2' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
      simpa [m] using h2
    have hw' : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w := by
      rw [hwm]
      exact hw
    exact admExp_self F w 2 hd (Q.c (Sum.inr (Sum.inr i))) hw' h2'
  · -- ¬2-adm: 1-adm + l2μ drop → ih
    have hf := q_type3_member_head_le F r s hcase hbigv hsj R0 hbhd
    have hm0 : pad0 m 0 ≤ Nat.card F := by
      dsimp [m]
      exact hf i
    have hdepth : Q.dep (Sum.inr (Sum.inr i)) = 1 → pad0 m 0 ≠ Nat.card F := by
      intro hd1 hq0
      have hw1 : weight (Q.dep (Sum.inr (Sum.inr i))) m = pad0 m 0 := by
        simpa [m] using weight_dep_one_eq_pad0 (Q.c (Sum.inr (Sum.inr i))) hd1
      have hbigp : (Nat.card F : ℕ) < pad0 s 1 := by
        rw [pad0_of_lt s (by omega : 1 < r)]
        exact hbigv
      have hwg : Nat.card F + 2 ≤ weight r s := case1_weight_ge_q_add_two F s hcase hbigp
      have hwr : weight r s = Nat.card F := by
        calc weight r s = weight (Q.dep (Sum.inr (Sum.inr i))) m := hwm.symm
             _ = pad0 m 0 := hw1
             _ = Nat.card F := hq0
      omega
    have h1m : kAdmissible (Nat.card F) m 1 :=
      kAdm_one_iff_front (Nat.card F) m hm0 hdepth
    have hdrop : l2μ (Nat.card F) m < l2μ (Nat.card F) s := by
      dsimp [m]
      have hle : psum (Q.c (Sum.inr (Sum.inr i))) 2 ≤ psum s 2 := (ht3 i).2.1
      by_cases hlt : psum (Q.c (Sum.inr (Sum.inr i))) 2 < psum s 2
      · exact l2_member_lt (q := Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) (Or.inl hlt)
      · apply l2_member_lt (q := Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))
        right
        constructor
        · exact le_antisymm hle (le_of_not_gt hlt)
        · have hdep : 1 ≤ Q.dep (Sum.inr (Sum.inr i)) :=
            Q_dep_inr_inr F r s 2 1 hk1 hcase hj1 hjk hsj R0 hbhd i
          have hm : 0 < Q.dep (Sum.inr (Sum.inr i)) := by omega
          have hfront := type3_sjadd_one_at F r s 2 1 hk1 hcase hj1 hjk hbigv hsj R0 hbhd i hm
          have hfl := type3_front_le F r s 2 1 hk1 hcase hj1 hjk hbigv hsj hsleq R0 hbhd i 0 (by omega : 0 < 1)
          have hsv : headVal (Nat.card F) s = pad0 s 0 := by
            rw [headVal]
            rw [if_pos (h1.1 0 (by omega : 0 < 1))]
          have hmv : headVal (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) =
              pad0 (Q.c (Sum.inr (Sum.inr i))) 0 := by
            rw [headVal]
            rw [if_pos hfl]
          have hfront0 : ((Q.c (Sum.inr (Sum.inr i))) ⟨0, hm⟩ : ℕ) =
              (s ⟨0, by omega⟩ : ℕ) + 1 := by
            simpa using hfront
          have hp0v : pad0 (Q.c (Sum.inr (Sum.inr i))) 0 =
              ((Q.c (Sum.inr (Sum.inr i))) ⟨0, hm⟩ : ℕ) := pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hm
          have hs0v : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
          rw [hsv]
          rw [hmv]
          rw [hp0v]
          rw [hs0v]
          rw [hfront0]
          omega
    have hwm' : weight (Q.dep (Sum.inr (Sum.inr i))) m = w := by
      rw [hwm]
      exact hw
    have hres := ih (Q.dep (Sum.inr (Sum.inr i))) m hwm' h1m h2 hdrop
    simpa [m] using hres
end ZagierHoffmanPositiveChar
