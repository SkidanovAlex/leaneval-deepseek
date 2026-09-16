import Submission.ZagierHoffmanProof.StepL111
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L112: the (k, k−2) chain members are (k−1)-admissible (SESSION 257)

The k-symbolic member (k−1)-adm facts for the (k, k−2) CASE-1 splice (the next
j-split after StepL110's (k, k−1)): over the zeta (k, k−2) chain lets
(D := BCqIter F (k−(k−2)−1) (toData R0) — ONE BC_q iterate; B*_{s⟨(k−2)−1⟩};
front sPrefix r s (k−2)), every type-1 (i₀ ≠ u), type-2 and type-3 member is
(k−1)-admissible.  Positions x < k−1 of a member are: the front (length k−3,
positions 0..k−4 share s-values — ≤ q by the input's (k−1)-admissibility h1), the
merged head at position k−3 = j−1 (s⟨k−3⟩ for type 1/2 via type{1,2}_sj_at_jm1,
s⟨k−3⟩+1 for type 3 via type3_sjadd_one_at — ≤ q by hsj), and the one-iterate
entry at position k−2 (q for type 1 — the iterate a-head; 1 for type 2 — the
iterate b-head; the fiber entry-1 ≤ q for type 3).  Depth: type-1/2 ≥ k
(structural); type-3 ≥ k−1 only, so its depth-(k−1)-form is excluded by the
WEIGHT (hwmem: member weight = weight r s), exactly as in StepL87's level-3 j=1
(= (k, k−2) at k=3) type-3 fact.
NEXT: maink_case1_kk2 (the (k,k−2) splice, StepL113).  theorem_B/D remain
ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Second entry of the one-iterate b-tuple is ≤ q (the p2WpT fiber bound: the
fiber LePad (X.hle) at prefix-1 plus the base b-head = 1), for ANY base data D. -/
lemma BCq_cB_entry1_le_q_head1 (D : RelData F)
    (hbhd : ∀ j' : D.ιB, ((D.cB j') ⟨0, D.hdepB j'⟩ : ℕ) = 1) :
    ∀ i : (RelData.BCq F D).ιB,
      pad0 ((RelData.BCq F D).cB i) 1 ≤ Nat.card F := by
  classical
  intro i
  have hfib : (RelData.BCq F D).cB i =
      consVec oneExp ((p2WpT F (qMinusExp F) (D.hdepB i.1) (D.cB i.1)).c i.2) := by
    change (RelData.BCq F D).cB i =
      consVec oneExp ((p2WpT F (qMinusExp F) (D.hdepB i.1) (D.cB i.1)).c i.2)
    rfl
  let X : P2Data F 1 (D.depB i.1) (by omega : 0 < 1) (D.hdepB i.1)
      (single (qMinusExp F)) (D.cB i.1) :=
    p2WpT F (qMinusExp F) (D.hdepB i.1) (D.cB i.1)
  have hle1 := (X.hle i.2).2 1
  have hsumL : psum (X.c i.2) 1 = ((X.c i.2) ⟨0, X.hdep i.2⟩ : ℕ) := by
    rw [psum_succ, psum_zero]
    simp
    rw [pad0_of_lt (X.c i.2) (X.hdep i.2)]
  have hsumR : psumSeq (tupPadSum (single (qMinusExp F)) (D.cB i.1)) 1 =
      (qMinusExp F : ℕ) + ((D.cB i.1) ⟨0, D.hdepB i.1⟩ : ℕ) := by
    dsimp [psumSeq, tupPadSum]
    change pad0 (single (qMinusExp F)) 0 + pad0 (D.cB i.1) 0 =
      (qMinusExp F : ℕ) + ((D.cB i.1) ⟨0, D.hdepB i.1⟩ : ℕ)
    rw [pad0_single_zero]
    rw [pad0_of_lt (D.cB i.1) (D.hdepB i.1)]
  have hle2 : pad0 (X.c i.2) 0 ≤ Nat.card F := by
    have hb := hbhd i.1
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
    calc
      pad0 (X.c i.2) 0 = ((X.c i.2) ⟨0, X.hdep i.2⟩ : ℕ) := by
            rw [pad0_of_lt (X.c i.2) (X.hdep i.2)]
      _ = psum (X.c i.2) 1 := hsumL.symm
      _ ≤ psumSeq (tupPadSum (single (qMinusExp F)) (D.cB i.1)) 1 := hle1
      _ = (qMinusExp F : ℕ) + ((D.cB i.1) ⟨0, D.hdepB i.1⟩ : ℕ) := hsumR
      _ = Nat.card F - 1 + 1 := by rw [hq, hb]
      _ = Nat.card F := by
        have h2 : 2 ≤ Nat.card F := card_ge_two F
        omega
  calc
    pad0 ((RelData.BCq F D).cB i) 1
        = pad0 ((p2WpT F (qMinusExp F) (D.hdepB i.1) (D.cB i.1)).c i.2) 0 := by
          rw [hfib]
          change pad0 (consVec oneExp ((p2WpT F (qMinusExp F) (D.hdepB i.1) (D.cB i.1)).c i.2)) 1 =
            pad0 ((p2WpT F (qMinusExp F) (D.hdepB i.1) (D.cB i.1)).c i.2) 0
          rw [pad0_consVec]
    _ = pad0 (X.c i.2) 0 := rfl
    _ ≤ Nat.card F := hle2

/-- The one-iterate relation equals `BCq (toData R0)` (as a data value). -/
lemma BCqIter_kk2_one (k : ℕ) (hk3 : 3 ≤ k) (R0 : BinaryRel F) :
    RelData.BCqIter F (k - (k - 2) - 1) (toData F R0) = RelData.BCq F (toData F R0) := by
  have hn1 : k - (k - 2) - 1 = 1 := by omega
  rw [hn1]
  rfl

/-- Type-1 (a-side, i₀ ≠ u) members of the (k, k−2) chain are (k−1)-adm, _of form. -/
theorem maink_kk2_type1_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk3 : 3 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 2 - 1, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 2) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 2 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 2) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 2) - 1) R0 (s ⟨k - 2 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 2) (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u →
      kAdmissible (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 2) - 1) (toData F R0) i₀))) (k - 1) := by
  classical
  intro D Bs Q i₀ hi
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  let idxA : D.ιA := RelData.iterIdx F (k - (k - 2) - 1) (toData F R0) (i₀ : (toData F R0).ιA)
  have hdepge : k ≤ Q.dep (Sum.inl idxA) := by
    have hQd : Q.dep (Sum.inl idxA) = (toData F R0).depA i₀ + (k - (k - 2) - 1) + 1 + ((k - 2) - 1) := by
      have h1' := FixedOver.prependList_dep F Bs (sPrefix r s (k - 2) (by omega) (by omega)) (Sum.inl idxA)
      have h2 : Bs.dep (Sum.inl idxA) = D.depA idxA + 1 := by
        dsimp [Bs, ofBstarOver, D]
      have hlen : (sPrefix r s (k - 2) (by omega) (by omega)).length = (k - 2) - 1 := by
        rw [sPrefix_length]
      have hd := RelData.BCqIter_depA_at F (k - (k - 2) - 1) (toData F R0) i₀
      rw [h1', h2, hlen, hd]
    rw [hQd]
    have hda : 0 < (toData F R0).depA i₀ := by
      change 0 < R0.depA i₀
      exact R0.hdepA i₀
    omega
  refine kAdm_pred_of_pad0_le (Nat.card F) k (Q.c (Sum.inl idxA)) hk1 hdepge ?_
  intro x hx
  by_cases hx1 : x < k - 3
  · have hxQ : x < Q.dep (Sum.inl idxA) := by
      have hlt : x < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := member_prefix_pos F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
      (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd (Sum.inl idxA) x (by omega) hxQ
    have hv' : (Q.c (Sum.inl idxA)) ⟨x, hxQ⟩ = s ⟨x, by omega⟩ := by
      simpa [Q, Bs, D] using hv
    rw [pad0_of_lt (Q.c (Sum.inl idxA)) hxQ]
    rw [hv']
    have hs : (s ⟨x, by omega⟩ : ℕ) = pad0 s x := by
      have hxr : x < r := by
        have hx2 : x < k - 1 := by omega
        have hk1r : k - 1 ≤ r := by omega
        omega
      rw [pad0_of_lt s hxr]
    rw [hs]
    exact h1.1 x (by omega)
  · by_cases hx2 : x < k - 2
    · have hxj : x = (k - 2) - 1 := by omega
      rw [hxj]
      have hxQ : (k - 2) - 1 < Q.dep (Sum.inl idxA) := by
        have hlt : (k - 2) - 1 < k := by omega
        exact lt_of_lt_of_le hlt hdepge
      have hv := type1_sj_at_jm1 F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
        (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd idxA hxQ
      rw [pad0_of_lt (Q.c (Sum.inl idxA)) hxQ]
      rw [hv]
      exact le_of_lt hsj
    · have hxk : x = k - 2 := by omega
      rw [hxk]
      have hxQ : k - 2 < Q.dep (Sum.inl idxA) := by
        have hlt : k - 2 < k := by omega
        exact lt_of_lt_of_le hlt hdepge
      -- position k−2 = the one-iterate a-head = q
      have hsh : pad0 (Q.c (Sum.inl idxA)) (k - 2) = Nat.card F := by
        have hge : k - 2 ≥ k - 2 := le_rfl
        have hsh0 := type1_pad0_shift F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
          (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd idxA (k - 2) hge
        have hsub : (k - 2) - (k - 2) = 0 := by omega
        rw [hsh0, hsub]
        have hf := BCqIter_cA_pad0_front F (k - (k - 2) - 1) R0 i₀ 0 (by omega : 0 < k - (k - 2) - 1)
        -- hf : pad0 (D.cA (iterIdx i₀)) 0 = q ; idxA is the same iterate index
        simpa [idxA] using hf
      rw [hsh]

/-- Type-2 (b-side inl) members of the (k, k−2) chain are (k−1)-adm, _of form. -/
theorem maink_kk2_type2_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk3 : 3 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 2 - 1, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 2) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 2 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 2) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 2) - 1) R0 (s ⟨k - 2 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 2) (by omega) (by omega))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) (k - 1) := by
  classical
  intro D Bs Q i
  have hk1 : 1 ≤ k := by omega
  have hdepge : k ≤ Q.dep (Sum.inr (Sum.inl i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 + ((k - 2) - 1) := by
      have h1' := FixedOver.prependList_dep F Bs (sPrefix r s (k - 2) (by omega) (by omega)) (Sum.inr (Sum.inl i))
      have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
        dsimp [Bs, ofBstarOver, D]
      have hlen : (sPrefix r s (k - 2) (by omega) (by omega)).length = (k - 2) - 1 := by
        rw [sPrefix_length]
      rw [h1', h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  refine kAdm_pred_of_pad0_le (Nat.card F) k (Q.c (Sum.inr (Sum.inl i))) hk1 hdepge ?_
  intro x hx
  by_cases hx1 : x < k - 3
  · have hxQ : x < Q.dep (Sum.inr (Sum.inl i)) := by
      have hlt : x < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := member_prefix_pos F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
      (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd (Sum.inr (Sum.inl i)) x (by omega) hxQ
    have hv' : (Q.c (Sum.inr (Sum.inl i))) ⟨x, hxQ⟩ = s ⟨x, by omega⟩ := by
      simpa [Q, Bs, D] using hv
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hxQ]
    rw [hv']
    have hs : (s ⟨x, by omega⟩ : ℕ) = pad0 s x := by
      have hxr : x < r := by
        have hx2 : x < k - 1 := by omega
        have hk1r : k - 1 ≤ r := by omega
        omega
      rw [pad0_of_lt s hxr]
    rw [hs]
    exact h1.1 x (by omega)
  · by_cases hx2 : x < k - 2
    · have hxj : x = (k - 2) - 1 := by omega
      rw [hxj]
      have hxQ : (k - 2) - 1 < Q.dep (Sum.inr (Sum.inl i)) := by
        have hlt : (k - 2) - 1 < k := by omega
        exact lt_of_lt_of_le hlt hdepge
      have hv := type2_sj_at_jm1 F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
        (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd i hxQ
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hxQ]
      rw [hv]
      exact le_of_lt hsj
    · have hxk : x = k - 2 := by omega
      rw [hxk]
      have hxQ : k - 2 < Q.dep (Sum.inr (Sum.inl i)) := by
        have hlt : k - 2 < k := by omega
        exact lt_of_lt_of_le hlt hdepge
      -- position k−2 = the one-iterate b-head = 1
      have hsh : pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 2) = 1 := by
        have hsh0 := type2_pad0_shift F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
          (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd i 0
        have hj0 : (k - 2) + 0 = k - 2 := by omega
        rw [← hj0]
        rw [hsh0]
        have hb0 := BCqIter_head_one_data F (k - (k - 2) - 1) R0 hbhd i
        have hz : 0 < D.depB i := D.hdepB i
        rw [pad0_of_lt (D.cB i) hz]
        simpa [D] using hb0
      rw [hsh]
      have hq : 2 ≤ Nat.card F := card_ge_two F
      omega


/-- Second entry of a `BC_q`-iterate b-tuple is ≤ q for every iterate level n ≥ 1
(the `n+1`-iterate is `BCq`-once over the level-`n` data, whose heads are 1). -/
lemma BCqIter_cB_entry1_le_q (n : ℕ) (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) (hn : 1 ≤ n) :
    ∀ i : (RelData.BCqIter F n (toData F R0)).ιB,
      pad0 ((RelData.BCqIter F n (toData F R0)).cB i) 1 ≤ Nat.card F := by
  classical
  rcases n with _ | n
  · omega
  · rw [BCqIter_append]
    intro i
    change RelData.BCqIdx F (RelData.BCqIter F n (toData F R0)) at i
    exact BCq_cB_entry1_le_q_head1 F (RelData.BCqIter F n (toData F R0))
      (BCqIter_head_one_data F n R0 hbhd) i

/-- Type-3 (b-side inr) members of the (k, k−2) chain are (k−1)-adm, _of form
(depth ≥ k−1 only, so the depth-(k−1)-form is excluded by the WEIGHT: member
weight = weight r s vs the strict bound from the s-entries). -/
theorem maink_kk2_type3_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk3 : 3 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 2 - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqmid : (s ⟨k - 2, by omega⟩ : ℕ) = Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 2) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 2 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 2) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 2) - 1) R0 (s ⟨k - 2 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 2) (by omega) (by omega))
    ∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight r s →
        kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) (k - 1) := by
  classical
  intro D Bs Q i hwmem
  have hk1 : 1 ≤ k := by omega
  have hdepge : k - 1 ≤ Q.dep (Sum.inr (Sum.inr i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inr i)) = D.depB i + ((k - 2) - 1) := by
      have h1' := FixedOver.prependList_dep F Bs (sPrefix r s (k - 2) (by omega) (by omega)) (Sum.inr (Sum.inr i))
      have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
        dsimp [Bs, ofBstarOver, D]
      have hlen : (sPrefix r s (k - 2) (by omega) (by omega)).length = (k - 2) - 1 := by
        rw [sPrefix_length]
      rw [h1', h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  constructor
  · intro x hx
    by_cases hx1 : x < k - 3
    · have hxQ : x < Q.dep (Sum.inr (Sum.inr i)) := by
        have hlt : x < k - 1 := by omega
        exact lt_of_lt_of_le hlt hdepge
      have hv := member_prefix_pos F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
        (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd (Sum.inr (Sum.inr i)) x (by omega) hxQ
      have hv' : (Q.c (Sum.inr (Sum.inr i))) ⟨x, hxQ⟩ = s ⟨x, by omega⟩ := by
        simpa [Q, Bs, D] using hv
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
      rw [hv']
      have hs : (s ⟨x, by omega⟩ : ℕ) = pad0 s x := by
        have hxr : x < r := by
          have hx2 : x < k - 1 := by omega
          have hk1r : k - 1 ≤ r := by omega
          omega
        rw [pad0_of_lt s hxr]
      rw [hs]
      exact h1.1 x (by omega)
    · by_cases hx2 : x < k - 2
      · have hxj : x = (k - 2) - 1 := by omega
        rw [hxj]
        have hxQ : (k - 2) - 1 < Q.dep (Sum.inr (Sum.inr i)) := by
          have hlt : (k - 2) - 1 < k - 1 := by omega
          exact lt_of_lt_of_le hlt hdepge
        have hv := type3_sjadd_one_at F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
          (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd i hxQ
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
        rw [hv]
        omega
      · have hxk : x = k - 2 := by omega
        rw [hxk]
        have hp := type3_pad0_headAdd F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
          (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd i 1
        have hpos : k - 2 = (k - 2) - 1 + 1 := by omega
        rw [hpos]
        rw [hp]
        have hsucc : pad0 (headAdd (s ⟨k - 2 - 1, by omega⟩) (D.hdepB i) (D.cB i)) 1 =
            pad0 (D.cB i) 1 := by
          change pad0 (headAdd (s ⟨k - 2 - 1, by omega⟩) (D.hdepB i) (D.cB i)) (0 + 1) =
            pad0 (D.cB i) (0 + 1)
          rw [pad0_headAdd_succ (s ⟨k - 2 - 1, by omega⟩) (D.hdepB i) (D.cB i) 0]
        rw [hsucc]
        exact BCqIter_cB_entry1_le_q F (k - (k - 2) - 1) R0 hbhd
          (by omega : 1 ≤ k - (k - 2) - 1) i
  · intro hform
    rcases hform with ⟨hr1, hdep, hall, hlast⟩
    have hd : Q.dep (Sum.inr (Sum.inr i)) = k - 1 := by omega
    have hwps : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
        psum (Q.c (Sum.inr (Sum.inr i))) (k - 1) := by
      rw [← hd]
      exact (psum_self (Q.c (Sum.inr (Sum.inr i)))).symm
    have hwt : psum (Q.c (Sum.inr (Sum.inr i))) (k - 1) = weight r s := by
      rw [hwps] at hwmem
      exact hwmem
    have hsplit : psum (Q.c (Sum.inr (Sum.inr i))) (k - 1) =
        psum (Q.c (Sum.inr (Sum.inr i))) (k - 3) +
          pad0 (Q.c (Sum.inr (Sum.inr i))) (k - 3) +
          pad0 (Q.c (Sum.inr (Sum.inr i))) (k - 2) := by
      calc
        psum (Q.c (Sum.inr (Sum.inr i))) (k - 1)
            = psum (Q.c (Sum.inr (Sum.inr i))) (((k - 3) + 1) + 1) := by
                rw [show ((k - 3) + 1) + 1 = k - 1 by omega]
        _ = psum (Q.c (Sum.inr (Sum.inr i))) (k - 3) +
              pad0 (Q.c (Sum.inr (Sum.inr i))) (k - 3) +
              pad0 (Q.c (Sum.inr (Sum.inr i))) ((k - 3) + 1) := by
                rw [psum_succ, psum_succ]
        _ = psum (Q.c (Sum.inr (Sum.inr i))) (k - 3) +
              pad0 (Q.c (Sum.inr (Sum.inr i))) (k - 3) +
              pad0 (Q.c (Sum.inr (Sum.inr i))) (k - 2) := by
                rw [show (k - 3) + 1 = k - 2 by omega]
    have hfront : psum (Q.c (Sum.inr (Sum.inr i))) (k - 3) = psum s (k - 3) := by
      change (∑ x ∈ Finset.range (k - 3), pad0 (Q.c (Sum.inr (Sum.inr i))) x) =
        (∑ x ∈ Finset.range (k - 3), pad0 s x)
      apply Finset.sum_congr rfl
      intro x hx
      have hx3 : x < k - 3 := Finset.mem_range.mp hx
      have hxQ : x < Q.dep (Sum.inr (Sum.inr i)) := by
        have hlt : x < k - 1 := by omega
        exact lt_of_lt_of_le hlt hdepge
      have hv := member_prefix_pos F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
        (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd (Sum.inr (Sum.inr i)) x (by omega) hxQ
      have hv' : (Q.c (Sum.inr (Sum.inr i))) ⟨x, hxQ⟩ = s ⟨x, by omega⟩ := by
        simpa [Q, Bs, D] using hv
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
      rw [hv']
      have hs : (s ⟨x, by omega⟩ : ℕ) = pad0 s x := by
        have hxr : x < r := by omega
        rw [pad0_of_lt s hxr]
      rw [hs]
    have hv1 : pad0 (Q.c (Sum.inr (Sum.inr i))) (k - 3) =
        (s ⟨k - 3, by omega⟩ : ℕ) + 1 := by
      have hxQ : k - 3 < Q.dep (Sum.inr (Sum.inr i)) := by
        have hlt : k - 3 < k - 1 := by omega
        exact lt_of_lt_of_le hlt hdepge
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
      have hm1 : (k - 2) - 1 < Q.dep (Sum.inr (Sum.inr i)) := by omega
      have hv := type3_sjadd_one_at F r s k (k - 2) hk1 hkr (by omega : 1 ≤ k - 2)
        (by omega : k - 2 ≤ k - 1) hbig hsj R0 hbhd i hm1
      have hidx : (⟨k - 3, hxQ⟩ : Fin (Q.dep (Sum.inr (Sum.inr i)))) =
          ⟨(k - 2) - 1, hm1⟩ := by
        apply Fin.ext
        change k - 3 = (k - 2) - 1
        omega
      rw [hidx]
      exact hv
    have hv2 : pad0 (Q.c (Sum.inr (Sum.inr i))) (k - 2) = Nat.card F := by
      have hxQ : k - 2 < Q.dep (Sum.inr (Sum.inr i)) := by
        rw [hd]
        omega
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
      have hlasti : ((Q.c (Sum.inr (Sum.inr i))) ⟨Q.dep (Sum.inr (Sum.inr i)) - 1, by omega⟩ : ℕ) =
          Nat.card F := hlast
      have hidx : (⟨k - 2, hxQ⟩ : Fin (Q.dep (Sum.inr (Sum.inr i)))) =
          ⟨Q.dep (Sum.inr (Sum.inr i)) - 1, by omega⟩ := by
        apply Fin.ext
        change k - 2 = Q.dep (Sum.inr (Sum.inr i)) - 1
        rw [hd]
        omega
      rw [hidx]
      exact hlasti
    have hw' : psum (Q.c (Sum.inr (Sum.inr i))) (k - 1) =
        psum s (k - 3) + ((s ⟨k - 3, by omega⟩ : ℕ) + 1) + Nat.card F := by
      rw [hsplit, hfront, hv1, hv2]
    have hpk : psum s k =
        psum s (k - 3) + pad0 s (k - 3) + pad0 s (k - 2) + pad0 s (k - 1) := by
      calc
        psum s k = psum s (((k - 3) + 2) + 1) := by
              rw [show ((k - 3) + 2) + 1 = k by omega]
        _ = psum s (k - 3) + pad0 s (k - 3) + pad0 s ((k - 3) + 1) + pad0 s ((k - 3) + 2) := by
              rw [psum_succ, psum_succ, psum_succ]
        _ = psum s (k - 3) + pad0 s (k - 3) + pad0 s (k - 2) + pad0 s (k - 1) := by
              rw [show (k - 3) + 1 = k - 2 by omega]
              rw [show (k - 3) + 2 = k - 1 by omega]
    have hmonok : psum s k ≤ weight r s := psum_le_weight s k
    have hltpk : psum (Q.c (Sum.inr (Sum.inr i))) (k - 1) < psum s k := by
      rw [hw', hpk]
      have hp3 : pad0 s (k - 3) = (s ⟨k - 3, by omega⟩ : ℕ) := by
        have hxr : k - 3 < r := by omega
        rw [pad0_of_lt s hxr]
      have hp2 : pad0 s (k - 2) = Nat.card F := by
        have hxr : k - 2 < r := by omega
        rw [pad0_of_lt s hxr]
        exact hqmid
      have hp1 : pad0 s (k - 1) = (s ⟨k - 1, by omega⟩ : ℕ) := by
        have hxr : k - 1 < r := by omega
        rw [pad0_of_lt s hxr]
      rw [hp3, hp2, hp1]
      have hq2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    exact (ne_of_lt (lt_of_lt_of_le hltpk hmonok)) hwt

end ZagierHoffmanPositiveChar
