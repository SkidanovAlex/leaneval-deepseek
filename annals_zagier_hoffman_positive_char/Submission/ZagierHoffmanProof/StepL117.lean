import Submission.ZagierHoffmanProof.StepL116
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L117: the (k, k−3) type-2 member is (k−1)-adm — obligation (2)'s type-2
weight-based segment (SESSION 258f)

★ maink_kk3_type2_k1adm — every type-2 (b-side inl) member of the (k,k−3) chain
is (k−1)-adm, by the WEIGHT argument for the depth-(k−1)-form (the member depth
= (k−4) + depB + 1 can be exactly k−1 when depB = 2): over the zeta (k,k−3)
chain lets (D := BCqIter F (k−(k−3)−1) (toData R0), B*_{s⟨k−3−1⟩}, front
sPrefix r s (k−3)), the member's positions x < k−1 are: the front (length k−4,
s-values ≤ q by h1), the merged head at k−4 = j−1 (value s⟨k−4⟩ < q by hsj,
type2_sj_at_jm1), D.cB₀ = 1 at k−3 (type2_pad0_shift t=0 + the iterate head-one),
and D.cB₁ ≤ q at k−2 (type2_pad0_shift t=1 + BCqIter_cB_entry1_le_q at iterate
count k−(k−3)−1 ≥ 1).  cond2: from the depth-form witness (r = Q.dep ≤ k−1,
k−1 ≤ Q.dep) get Q.dep = k−1; weight(member) = psum s (k−4) + s⟨k−4⟩ + 1 + q
(psum_succ-split; hlast = q at position k−2) while weight r s ≥ psum s k =
psum s (k−4) + s⟨k−4⟩ + q + q + s⟨k−1⟩ (hqmid: s⟨k−3⟩ = q; hqmid1: s⟨k−2⟩ = q)
> weight(member) — contradicts hwmem.  Port of StepL112's type-3 weight
machinery at the (k,k−3) front length k−4 (three pad positions after the front).
NEXT: the (k,k−3) type-3 segment, then the maink_case1_kk3 splice.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Type-2 (b-side inl) members of the (k, k−3) chain are (k−1)-adm, _of form
(depth-(k−1)-form excluded by the weight). -/
theorem maink_kk3_type2_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk4 : 4 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 3 - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqmid : (s ⟨k - 3, by omega⟩ : ℕ) = Nat.card F)
    (hqmid1 : (s ⟨k - 2, by omega⟩ : ℕ) = Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 3) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 3 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 3) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 3) - 1) R0 (s ⟨k - 3 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 3) (by omega) (by omega))
    ∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight r s →
        kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) (k - 1) := by
  classical
  intro D Bs Q i hwmem
  have hk1 : 1 ≤ k := by omega
  have hdepge : k - 1 ≤ Q.dep (Sum.inr (Sum.inl i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 + ((k - 3) - 1) := by
      have h1' := FixedOver.prependList_dep F Bs (sPrefix r s (k - 3) (by omega) (by omega)) (Sum.inr (Sum.inl i))
      have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
        dsimp [Bs, ofBstarOver, D]
      have hlen : (sPrefix r s (k - 3) (by omega) (by omega)).length = (k - 3) - 1 := by
        rw [sPrefix_length]
      rw [h1', h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  constructor
  · intro x hx
    by_cases hx1 : x < k - 4
    · have hxQ : x < Q.dep (Sum.inr (Sum.inl i)) := by
        have hlt : x < k - 1 := by omega
        exact lt_of_lt_of_le hlt hdepge
      have hv := member_prefix_pos F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
        (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd (Sum.inr (Sum.inl i)) x (by omega) hxQ
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
    · by_cases hx2 : x < k - 3
      · have hxj : x = (k - 3) - 1 := by omega
        rw [hxj]
        have hxQ : (k - 3) - 1 < Q.dep (Sum.inr (Sum.inl i)) := by
          have hlt : (k - 3) - 1 < k - 1 := by omega
          exact lt_of_lt_of_le hlt hdepge
        have hv := type2_sj_at_jm1 F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
          (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd i hxQ
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hxQ]
        rw [hv]
        exact le_of_lt hsj
      · by_cases hx3 : x < k - 2
        · have hxk : x = k - 3 := by omega
          rw [hxk]
          have hsh : pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 3) = 1 := by
            have hsh0 := type2_pad0_shift F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
              (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd i 0
            have hj0 : (k - 3) + 0 = k - 3 := by omega
            rw [← hj0]
            rw [hsh0]
            have hb0 := BCqIter_head_one_data F (k - (k - 3) - 1) R0 hbhd i
            have hz : 0 < D.depB i := D.hdepB i
            rw [pad0_of_lt (D.cB i) hz]
            simpa [D] using hb0
          rw [hsh]
          have hq1 : 1 ≤ Nat.card F := by
            have h2 : 2 ≤ Nat.card F := card_ge_two F
            omega
          exact hq1
        · have hxk : x = k - 2 := by omega
          rw [hxk]
          have hsh : pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 2) ≤ Nat.card F := by
            have hsh0 := type2_pad0_shift F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
              (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd i 1
            have hsum : (k - 3) + 1 = k - 2 := by omega
            rw [← hsum]
            rw [hsh0]
            exact BCqIter_cB_entry1_le_q F (k - (k - 3) - 1) R0 hbhd
              (by omega : 1 ≤ k - (k - 3) - 1) i
          exact hsh
  · intro hform
    rcases hform with ⟨hr1, hdep, hall, hlast⟩
    have hd : Q.dep (Sum.inr (Sum.inl i)) = k - 1 := by omega
    have hwps : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) =
        psum (Q.c (Sum.inr (Sum.inl i))) (k - 1) := by
      rw [← hd]
      exact (psum_self (Q.c (Sum.inr (Sum.inl i)))).symm
    have hwt : psum (Q.c (Sum.inr (Sum.inl i))) (k - 1) = weight r s := by
      rw [hwps] at hwmem
      exact hwmem
    have hsplit : psum (Q.c (Sum.inr (Sum.inl i))) (k - 1) =
        psum (Q.c (Sum.inr (Sum.inl i))) (k - 4) +
          pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 4) +
          pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 3) +
          pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 2) := by
      calc
        psum (Q.c (Sum.inr (Sum.inl i))) (k - 1)
            = psum (Q.c (Sum.inr (Sum.inl i))) (((k - 4) + 2) + 1) := by
                rw [show ((k - 4) + 2) + 1 = k - 1 by omega]
        _ = psum (Q.c (Sum.inr (Sum.inl i))) (k - 4) +
              pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 4) +
              pad0 (Q.c (Sum.inr (Sum.inl i))) ((k - 4) + 1) +
              pad0 (Q.c (Sum.inr (Sum.inl i))) ((k - 4) + 2) := by
                rw [psum_succ, psum_succ, psum_succ]
        _ = psum (Q.c (Sum.inr (Sum.inl i))) (k - 4) +
              pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 4) +
              pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 3) +
              pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 2) := by
                rw [show (k - 4) + 1 = k - 3 by omega]
                rw [show (k - 4) + 2 = k - 2 by omega]
    have hfront : psum (Q.c (Sum.inr (Sum.inl i))) (k - 4) = psum s (k - 4) := by
      change (∑ x ∈ Finset.range (k - 4), pad0 (Q.c (Sum.inr (Sum.inl i))) x) =
        (∑ x ∈ Finset.range (k - 4), pad0 s x)
      apply Finset.sum_congr rfl
      intro x hx
      have hx4 : x < k - 4 := Finset.mem_range.mp hx
      have hxQ : x < Q.dep (Sum.inr (Sum.inl i)) := by
        have hlt : x < k - 1 := by omega
        exact lt_of_lt_of_le hlt hdepge
      have hv := member_prefix_pos F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
        (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd (Sum.inr (Sum.inl i)) x (by omega) hxQ
      have hv' : (Q.c (Sum.inr (Sum.inl i))) ⟨x, hxQ⟩ = s ⟨x, by omega⟩ := by
        simpa [Q, Bs, D] using hv
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hxQ]
      rw [hv']
      have hs : (s ⟨x, by omega⟩ : ℕ) = pad0 s x := by
        have hxr : x < r := by omega
        rw [pad0_of_lt s hxr]
      rw [hs]
    have hv1 : pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 4) =
        (s ⟨k - 4, by omega⟩ : ℕ) := by
      have hxQ : k - 4 < Q.dep (Sum.inr (Sum.inl i)) := by
        have hlt : k - 4 < k - 1 := by omega
        exact lt_of_lt_of_le hlt hdepge
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hxQ]
      have hm1 : (k - 3) - 1 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      have hv := type2_sj_at_jm1 F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
        (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd i hm1
      have hidx : (⟨k - 4, hxQ⟩ : Fin (Q.dep (Sum.inr (Sum.inl i)))) =
          ⟨(k - 3) - 1, hm1⟩ := by
        apply Fin.ext
        change k - 4 = (k - 3) - 1
        omega
      rw [hidx]
      exact hv
    have hv2 : pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 3) = 1 := by
      have hxQ : k - 3 < Q.dep (Sum.inr (Sum.inl i)) := by
        have hlt : k - 3 < k - 1 := by omega
        exact lt_of_lt_of_le hlt hdepge
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hxQ]
      have hm1 : (k - 3) + 0 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      have hv := type2_pad0_shift F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
        (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd i 0
      have hcv : ((Q.c (Sum.inr (Sum.inl i))) ⟨k - 3, hxQ⟩ : ℕ) = 1 := by
        have hidx : (⟨k - 3, hxQ⟩ : Fin (Q.dep (Sum.inr (Sum.inl i)))) =
            ⟨(k - 3) + 0, hm1⟩ := by
          apply Fin.ext
          change k - 3 = (k - 3) + 0
          omega
        rw [hidx]
        have hb0 := BCqIter_head_one_data F (k - (k - 3) - 1) R0 hbhd i
        have hz : 0 < D.depB i := D.hdepB i
        -- hv : pad0 member ((k−3)+0) = pad0 (D.cB i) 0 ; unfold member value at (k−3)+0:
        have hv' : ((Q.c (Sum.inr (Sum.inl i))) ⟨(k - 3) + 0, hm1⟩ : ℕ) =
            pad0 (D.cB i) 0 := by
          have hp0 := pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hm1
          rw [← hp0]
          exact hv
        rw [hv']
        rw [pad0_of_lt (D.cB i) hz]
        simpa [D] using hb0
      exact hcv
    have hv3 : pad0 (Q.c (Sum.inr (Sum.inl i))) (k - 2) = Nat.card F := by
      have hxQ : k - 2 < Q.dep (Sum.inr (Sum.inl i)) := by
        rw [hd]
        omega
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hxQ]
      have hlasti : ((Q.c (Sum.inr (Sum.inl i))) ⟨Q.dep (Sum.inr (Sum.inl i)) - 1, by omega⟩ : ℕ) =
          Nat.card F := hlast
      have hidx : (⟨k - 2, hxQ⟩ : Fin (Q.dep (Sum.inr (Sum.inl i)))) =
          ⟨Q.dep (Sum.inr (Sum.inl i)) - 1, by omega⟩ := by
        apply Fin.ext
        change k - 2 = Q.dep (Sum.inr (Sum.inl i)) - 1
        rw [hd]
        omega
      rw [hidx]
      exact hlasti
    have hw' : psum (Q.c (Sum.inr (Sum.inl i))) (k - 1) =
        psum s (k - 4) + (s ⟨k - 4, by omega⟩ : ℕ) + 1 + Nat.card F := by
      rw [hsplit, hfront, hv1, hv2, hv3]
    have hpk : psum s k =
        psum s (k - 4) + pad0 s (k - 4) + pad0 s (k - 3) + pad0 s (k - 2) +
          pad0 s (k - 1) := by
      calc
        psum s k = psum s (((k - 4) + 3) + 1) := by
              rw [show ((k - 4) + 3) + 1 = k by omega]
        _ = psum s (k - 4) + pad0 s (k - 4) + pad0 s ((k - 4) + 1) +
              pad0 s ((k - 4) + 2) + pad0 s ((k - 4) + 3) := by
              rw [psum_succ, psum_succ, psum_succ, psum_succ]
        _ = psum s (k - 4) + pad0 s (k - 4) + pad0 s (k - 3) + pad0 s (k - 2) +
              pad0 s (k - 1) := by
              rw [show (k - 4) + 1 = k - 3 by omega]
              rw [show (k - 4) + 2 = k - 2 by omega]
              rw [show (k - 4) + 3 = k - 1 by omega]
    have hmonok : psum s k ≤ weight r s := psum_le_weight s k
    have hltpk : psum (Q.c (Sum.inr (Sum.inl i))) (k - 1) < psum s k := by
      rw [hw', hpk]
      have hp4 : pad0 s (k - 4) = (s ⟨k - 4, by omega⟩ : ℕ) := by
        have hxr : k - 4 < r := by omega
        rw [pad0_of_lt s hxr]
      have hp3 : pad0 s (k - 3) = Nat.card F := by
        have hxr : k - 3 < r := by omega
        rw [pad0_of_lt s hxr]
        exact hqmid
      have hp2 : pad0 s (k - 2) = Nat.card F := by
        have hxr : k - 2 < r := by omega
        rw [pad0_of_lt s hxr]
        exact hqmid1
      have hp1 : pad0 s (k - 1) = (s ⟨k - 1, by omega⟩ : ℕ) := by
        have hxr : k - 1 < r := by omega
        rw [pad0_of_lt s hxr]
      rw [hp4, hp3, hp2, hp1]
      have hq2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    exact (ne_of_lt (lt_of_lt_of_le hltpk hmonok)) hwt

end ZagierHoffmanPositiveChar
