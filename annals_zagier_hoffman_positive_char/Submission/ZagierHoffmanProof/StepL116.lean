import Submission.ZagierHoffmanProof.StepL113
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L116: the (k, k−3) type-1 member is (k−1)-adm — obligation (2)'s type-1
depth-based segment (SESSION 258e)

Obligation (2) of the StepL115 skeleton (maink_case1_kk3, the CASE-1 j = k−3
splice) is decomposed by member type; THIS module closes its type-1 segment:
★ maink_kk3_type1_k1adm — every type-1 (a-side, i₀ ≠ u) member of the (k,k−3)
chain is (k−1)-adm, DEPTH-BASED (no weight, no deep-entry content): over the
zeta (k,k−3) chain lets (D := BCqIter F (k−(k−3)−1) (toData R0) — TWO BC_q
iterates; B*_{s⟨k−3−1⟩}; front sPrefix r s (k−3)), the member's positions
x < k−1 are: the front (length k−4 = (k−3)−1, positions 0..k−5 share s-values
≤ q by the input's (k−1)-adm h1), the merged head at position k−4 = j−1
(value s⟨k−4⟩ < q by hsj, via type1_sj_at_jm1), and the two iterate a-heads q
at positions k−3, k−2 (via type1_pad0_shift + BCqIter_cA_pad0_front at t = 0,1
— the (k,j)-generic shift lemmas).  Depth = front + 1 + (R0.depA + 2) ≥ k.
NEXT: the (k,k−3) type-2 (weight-based at depth k−1) and type-3
(¬(k−1)-adm members → route via maink_not_k1adm_member_e) segments, then the
maink_case1_kk3 splice (StepL113's script at j = k−3).  theorem_B/D remain
ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Type-1 (a-side, i₀ ≠ u) members of the (k, k−3) chain are (k−1)-adm, _of form
(depth-based: front + merged head + two iterate q-heads). -/
theorem maink_kk3_type1_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk4 : 4 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 3 - 1, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 3) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 3 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 3) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 3) - 1) R0 (s ⟨k - 3 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 3) (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u →
      kAdmissible (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 3) - 1) (toData F R0) i₀))) (k - 1) := by
  classical
  intro D Bs Q i₀ hi
  have hk1 : 1 ≤ k := by omega
  let idxA : D.ιA := RelData.iterIdx F (k - (k - 3) - 1) (toData F R0) (i₀ : (toData F R0).ιA)
  have hdepge : k ≤ Q.dep (Sum.inl idxA) := by
    have hQd : Q.dep (Sum.inl idxA) = (toData F R0).depA i₀ + (k - (k - 3) - 1) + 1 + ((k - 3) - 1) := by
      have h1' := FixedOver.prependList_dep F Bs (sPrefix r s (k - 3) (by omega) (by omega)) (Sum.inl idxA)
      have h2 : Bs.dep (Sum.inl idxA) = D.depA idxA + 1 := by
        dsimp [Bs, ofBstarOver, D]
      have hlen : (sPrefix r s (k - 3) (by omega) (by omega)).length = (k - 3) - 1 := by
        rw [sPrefix_length]
      have hd := RelData.BCqIter_depA_at F (k - (k - 3) - 1) (toData F R0) i₀
      rw [h1', h2, hlen, hd]
    rw [hQd]
    have hda : 0 < (toData F R0).depA i₀ := by
      change 0 < R0.depA i₀
      exact R0.hdepA i₀
    omega
  refine kAdm_pred_of_pad0_le (Nat.card F) k (Q.c (Sum.inl idxA)) hk1 hdepge ?_
  intro x hx
  by_cases hx1 : x < k - 4
  · have hxQ : x < Q.dep (Sum.inl idxA) := by
      have hlt : x < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := member_prefix_pos F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
      (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd (Sum.inl idxA) x (by omega) hxQ
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
  · by_cases hx2 : x < k - 3
    · have hxj : x = (k - 3) - 1 := by omega
      rw [hxj]
      have hxQ : (k - 3) - 1 < Q.dep (Sum.inl idxA) := by
        have hlt : (k - 3) - 1 < k := by omega
        exact lt_of_lt_of_le hlt hdepge
      have hv := type1_sj_at_jm1 F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
        (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd idxA hxQ
      rw [pad0_of_lt (Q.c (Sum.inl idxA)) hxQ]
      rw [hv]
      exact le_of_lt hsj
    · by_cases hx3 : x < k - 2
      · have hxk : x = k - 3 := by omega
        rw [hxk]
        have hsh : pad0 (Q.c (Sum.inl idxA)) (k - 3) = Nat.card F := by
          have hge : k - 3 ≥ k - 3 := le_rfl
          have hsh0 := type1_pad0_shift F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
            (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd idxA (k - 3) hge
          have hsub : (k - 3) - (k - 3) = 0 := by omega
          rw [hsh0, hsub]
          have hf := BCqIter_cA_pad0_front F (k - (k - 3) - 1) R0 i₀ 0 (by omega : 0 < k - (k - 3) - 1)
          simpa [idxA] using hf
        rw [hsh]
      · have hxk : x = k - 2 := by omega
        rw [hxk]
        have hsh : pad0 (Q.c (Sum.inl idxA)) (k - 2) = Nat.card F := by
          have hge : k - 2 ≥ k - 3 := by omega
          have hsh0 := type1_pad0_shift F r s k (k - 3) hk1 hkr (by omega : 1 ≤ k - 3)
            (by omega : k - 3 ≤ k - 1) hbig hsj R0 hbhd idxA (k - 2) hge
          have hsub : (k - 2) - (k - 3) = 1 := by omega
          rw [hsh0, hsub]
          have hf := BCqIter_cA_pad0_front F (k - (k - 3) - 1) R0 i₀ 1 (by omega : 1 < k - (k - 3) - 1)
          simpa [idxA] using hf
        rw [hsh]

end ZagierHoffmanPositiveChar
