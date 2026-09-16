import Submission.ZagierHoffmanProof.StepL109
import Submission.ZagierHoffmanProof.StepM1
import Submission.ZagierHoffmanProof.StepL107
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L110: generic (k,k−1) chain members are (k−1)-admissible (SESSION 256)

The k-symbolic member (k−1)-adm facts of the (k, k−1) CASE-1 splice (the
"resisting conjunct" recorded in SESSION 254): over the zeta_214 (k, k−1) chain
lets (D := BCqIter F (k−(k−1)−1) (toData R0), B*_{s⟨k−1−1⟩}, front
sPrefix r s (k−1)), every type-1 (i₀ ≠ u), type-2 and type-3 member is
(k−1)-admissible — from (i) depth ≥ k (front (k−2) entries + ≥ 1/1/2 more) which
kills the depth-(k−1) form, and (ii) the pad0 entries x < k−1: the front
positions x < k−2 share s-values (member_prefix_pos; ≤ q by the input's
(k−1)-admissibility) and the position k−2 = j−1 holds s⟨k−2⟩ (type 1/2, via
type{1,2}_sj_at_jm1) or s⟨k−2⟩+1 (type 3, via type3_sjadd_one_at) — both ≤ q by
hsj : s⟨k−2⟩ < q.

These are the generic-k ports of StepL87's level3_j2_type*_twoAdm_of at
(k, j) = (k, k−1).  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- From depth ≥ k and the pad0 entries x < k−1 all ≤ q, the tuple is
(k−1)-admissible (the depth-form of depth ≤ k−1 is impossible). -/
lemma kAdm_pred_of_pad0_le (q k : ℕ) {r : ℕ} (t : Fin r → ℕ+) (hk : 1 ≤ k) (hr : k ≤ r)
    (h : ∀ x : ℕ, x < k - 1 → pad0 t x ≤ q) : kAdmissible q t (k - 1) := by
  constructor
  · intro x hx
    exact h x hx
  · intro hform
    rcases hform with ⟨hr1, hrk, hall, hlast⟩
    omega

/-- Type-1 (a-side, i₀ ≠ u) members of the (k, k−1) chain are (k−1)-adm, _of form. -/
theorem maink_kk1_type1_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk2 : 2 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 1 - 1, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 1) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 1 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 1) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 1) - 1) R0 (s ⟨k - 1 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 1) (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u →
      kAdmissible (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀))) (k - 1) := by
  classical
  intro D Bs Q i₀ hi
  have hk1 : 1 ≤ k := by omega
  let idxA : D.ιA := RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) (i₀ : (toData F R0).ιA)
  have hdepge : k ≤ Q.dep (Sum.inl idxA) := by
    have hQd : Q.dep (Sum.inl idxA) = (toData F R0).depA i₀ + (k - (k - 1) - 1) + 1 + ((k - 1) - 1) := by
      have h1' := FixedOver.prependList_dep F Bs (sPrefix r s (k - 1) (by omega) (by omega)) (Sum.inl idxA)
      have h2 : Bs.dep (Sum.inl idxA) = D.depA idxA + 1 := by
        dsimp [Bs, ofBstarOver, D]
      have hlen : (sPrefix r s (k - 1) (by omega) (by omega)).length = (k - 1) - 1 := by
        rw [sPrefix_length]
      have hd := RelData.BCqIter_depA_at F (k - (k - 1) - 1) (toData F R0) i₀
      rw [h1', h2, hlen, hd]
    rw [hQd]
    have hda : 0 < (toData F R0).depA i₀ := by
      change 0 < R0.depA i₀
      exact R0.hdepA i₀
    omega
  refine kAdm_pred_of_pad0_le (Nat.card F) k (Q.c (Sum.inl idxA)) hk1 hdepge ?_
  intro x hx
  by_cases hxpre : x < k - 2
  · have hxQ : x < Q.dep (Sum.inl idxA) := by
      have hlt : x < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := member_prefix_pos F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbig hsj R0 hbhd (Sum.inl idxA) x (by omega) hxQ
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
  · have hxj : x = (k - 1) - 1 := by omega
    rw [hxj]
    have hxQ : (k - 1) - 1 < Q.dep (Sum.inl idxA) := by
      have hlt : (k - 1) - 1 < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := type1_sj_at_jm1 F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbig hsj R0 hbhd idxA hxQ
    rw [pad0_of_lt (Q.c (Sum.inl idxA)) hxQ]
    rw [hv]
    exact le_of_lt hsj

/-- Type-2 (b-side inl) members of the (k, k−1) chain are (k−1)-adm, _of form. -/
theorem maink_kk1_type2_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk2 : 2 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 1 - 1, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 1) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 1 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 1) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 1) - 1) R0 (s ⟨k - 1 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 1) (by omega) (by omega))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) (k - 1) := by
  classical
  intro D Bs Q i
  have hk1 : 1 ≤ k := by omega
  have hdepge : k ≤ Q.dep (Sum.inr (Sum.inl i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 + ((k - 1) - 1) := by
      have h1' := FixedOver.prependList_dep F Bs (sPrefix r s (k - 1) (by omega) (by omega)) (Sum.inr (Sum.inl i))
      have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
        dsimp [Bs, ofBstarOver, D]
      have hlen : (sPrefix r s (k - 1) (by omega) (by omega)).length = (k - 1) - 1 := by
        rw [sPrefix_length]
      rw [h1', h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  refine kAdm_pred_of_pad0_le (Nat.card F) k (Q.c (Sum.inr (Sum.inl i))) hk1 hdepge ?_
  intro x hx
  by_cases hxpre : x < k - 2
  · have hxQ : x < Q.dep (Sum.inr (Sum.inl i)) := by
      have hlt : x < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := member_prefix_pos F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbig hsj R0 hbhd (Sum.inr (Sum.inl i)) x (by omega) hxQ
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
  · have hxj : x = (k - 1) - 1 := by omega
    rw [hxj]
    have hxQ : (k - 1) - 1 < Q.dep (Sum.inr (Sum.inl i)) := by
      have hlt : (k - 1) - 1 < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := type2_sj_at_jm1 F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbig hsj R0 hbhd i hxQ
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hxQ]
    rw [hv]
    exact le_of_lt hsj

/-- Type-3 (b-side inr) members of the (k, k−1) chain are (k−1)-adm, _of form
(the +1 entry at position k−2 stays ≤ q by hsj). -/
theorem maink_kk1_type3_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk2 : 2 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 1 - 1, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 1) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 1 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 1) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 1) - 1) R0 (s ⟨k - 1 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 1) (by omega) (by omega))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) (k - 1) := by
  classical
  intro D Bs Q i
  have hk1 : 1 ≤ k := by omega
  have hdepge : k ≤ Q.dep (Sum.inr (Sum.inr i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inr i)) = D.depB i + ((k - 1) - 1) := by
      have h1' := FixedOver.prependList_dep F Bs (sPrefix r s (k - 1) (by omega) (by omega)) (Sum.inr (Sum.inr i))
      have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
        dsimp [Bs, ofBstarOver, D]
      have hlen : (sPrefix r s (k - 1) (by omega) (by omega)).length = (k - 1) - 1 := by
        rw [sPrefix_length]
      rw [h1', h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  refine kAdm_pred_of_pad0_le (Nat.card F) k (Q.c (Sum.inr (Sum.inr i))) hk1 hdepge ?_
  intro x hx
  by_cases hxpre : x < k - 2
  · have hxQ : x < Q.dep (Sum.inr (Sum.inr i)) := by
      have hlt : x < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := member_prefix_pos F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbig hsj R0 hbhd (Sum.inr (Sum.inr i)) x (by omega) hxQ
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
  · have hxj : x = (k - 1) - 1 := by omega
    rw [hxj]
    have hxQ : (k - 1) - 1 < Q.dep (Sum.inr (Sum.inr i)) := by
      have hlt : (k - 1) - 1 < k := by omega
      exact lt_of_lt_of_le hlt hdepge
    have hv := type3_sjadd_one_at F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbig hsj R0 hbhd i hxQ
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
    rw [hv]
    omega

end ZagierHoffmanPositiveChar
