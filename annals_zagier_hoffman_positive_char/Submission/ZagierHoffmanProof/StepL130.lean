import Submission.ZagierHoffmanProof.StepL129
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L130: the type-2 member's (k−1)-front bound and admissibility at j = k−3
(SESSION 258w)

The b-side analogue of StepL126's front facts, at j = k−3 (so the tail is the
level-2 BC_q-iterate and only the fiber's entry-1 is needed):
  • ★ `maink_type2_front_le`: every entry 0..k−2 of a type-2 member is ≤ q —
      x < j−1: the front list (= s's entries, via prependList_c_front_value +
      sPrefix_reverse_value);
      x = j−1: `type2_sj_at_jm1` (= s⟨j−1⟩ ≤ q from the (k−1)-admissibility);
      x = j: `type2_one_at_j` (= 1 ≤ q);
      x = j+1 = k−2: `type2_tail_pad0` + `BCqIter_cB_entry1_le_q` (the level-2
      fiber's entry-1 ≤ q).
  • ★ `maink_type2_k1adm`: hence the type-2 member is `(k−1)`-admissible, GIVEN
      the depth bound `k ≤ Q.dep (member)` (cond2 follows by omega — the
      depth-form witness r ≤ k−1 is impossible).  The depth bound itself
      (`maink_b_dep_ge`: the level-n b-fibers have depth ≥ n+1, so that
      Q.dep ≥ k) is the next small lemma.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ Every entry `0..k−2` of a type-2 member is at most `q` at `j = k−3`. -/
theorem maink_type2_front_le (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk1 : 1 ≤ k) (hk4 : 4 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 3 - 1, by omega⟩ : ℕ) < Nat.card F)
    (hadm : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 3) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 3 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 3) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 3) - 1) R0 (s ⟨k - 3 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 3) (by omega) (by omega))
    ∀ i : D.ιB, ∀ x : ℕ, x < k - 1 →
      pad0 (Q.c (Sum.inr (Sum.inl i))) x ≤ Nat.card F := by
  classical
  intro D Bs Q i x hx
  have hq1 : 1 ≤ Nat.card F := by have h2 := card_ge_two F; omega
  -- depth of the member: ≥ j + 1 (so the entry conversions are valid below)
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) = Bs.dep (Sum.inr (Sum.inl i)) +
      (sPrefix r s (k - 3) (by omega) (by omega)).length :=
    FixedOver.prependList_dep F Bs (sPrefix r s (k - 3) (by omega) (by omega)) (Sum.inr (Sum.inl i))
  have hBsdep : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
    dsimp [Bs, ofBstarOver]
  have hlen : (sPrefix r s (k - 3) (by omega) (by omega)).length = k - 3 - 1 :=
    sPrefix_length r s (k - 3) (by omega) (by omega)
  have hdepj : k - 3 < Q.dep (Sum.inr (Sum.inl i)) := by
    rw [hQdep, hBsdep, hlen]
    have h1 : 0 < D.depB i := D.hdepB i
    omega
  by_cases hxj : (k - 3 : ℕ) ≤ x
  · by_cases hxj' : (k - 3 : ℕ) = x
    · -- x = j: the entry is 1
      rw [← hxj']
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hdepj]
      rw [type2_one_at_j F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj R0 hbhd i hdepj]
      exact hq1
    · -- x = j+1 = k−2: the tail's first entry = the level-2 fiber's entry-1
      have hxe : x = k - 2 := by omega
      have hjm1 : (k - 3) + 1 ≤ x := by omega
      have hsub : x - (k - 3) - 1 = 0 := by omega
      rw [hxe]
      rw [show k - 2 = (k - 3) + 1 + 0 by omega]
      rw [type2_tail_pad0 F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj R0 hbhd i 0]
      -- pad0 (expTail (D.cB i)) 0 = pad0 (D.cB i) 1
      have hexp : pad0 (expTail (D.cB i)) 0 = pad0 (D.cB i) 1 :=
        (pad0_succ_expTail (t := D.cB i) (a := 0)).symm
      rw [hexp]
      exact BCqIter_cB_entry1_le_q F (k - (k - 3) - 1) R0 hbhd (by omega) i
  · have hxjlt : x < k - 3 := by omega
    by_cases hxj1 : x = k - 3 - 1
    · -- x = j−1: the entry is s⟨j−1⟩
      subst hxj1
      have hdep' : k - 3 - 1 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hdep']
      rw [type2_sj_at_jm1 F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj R0 hbhd i hdep']
      rw [← pad0_of_lt s (by omega : k - 3 - 1 < r)]
      exact hadm (k - 3 - 1) (by omega)
    · -- x < j−1: the front list, i.e. s's entries
      have hmf : x < (sPrefix r s (k - 3) (by omega) (by omega)).length := by
        rw [hlen]; omega
      have hmx : x < Q.dep (Sum.inr (Sum.inl i)) := by omega
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hmx]
      rw [prependList_c_front_value F Bs (sPrefix r s (k - 3) (by omega) (by omega))
        (Sum.inr (Sum.inl i)) x hmx hmf]
      rw [sPrefix_reverse_value r s (k - 3) (by omega) (by omega) x (by simpa using hmf)]
      rw [← pad0_of_lt s (by omega : x < r)]
      exact hadm x (by omega)

/-- ★ The type-2 member is `(k−1)`-admissible at `j = k−3`, given the depth bound
(the depth-form witness `r ≤ k−1` is then impossible). -/
theorem maink_type2_k1adm (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk1 : 1 ≤ k) (hk4 : 4 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 3 - 1, by omega⟩ : ℕ) < Nat.card F)
    (hadm : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 3) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 3 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 3) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 3) - 1) R0 (s ⟨k - 3 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 3) (by omega) (by omega))
    ∀ i : D.ιB, k ≤ Q.dep (Sum.inr (Sum.inl i)) →
      kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) (k - 1) := by
  classical
  intro D Bs Q i hdep
  refine ⟨?_, ?_⟩
  · intro x hx
    exact maink_type2_front_le F r s k hk1 hk4 hkr hbig hsj hadm R0 hbhd i x hx
  · intro hwit
    rcases hwit with ⟨hr1, hrle, -, -⟩
    omega

end ZagierHoffmanPositiveChar
