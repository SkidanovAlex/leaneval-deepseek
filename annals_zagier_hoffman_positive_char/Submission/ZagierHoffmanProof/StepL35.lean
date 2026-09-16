import Submission.ZagierHoffmanProof.StepL34
import Submission.ZagierHoffmanProof.StepL33

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L35: the CASE-1 Step-1 ζ-decomposition (paper (2.14)) — G1 + G2a assembly

★ `prop212_step1` is the Prop-3.2-algorithm "Step 1" for CASE 1 (`s_k > q`, with the
`(k−1)`-admissible front `s₁..s_{k−1} ≤ q`): it ∃-packages the whole Lemma-2.9 chain
at the configuration `r s k j` — the binary relation `R0` with distinguished
coefficient-`1` output `u` of depth `(r−k)+1` and tuple `bstarBase` (= `(s_k,…,s_r)`),
the `1`-headedness of the `b`-side, the `D Bs Q` chain, and then
  (REL)  ζ_A s + (type-1 sum over `i₀ ≠ u`) + (type-2 sum) + (type-3 sum) = 0
        [zeta_214_reindexed at the `lemma_2_9_config_data` instance],
  (T1)   type-1 members (`i₀ ≠ u`): weight = `w(s)` AND prefix-`k` sum < `psum s k`,
  (T2)   type-2 members: weight = `w(s)` AND prefix-`k` sum < `psum s k`,
  (T3)   type-3 members: weight = `w(s)` AND prefix-`k` sum ≤ `psum s k` AND
         `Init(s) ≺ Init(u)` lex.
G2a's prefix-`k` ≤ for type-3 members comes from `type3_psum_k_le_X` (the per-member
bound from an abstract level-0 `b`-tail prefix bound `X` with `X 1 ≤ s_k − 1`, through
`BCq_fiber_prefix_X`) + `lemma29_X1_le` (at the config `X 1 = (q−1)+w1 = s_k−1`, from
the `hleB` LePad-prefix conjunct that `lemma_2_9_config_data` now also exposes).
Remaining Step-1 conjuncts for the strengthened (H'_k) invariant (depth ≥ k, full
`T_k`-orders for ℓ > k) are flagged as G3 in PLAN.md.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
/-- A type-3 member's prefix-`k` sum is at most `s₁+…+s_k`, given the level-0 `b`-tail
prefix bound `X` (with `X 1 ≤ s_k − 1`):  prefix-k(u) = psum s j + 1 + psum(f)(k−j)
≤ psum s j + 1 + (k−j−1)q + X 1 ≤ psum s j + (k−1−j)q + s_k = psum s k. -/
lemma type3_psum_k_le_X (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (X : ℕ → ℕ)
    (hX0 : ∀ j' : R0.ιB, ∀ m : ℕ, psum (expTail (R0.cB j')) m ≤ X m)
    (hX1 : X 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) - 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inr i))) k ≤ psum s k := by
  classical
  intro D Bs Q i
  have hjk' : j ≤ k := by omega
  have hsplit : psum (Q.c (Sum.inr (Sum.inr i))) k =
      psum (Q.c (Sum.inr (Sum.inr i))) j +
        (∑ t ∈ Finset.range (k - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) := by
    change (∑ x ∈ Finset.range k, pad0 (Q.c (Sum.inr (Sum.inr i))) x) =
      (∑ x ∈ Finset.range j, pad0 (Q.c (Sum.inr (Sum.inr i))) x) +
        (∑ t ∈ Finset.range (k - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t))
    have hk : k = j + (k - j) := (Nat.add_sub_of_le hjk').symm
    rw [show Finset.range k = Finset.range (j + (k - j)) by exact congrArg Finset.range hk]
    rw [Finset.sum_range_add]
  have hpj : psum (Q.c (Sum.inr (Sum.inr i))) j = psum s j + 1 :=
    type3_psum_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  have htail : (∑ t ∈ Finset.range (k - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) =
      psum (expTail (D.cB i)) (k - j) := by
    change (∑ t ∈ Finset.range (k - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) =
      (∑ t ∈ Finset.range (k - j), pad0 (expTail (D.cB i)) t)
    apply Finset.sum_congr rfl
    intro t ht
    exact type3_tail_pad0 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i t
  have hfib := BCq_fiber_prefix_X F (k - j - 1) R0 hbhd X hX0 i (k - j)
  have hsub : (k - j) - (k - j - 1) = 1 := by omega
  have hfib' : psum (expTail (D.cB i)) (k - j) ≤ (k - j - 1) * Nat.card F + X 1 := by
    simpa [D, hsub] using hfib
  have hkm1 : k - 1 < r := by omega
  have hpkm1 : psum s (k - 1) = psum s j + (k - 1 - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hxj hxkm1
      have hxr : x < r := by omega
      have hm := hmid ⟨x, hxr⟩ hxj hxkm1
      rw [pad0_of_lt s hxr]
      exact hm
  have hsu := psum_last r s k hk1 hkr
  have hpk : psum s k = psum s j + (k - 1 - j) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) := by
    rw [hsu, hpkm1]
  have hsk1 : 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := (s ⟨k - 1, by omega⟩).pos
  calc
    psum (Q.c (Sum.inr (Sum.inr i))) k
        = psum (Q.c (Sum.inr (Sum.inr i))) j + psum (expTail (D.cB i)) (k - j) := by
          rw [hsplit, htail]
    _ = (psum s j + 1) + psum (expTail (D.cB i)) (k - j) := by rw [hpj]
    _ ≤ (psum s j + 1) + ((k - j - 1) * Nat.card F + X 1) := by
          exact Nat.add_le_add_left hfib' (psum s j + 1)
    _ ≤ (psum s j + 1) + ((k - j - 1) * Nat.card F + ((s ⟨k - 1, by omega⟩ : ℕ) - 1)) := by
          exact Nat.add_le_add_left (Nat.add_le_add_left hX1 ((k - j - 1) * Nat.card F)) (psum s j + 1)
    _ ≤ psum s k := by
          rw [hpk]
          have hn' : k - j - 1 = k - 1 - j := by omega
          rw [hn']
          omega


/-- At the configuration the Lemma-2.9 `b`-tail prefix bound has `X 1 = (q−1)+w1 = s_k−1`
(the `X 1 ≤ s_k − 1` hypothesis of `type3_psum_k_le_X`). -/
lemma lemma29_X1_le (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    (psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) 1) ≤
      (s ⟨k - 1, by omega⟩ : ℕ) - 1 := by
  classical
  let w1 : ℕ+ := w1Of F r s k hk1 hkr hbig
  let B : Fin (r - k) → ℕ+ := sTail r s k hkr
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hqsk : Nat.card F < (s ⟨k - 1, by omega⟩ : ℕ) := hbig
  have hx1 : (psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 B)) 1) =
      (qMinusExp F : ℕ) + (w1 : ℕ) := by
    dsimp [psumSeq, tupPadSum]
    rw [Finset.sum_singleton]
    rw [pad0_single_zero]
    have hb0 : 0 < (r - k) + 1 := by omega
    rw [pad0_of_lt (consVec w1 B) hb0]
    exact congrArg (fun t : ℕ+ => ((qMinusExp F : ℕ) + (t : ℕ))) (consVec_zero w1 B)
  calc
    (psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) 1)
        = (psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 B)) 1) := by
          rfl
    _ = (qMinusExp F : ℕ) + (w1 : ℕ) := hx1
    _ = (Nat.card F - 1) + ((s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F) := by
          rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
          rw [show (w1 : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F by rfl]
    _ ≤ (s ⟨k - 1, by omega⟩ : ℕ) - 1 := by omega


theorem prop212_step1 (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F (k - j - 1) (toData F R0)
      let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
          (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
      R0.aA u = 1 ∧
      R0.depA u = (r - k) + 1 ∧
      (∀ hd : R0.depA u = (r - k) + 1,
        (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
          bstarBase F r s k hk1 hkr hbig) ∧
      (ζ_A F s +
        (∑ i₀ : R0.ιA, (if i₀ = u then 0 else
          (Q.a (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) : RatFunc.CompletionAtInfty F) *
            ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))))) +
        (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inl i)) : RatFunc.CompletionAtInfty F) *
            ζ_A F (Q.c (Sum.inr (Sum.inl i)))) +
        (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inr i)) : RatFunc.CompletionAtInfty F) *
            ζ_A F (Q.c (Sum.inr (Sum.inr i)))) = 0) ∧
      (∀ i₀ : R0.ιA, i₀ ≠ u →
        weight (Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
            (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) = weight r s ∧
        psum (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) k < psum s k) ∧
      (∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight r s ∧
        psum (Q.c (Sum.inr (Sum.inl i))) k < psum s k) ∧
      (∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight r s ∧
        psum (Q.c (Sum.inr (Sum.inr i))) k ≤ psum s k ∧
        InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))) := by
  classical
  rcases lemma_2_9_config_data F r s k hk1 hkr hbig with
    ⟨R0, u, hdep0, ha, hc0, hbhd, hwtA, hhead, hXw, hbndB⟩
  refine ⟨R0, u, hbhd, ?ha, ?hdep0, ?hc0, ?rel, ?t1, ?t2, ?t3⟩
  · exact ha
  · exact hdep0
  · exact hc0
  · simpa using (zeta_214_reindexed F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 u ha hdep0 hc0 hbhd)
  · intro i₀ hi
    constructor
    · simpa using (type1_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ (hwtA i₀ hi))
    · simpa using (type1_psum_lt_k F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ (hhead i₀ hi))
  · intro i
    constructor
    · simpa using (type2_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw)
    · simpa using (type2_psum_lt_k F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i)
  · intro i
    constructor
    · simpa using (type3_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw)
    · constructor
      · have hX1 : (psumSeq (tupPadSum (single (qMinusExp F))
            (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) 1) ≤
            (s ⟨k - 1, by omega⟩ : ℕ) - 1 := by
          exact lemma29_X1_le F r s k hk1 hkr hbig
        exact (type3_psum_k_le_X F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd
          (fun m => psumSeq (tupPadSum (single (qMinusExp F))
            (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) hbndB hX1 i)
      · simpa using (type3_Init_gt F r s k j hk1 hkr hj1 hjk hbig hsj hsleq R0 hbhd i)

end ZagierHoffmanPositiveChar
