import Submission.ZagierHoffmanProof.StepL47
import Submission.ZagierHoffmanProof.StepL31

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L48: CASE-1 type-1 `prefix-ℓ ≤` for ℓ ≥ k (last per-member ℓ-order stone)

The type-1 (a-side) members of the CASE-1 chain have tuples
`s₁..s_j, q^{(k−1−j)}, cA i₀ …` (front from the prefix prepends and B* head, the
`k−1−j` `q`'s from the `BC_q`-iterate a-heads, then the level-0 a-tuple `R0.cA i₀`).
★ `type1_psum_decompose_ge`: `psum (member) ℓ = psum s (k−1) + psum (cA i₀) (ℓ−k+1)`
for `ℓ ≥ k` (range-split at `j`, `type1_pad0_shift`, and the iterate-a psum split
into the `k−j−1` leading `q`'s plus the base tuple).  ★ `type1_psum_ge_k_le`:
bounded by the level-0 `a`-LePad prefix (hleA: `psum (cA i₀) m ≤` the
`(qExp) + (w1,B)` reference), whose `q`-telescope companion
(`lemma29_qExp_telescope`) makes it exactly `≤ psum s ℓ` — the paper's Prop-2.12
type-1 claim.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The `(qExp, w1, sTail)` reference-prefix telescopes: `q`-version companion of
`lemma29_X_telescope` (the `qExp` head instead of `qMinusExp`), giving
`psumSeq … m = s_k + (psum s (k+m−1) − psum s k)` for `m ≥ 1`. -/
lemma lemma29_qExp_telescope (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) (m : ℕ) (hm : 1 ≤ m) :
    (psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) =
      ((s ⟨k - 1, by omega⟩ : ℕ)) + (psum s (k + m - 1) - psum s k) := by
  classical
  let w1 : ℕ+ := w1Of F r s k hk1 hkr hbig
  let B : Fin (r - k) → ℕ+ := sTail r s k hkr
  have hsplit : psumSeq (tupPadSum (single (qExp F)) (consVec w1 B)) m =
      psum (single (qExp F)) m + psum (consVec w1 B) m := by
    exact psumSeq_tupPadSum_split (single (qExp F)) (consVec w1 B) m
  have hq := psum_single_of_pos (qExp F) (by omega : 0 < m)
  have hc : psum (consVec w1 B) m = (w1 : ℕ) + psum B (m - 1) := by
    have hmm : m = (m - 1) + 1 := by omega
    rw [hmm]
    simpa [B] using (psum_consVec w1 B (m - 1))
  have hB : psum B (m - 1) = psum s (k + m - 1) - psum s k := by
    have htail := psum_sTail_add s hkr (m - 1)
    have hcong : k + (m - 1) = k + m - 1 := by omega
    rw [hcong] at htail
    have htail' : psum s (k + m - 1) = psum s k + psum B (m - 1) := by
      simpa [B] using htail
    omega
  calc
    psumSeq (tupPadSum (single (qExp F)) (consVec w1 B)) m
        = psum (single (qExp F)) m + psum (consVec w1 B) m := hsplit
    _ = (qExp F : ℕ) + psum (consVec w1 B) m := by rw [hq]
    _ = (qExp F : ℕ) + ((w1 : ℕ) + psum B (m - 1)) := by rw [hc]
    _ = ((qExp F : ℕ) + (w1 : ℕ)) + (psum s (k + m - 1) - psum s k) := by
          rw [hB]
          omega
    _ = (s ⟨k - 1, by omega⟩ : ℕ) + (psum s (k + m - 1) - psum s k) := by
          exact congrArg (fun a : ℕ => a + (psum s (k + m - 1) - psum s k))
            (w1Of_add F r s k hk1 hkr hbig)

/-- Padded values of the `BC_q`-iterate `a`-tuple beyond its `n` leading `q`'s are the
base `a`-tuple's padded values. -/
lemma iterateA_pad_beyond (n : ℕ) (R0 : BinaryRel F) (i₀ : R0.ιA) (t : ℕ) :
    pad0 ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) (n + t) =
      pad0 (R0.cA i₀) t := by
  classical
  let A : Fin (R0.depA i₀ + n) → ℕ+ := fun x =>
    (RelData.BCqIter F n (toData F R0)).cA (RelData.iterIdx F n (toData F R0) i₀)
      (Fin.cast (RelData.BCqIter_depA_at F n (toData F R0) i₀).symm x)
  have hdep : (RelData.BCqIter F n (toData F R0)).depA
      (RelData.iterIdx F n (toData F R0) i₀) = R0.depA i₀ + n :=
    RelData.BCqIter_depA_at F n (toData F R0) i₀
  by_cases ht : t < R0.depA i₀
  · have hm : n + t < R0.depA i₀ + n := by omega
    have hb : n + t < (RelData.BCqIter F n (toData F R0)).depA
        (RelData.iterIdx F n (toData F R0) i₀) := by
      rw [hdep]
      exact hm
    rw [pad0_of_lt ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) hb]
    rw [pad0_of_lt (R0.cA i₀) ht]
    -- values agree via BCqIter_cA_value at index n+t (≥ n → base at (n+t)−n = t)
    have hidx : Fin.cast (RelData.BCqIter_depA_at F n (toData F R0) i₀).symm
        ⟨n + t, hm⟩ = ⟨n + t, hb⟩ := by
      apply Fin.ext
      simp
    have hv := RelData.BCqIter_cA_value F n (toData F R0) i₀ ⟨n + t, hm⟩
    rw [hidx] at hv
    have hge : ¬ (n + t : ℕ) < n := by omega
    have htn : (n + t) - n = t := by omega
    have hv' : ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) ⟨n + t, hb⟩ =
        (R0.cA i₀) ⟨t, ht⟩ := by
      rw [dif_neg hge] at hv
      have hidx2 : (⟨(n + t) - n, by omega⟩ : Fin (R0.depA i₀)) = ⟨t, ht⟩ := by
        apply Fin.ext
        simp [htn]
      calc
        ((RelData.BCqIter F n (toData F R0)).cA
            (RelData.iterIdx F n (toData F R0) i₀)) ⟨n + t, hb⟩
            = (R0.cA i₀) ⟨(n + t) - n, by omega⟩ := hv
        _ = (R0.cA i₀) ⟨t, ht⟩ := by rw [hidx2]
    apply congrArg (fun v : ℕ+ => (v : ℕ)) hv'
  · have hge : R0.depA i₀ ≤ t := le_of_not_gt ht
    have hgeA : R0.depA i₀ + n ≤ n + t := by omega
    have hb' : (RelData.BCqIter F n (toData F R0)).depA
        (RelData.iterIdx F n (toData F R0) i₀) ≤ n + t := by
      rw [hdep]
      exact hgeA
    rw [pad0_of_ge ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) hb']
    rw [pad0_of_ge (R0.cA i₀) hge]

/-- The `BC_q`-iterate `a`-tuple psum: `n` leading `q`'s plus the base `a`-tuple at
`m − n` (for `m ≥ n`). -/
lemma iterateA_psum_split (n : ℕ) (R0 : BinaryRel F) (i₀ : R0.ιA) (m : ℕ) (hmn : n ≤ m) :
    psum ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) m =
      n * Nat.card F + psum (R0.cA i₀) (m - n) := by
  classical
  have hsplit : psum ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) (n + (m - n)) =
      psum ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) n +
        (∑ t ∈ Finset.range (m - n), pad0 ((RelData.BCqIter F n (toData F R0)).cA
          (RelData.iterIdx F n (toData F R0) i₀)) (n + t)) := by
    change (∑ x ∈ Finset.range (n + (m - n)), pad0 ((RelData.BCqIter F n (toData F R0)).cA
          (RelData.iterIdx F n (toData F R0) i₀)) x) =
      (∑ x ∈ Finset.range n, pad0 ((RelData.BCqIter F n (toData F R0)).cA
          (RelData.iterIdx F n (toData F R0) i₀)) x) +
        (∑ t ∈ Finset.range (m - n), pad0 ((RelData.BCqIter F n (toData F R0)).cA
          (RelData.iterIdx F n (toData F R0) i₀)) (n + t))
    rw [Finset.sum_range_add]
  have hfront : psum ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) n = n * Nat.card F := by
    calc
      psum ((RelData.BCqIter F n (toData F R0)).cA
          (RelData.iterIdx F n (toData F R0) i₀)) n
          = (∑ x ∈ Finset.range n, Nat.card F) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hx' : x < n := Finset.mem_range.mp hx
            exact BCqIter_cA_pad0_front F n R0 i₀ x hx'
      _ = n * Nat.card F := by
            rw [Finset.sum_const]
            simp
  have htail : (∑ t ∈ Finset.range (m - n), pad0 ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) (n + t)) =
      psum (R0.cA i₀) (m - n) := by
    change (∑ t ∈ Finset.range (m - n), pad0 ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) (n + t)) =
      (∑ t ∈ Finset.range (m - n), pad0 (R0.cA i₀) t)
    apply Finset.sum_congr rfl
    intro t ht
    exact iterateA_pad_beyond F n R0 i₀ t
  have hmm : n + (m - n) = m := by omega
  calc
    psum ((RelData.BCqIter F n (toData F R0)).cA
        (RelData.iterIdx F n (toData F R0) i₀)) m
        = psum ((RelData.BCqIter F n (toData F R0)).cA
            (RelData.iterIdx F n (toData F R0) i₀)) (n + (m - n)) := by
          exact congrArg (psum ((RelData.BCqIter F n (toData F R0)).cA
            (RelData.iterIdx F n (toData F R0) i₀))) hmm.symm
    _ = psum ((RelData.BCqIter F n (toData F R0)).cA
          (RelData.iterIdx F n (toData F R0) i₀)) n +
        (∑ t ∈ Finset.range (m - n), pad0 ((RelData.BCqIter F n (toData F R0)).cA
          (RelData.iterIdx F n (toData F R0) i₀)) (n + t)) := hsplit
    _ = n * Nat.card F + psum (R0.cA i₀) (m - n) := by rw [hfront, htail]


/-- Type-1 member `ℓ`-prefix decomposition: the front `s₁..s_{k−1}` (with the
`k−1−j` `q`'s) plus the level-0 `a`-tuple over `ℓ−k+1` positions. -/
lemma type1_psum_decompose_ge (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, ∀ (ℓ : ℕ), k ≤ ℓ →
      psum (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) ℓ =
        psum s (k - 1) + psum (R0.cA i₀) (ℓ - k + 1) := by
  classical
  intro D Bs Q i₀ ℓ hkℓ
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  have hjl : j ≤ ℓ := by omega
  have hsplit : psum (Q.c (Sum.inl i)) ℓ =
      psum (Q.c (Sum.inl i)) j +
        (∑ t ∈ Finset.range (ℓ - j), pad0 (Q.c (Sum.inl i)) (j + t)) := by
    change (∑ x ∈ Finset.range ℓ, pad0 (Q.c (Sum.inl i)) x) =
      (∑ x ∈ Finset.range j, pad0 (Q.c (Sum.inl i)) x) +
        (∑ t ∈ Finset.range (ℓ - j), pad0 (Q.c (Sum.inl i)) (j + t))
    have hℓ : ℓ = j + (ℓ - j) := (Nat.add_sub_of_le hjl).symm
    rw [show Finset.range ℓ = Finset.range (j + (ℓ - j)) by exact congrArg Finset.range hℓ]
    rw [Finset.sum_range_add]
  have hpj : psum (Q.c (Sum.inl i)) j = psum s j :=
    a_side_psum_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  have htail : (∑ t ∈ Finset.range (ℓ - j), pad0 (Q.c (Sum.inl i)) (j + t)) =
      psum (D.cA i) (ℓ - j) := by
    change (∑ t ∈ Finset.range (ℓ - j), pad0 (Q.c (Sum.inl i)) (j + t)) =
      (∑ t ∈ Finset.range (ℓ - j), pad0 (D.cA i) t)
    apply Finset.sum_congr rfl
    intro t ht
    have hsh := type1_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i (j + t) (by omega)
    have hsub : (j + t) - j = t := by omega
    rw [hsh]
    rw [hsub]
  have hmn : k - j - 1 ≤ ℓ - j := by omega
  have hiter := iterateA_psum_split F (k - j - 1) R0 i₀ (ℓ - j) hmn
  have hsub2 : (ℓ - j) - (k - j - 1) = ℓ - k + 1 := by omega
  have hiter' : psum (D.cA i) (ℓ - j) =
      (k - j - 1) * Nat.card F + psum (R0.cA i₀) (ℓ - k + 1) := by
    simpa [D, i, hsub2] using hiter
  have hpkm1 : psum s (k - 1) = psum s j + (k - 1 - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hxj hxkm1
      have hxr : x < r := by omega
      have hm := hmid ⟨x, hxr⟩ hxj hxkm1
      rw [pad0_of_lt s hxr]
      exact hm
  have hn' : k - 1 - j = k - j - 1 := by omega
  calc
    psum (Q.c (Sum.inl i)) ℓ
        = psum (Q.c (Sum.inl i)) j + psum (D.cA i) (ℓ - j) := by
          rw [hsplit, htail]
    _ = psum s j + psum (D.cA i) (ℓ - j) := by rw [hpj]
    _ = psum s j + ((k - j - 1) * Nat.card F + psum (R0.cA i₀) (ℓ - k + 1)) := by
          rw [hiter']
    _ = psum s j + ((k - 1 - j) * Nat.card F + psum (R0.cA i₀) (ℓ - k + 1)) := by
          rw [hn']
    _ = (psum s j + (k - 1 - j) * Nat.card F) + psum (R0.cA i₀) (ℓ - k + 1) := by omega
    _ = psum s (k - 1) + psum (R0.cA i₀) (ℓ - k + 1) := by rw [hpkm1]

/-- ★ A type-1 member's `ℓ`-prefix is at most `s`'s `ℓ`-prefix for every `ℓ ≥ k`
(within the depth of `s`), via the level-0 `a`-LePad prefix bound (the paper's
Prop-2.12 type-1 claim). -/
lemma type1_psum_ge_k_le (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hpref : ∀ i₀ : R0.ιA, ∀ m : ℕ,
      psum (R0.cA i₀) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, ∀ (ℓ : ℕ), k ≤ ℓ → ℓ ≤ r →
      psum (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) ℓ ≤ psum s ℓ := by
  classical
  intro D Bs Q i₀ ℓ hkℓ hℓr
  have hdec := type1_psum_decompose_ge F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ ℓ hkℓ
  have hpref' : psum (R0.cA i₀) (ℓ - k + 1) ≤ psumSeq (tupPadSum (single (qExp F))
      (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k + 1) :=
    hpref i₀ (ℓ - k + 1)
  have htel := lemma29_qExp_telescope F r s k hk1 hkr hbig (ℓ - k + 1) (by omega)
  have hk1' : k + (ℓ - k + 1) - 1 = ℓ := by omega
  have htel' : psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k + 1) =
      (s ⟨k - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k) := by
    rw [htel, hk1']
  have hkm1 : k - 1 < r := by omega
  have hsu := psum_succ s (k - 1)
  have hkk : (k - 1) + 1 = k := by omega
  have hpks : psum s k = psum s (k - 1) + (s ⟨k - 1, hkm1⟩ : ℕ) := by
    rw [hkk] at hsu
    rw [hsu]
    rw [pad0_of_lt s hkm1]
  have hkleq : psum s k ≤ psum s ℓ := psum_mono s hkℓ
  calc
    psum (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) ℓ
        = psum s (k - 1) + psum (R0.cA i₀) (ℓ - k + 1) := hdec
    _ ≤ psum s (k - 1) + psumSeq (tupPadSum (single (qExp F))
          (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k + 1) := by
          exact Nat.add_le_add_left hpref' (psum s (k - 1))
    _ = psum s (k - 1) + ((s ⟨k - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k)) := by
          rw [htel']
    _ ≤ psum s ℓ := by
          rw [hpks]
          omega
end ZagierHoffmanPositiveChar
