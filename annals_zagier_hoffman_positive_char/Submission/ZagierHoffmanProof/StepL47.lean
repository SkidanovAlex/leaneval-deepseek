import Submission.ZagierHoffmanProof.StepL46
import Submission.ZagierHoffmanProof.StepL33

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L47: CASE-1 type-3 `prefix-ℓ ≤` for ℓ ≥ k (option-(i) per-member order)

★ `type3_psum_ge_k_le`: a type-3 member `u` of the CASE-1 chain satisfies
`psum u ℓ ≤ psum s ℓ` for every `ℓ ∈ [k, depth(s)]` — the paper's Prop-2.12
type-3 claim (the strengthened `(H'_k)` recursion's output order; ℓ = k is the
existing `type3_psum_k_le_X`, ℓ > k needs the level-0 X-telescope of StepL46).
Assembly: prefix-ℓ(u) = psum s j + 1 + psum(τ)(ℓ−j) (`type3_psum_j` +
`type3_tail_pad0`), ≤ psum s j + 1 + (k−j−1)·q + X(ℓ−k+1)
(`BCq_fiber_prefix_X` with the `hbndB` level-0 prefix bound), =
psum s j + 1 + (k−j−1)·q + ((s_k−1) + psum s ℓ − psum s k)
(`lemma29_X_telescope`), = psum s k + (psum s ℓ − psum s k) (hmid block), ≤ psum s ℓ.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ A type-3 member's `ℓ`-prefix is at most `s`'s `ℓ`-prefix for every `ℓ ≥ k`
(within the depth of `s`). -/
lemma type3_psum_ge_k_le (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (ℓ : ℕ), k ≤ ℓ → ℓ ≤ r →
      psum (Q.c (Sum.inr (Sum.inr i))) ℓ ≤ psum s ℓ := by
  classical
  intro D Bs Q i ℓ hkℓ hℓr
  have hjl : j ≤ ℓ := by omega
  have hsplit : psum (Q.c (Sum.inr (Sum.inr i))) ℓ =
      psum (Q.c (Sum.inr (Sum.inr i))) j +
        (∑ t ∈ Finset.range (ℓ - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) := by
    change (∑ x ∈ Finset.range ℓ, pad0 (Q.c (Sum.inr (Sum.inr i))) x) =
      (∑ x ∈ Finset.range j, pad0 (Q.c (Sum.inr (Sum.inr i))) x) +
        (∑ t ∈ Finset.range (ℓ - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t))
    have hℓ : ℓ = j + (ℓ - j) := (Nat.add_sub_of_le hjl).symm
    rw [show Finset.range ℓ = Finset.range (j + (ℓ - j)) by exact congrArg Finset.range hℓ]
    rw [Finset.sum_range_add]
  have hpj : psum (Q.c (Sum.inr (Sum.inr i))) j = psum s j + 1 :=
    type3_psum_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  have htail : (∑ t ∈ Finset.range (ℓ - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) =
      psum (expTail (D.cB i)) (ℓ - j) := by
    change (∑ t ∈ Finset.range (ℓ - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) =
      (∑ t ∈ Finset.range (ℓ - j), pad0 (expTail (D.cB i)) t)
    apply Finset.sum_congr rfl
    intro t ht
    exact type3_tail_pad0 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i t
  have hfib := BCq_fiber_prefix_X F (k - j - 1) R0 hbhd
    (fun m : ℕ => psumSeq (tupPadSum (single (qMinusExp F))
      (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m)
    hbndB i (ℓ - j)
  have hsub : (ℓ - j) - (k - j - 1) = ℓ - k + 1 := by omega
  have hfib' : psum (expTail (D.cB i)) (ℓ - j) ≤
      (k - j - 1) * Nat.card F + psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k + 1) := by
    simpa [D, hsub] using hfib
  have htel := lemma29_X_telescope F r s k hk1 hkr hbig (ℓ - k + 1) (by omega)
  -- htel : X(ℓ−k+1) = (s_k − 1) + (psum s (k + (ℓ−k+1) − 1) − psum s k)
  have hk1' : k + (ℓ - k + 1) - 1 = ℓ := by omega
  have htel' : psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k + 1) =
      ((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s ℓ - psum s k) := by
    rw [htel, hk1']
  -- block identity psum s k = psum s j + (k−1−j)·q + s_k
  have hpkm1 : psum s (k - 1) = psum s j + (k - 1 - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hxj hxkm1
      have hxr : x < r := by omega
      have hm := hmid ⟨x, hxr⟩ hxj hxkm1
      rw [pad0_of_lt s hxr]
      exact hm
  have hkm1 : k - 1 < r := by omega
  have hsu2 := psum_succ s (k - 1)
  have hkk : (k - 1) + 1 = k := by omega
  have hpk : psum s k = psum s j + ((k - 1) - j) * Nat.card F + (s ⟨k - 1, hkm1⟩ : ℕ) := by
    rw [hkk] at hsu2
    rw [hsu2]
    rw [hpkm1]
    rw [pad0_of_lt s hkm1]
  have hkleq : psum s k ≤ psum s ℓ := psum_mono s hkℓ
  have hpk' : psum s k = psum s j + (k - j - 1) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) := by
    rw [hpk]
    have hn' : (k - 1 - j) = k - j - 1 := by omega
    rw [hn']
  have hskpos : 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := (s ⟨k - 1, by omega⟩).pos
  have hmain : (psum s j + 1) + ((k - j - 1) * Nat.card F +
        (((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s ℓ - psum s k))) ≤ psum s ℓ := by
    calc
      (psum s j + 1) + ((k - j - 1) * Nat.card F +
            (((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s ℓ - psum s k)))
          ≤ psum s k + (psum s ℓ - psum s k) := by
            rw [hpk']
            omega
      _ ≤ psum s ℓ := by omega
  calc
    psum (Q.c (Sum.inr (Sum.inr i))) ℓ
        = psum (Q.c (Sum.inr (Sum.inr i))) j + psum (expTail (D.cB i)) (ℓ - j) := by
          rw [hsplit, htail]
    _ = (psum s j + 1) + psum (expTail (D.cB i)) (ℓ - j) := by rw [hpj]
    _ ≤ (psum s j + 1) + ((k - j - 1) * Nat.card F +
          psumSeq (tupPadSum (single (qMinusExp F))
            (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k + 1)) := by
          exact Nat.add_le_add_left hfib' (psum s j + 1)
    _ = (psum s j + 1) + ((k - j - 1) * Nat.card F +
          (((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s ℓ - psum s k))) := by
          rw [htel']
    _ ≤ psum s ℓ := hmain


/-- A type-2 member's `ℓ`-prefix is strictly smaller than `s`'s `ℓ`-prefix for every
`ℓ ∈ (k, depth(s)]` (the paper's Prop-2.12 type-2 claim for `ℓ > k`; `ℓ = k` is the
existing `type2_psum_lt_k`).  The `X`-telescope at `m = ℓ−k` gives the bound
`psum s (ℓ−1)`, and the `ℓ`-th entry of `s` is `≥ 1` so that is `< psum s ℓ`. -/
lemma type2_psum_ge_k_lt (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (ℓ : ℕ), k < ℓ → ℓ ≤ r →
      psum (Q.c (Sum.inr (Sum.inl i))) ℓ < psum s ℓ := by
  classical
  intro D Bs Q i ℓ hkℓ hℓr
  have hjl : j ≤ ℓ := by omega
  have hkj1 : k + 1 ≤ ℓ := by omega
  have hdec := type2_psum_after F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i (ℓ - j - 1)
  -- hdec : psum (member) (j + 1 + (ℓ−j−1)) = psum s j + 1 + psum τ (ℓ−j−1)
  have hkk' : j + 1 + (ℓ - j - 1) = ℓ := by omega
  have hdec' : psum (Q.c (Sum.inr (Sum.inl i))) ℓ = psum s j + 1 + psum (expTail (D.cB i)) (ℓ - j - 1) := by
    rw [← hdec]
    exact congrArg (psum (Q.c (Sum.inr (Sum.inl i)))) (by omega : ℓ = j + 1 + (ℓ - j - 1))
  have hfib := BCq_fiber_prefix_X F (k - j - 1) R0 hbhd
    (fun m : ℕ => psumSeq (tupPadSum (single (qMinusExp F))
      (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m)
    hbndB i (ℓ - j - 1)
  have hsub : (ℓ - j - 1) - (k - j - 1) = ℓ - k := by omega
  have hfib' : psum (expTail (D.cB i)) (ℓ - j - 1) ≤
      (k - j - 1) * Nat.card F + psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k) := by
    simpa [D, hsub] using hfib
  have htel := lemma29_X_telescope F r s k hk1 hkr hbig (ℓ - k) (by omega)
  have hk1' : k + (ℓ - k) - 1 = ℓ - 1 := by omega
  have htel' : psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k) =
      ((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s k) := by
    rw [htel, hk1']
  have hpk' : psum s k = psum s j + (k - j - 1) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) := by
    have hpkm1 : psum s (k - 1) = psum s j + (k - 1 - j) * Nat.card F := by
      apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
      · omega
      · intro x hxj hxkm1
        have hxr : x < r := by omega
        have hm := hmid ⟨x, hxr⟩ hxj hxkm1
        rw [pad0_of_lt s hxr]
        exact hm
    have hkm1 : k - 1 < r := by omega
    have hsu2 := psum_succ s (k - 1)
    have hkk2 : (k - 1) + 1 = k := by omega
    have hpk : psum s k = psum s j + ((k - 1) - j) * Nat.card F + (s ⟨k - 1, hkm1⟩ : ℕ) := by
      rw [hkk2] at hsu2
      rw [hsu2]
      rw [hpkm1]
      rw [pad0_of_lt s hkm1]
    rw [hpk]
    have hn' : (k - 1 - j) = k - j - 1 := by omega
    rw [hn']
  have hskpos : 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := (s ⟨k - 1, by omega⟩).pos
  have hmono1 : psum s k ≤ psum s (ℓ - 1) := by
    apply psum_mono s
    omega
  have hmain : psum s j + 1 + ((k - j - 1) * Nat.card F +
        (((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s k)))
      < psum s (ℓ - 1) + pad0 s (ℓ - 1) := by
    -- = psum s (ℓ−1) + pad0 s (ℓ−1) is psum s ℓ (psum_succ) — prove < psum s (ℓ−1) first
    have hle : psum s j + 1 + ((k - j - 1) * Nat.card F +
        (((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s k)))
      ≤ psum s (ℓ - 1) := by
      calc
        psum s j + 1 + ((k - j - 1) * Nat.card F +
            (((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s k)))
            ≤ psum s k + (psum s (ℓ - 1) - psum s k) := by
              rw [hpk']
              omega
        _ ≤ psum s (ℓ - 1) := by omega
    exact lt_of_le_of_lt hle (by
      -- pad0 s (ℓ−1) = s⟨ℓ−1⟩ ≥ 1 when ℓ−1 < r
      have hℓ1r : ℓ - 1 < r := by omega
      have hp : pad0 s (ℓ - 1) = (s ⟨ℓ - 1, hℓ1r⟩ : ℕ) := pad0_of_lt s hℓ1r
      have hpos : 0 < (s ⟨ℓ - 1, hℓ1r⟩ : ℕ) := (s ⟨ℓ - 1, hℓ1r⟩).pos
      rw [hp]
      omega)
  have hsu := psum_succ s (ℓ - 1)
  have hℓs : (ℓ - 1) + 1 = ℓ := by omega
  have hpsumℓ : psum s ℓ = psum s (ℓ - 1) + pad0 s (ℓ - 1) := by
    rw [hℓs] at hsu
    exact hsu
  calc
    psum (Q.c (Sum.inr (Sum.inl i))) ℓ = psum s j + 1 + psum (expTail (D.cB i)) (ℓ - j - 1) := hdec'
    _ ≤ psum s j + 1 + ((k - j - 1) * Nat.card F +
          psumSeq (tupPadSum (single (qMinusExp F))
            (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - k)) := by
          exact Nat.add_le_add_left hfib' (psum s j + 1)
    _ = psum s j + 1 + ((k - j - 1) * Nat.card F +
          (((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s k))) := by
          rw [htel']
    _ < psum s (ℓ - 1) + pad0 s (ℓ - 1) := hmain
    _ = psum s ℓ := by rw [hpsumℓ]

end ZagierHoffmanPositiveChar
