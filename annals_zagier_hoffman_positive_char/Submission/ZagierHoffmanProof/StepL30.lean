import Submission.ZagierHoffmanProof.StepL29

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L30: type-2 prefix-sum bounds of the (2.14) chain (the ℓ = k strict drop)

The type-2 members `Q.c (inr (inl i))` of the (2.14) chain have tuple
`s_1,…,s_j,1,τ` where `τ = expTail (D.cB i)` is the tail of the level-`(k−j−1)`
`BC_q`-b-tuple.  This module records the structural facts of that shape:
`type2_tail_pad0` (padded value at position `j+1+t` is the `t`-th tail entry),
`type2_psum_after` (prefix sum at `j+1+m` splits as `psum s j + 1 +` the `m`-prefix
of `τ`), the generic q-block prefix lemma `psum_const_block`, and
★ `type2_psum_lt_k`: `psum (Q.c (inr (inl i))) k < psum s k` — the paper's type-2
`t'₁+…+t'ₖ < s₁+…+sₖ` estimate (`BCq_fiber_prefix_qN` bounds the `τ`-prefix by
`(k−j−1)·q`; the front `q`-block of `s` and `s_k > q` give the strict drop).
These are the seed inequalities of Prop 3.2's inner induction on `s₁+…+sₖ`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
/-- Padded values of a type-2 member beyond the `1` at position `j`: at full position
`j+1+t` the value is the `t`-th padded entry of the b-fiber tail `expTail (D.cB i)`. -/
lemma type2_tail_pad0 (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (t : ℕ),
      pad0 (Q.c (Sum.inr (Sum.inl i))) (j + 1 + t) = pad0 (expTail (D.cB i)) t := by
  classical
  intro D Bs Q i t
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
      Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix r s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
  have hBsdep : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
    dsimp [Bs, ofBstarOver]
  by_cases hm : j + 1 + t < Q.dep (Sum.inr (Sum.inl i))
  · have hge : (sPrefix r s j (by omega) (by omega)).length ≤ j + 1 + t := by omega
    have ht1b : t + 1 < D.depB i := by
      have hm0 : j + 1 + t < Q.dep (Sum.inr (Sum.inl i)) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have b' : (j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inl i)) := by
      rw [hBsdep]
      have hm0 : j + 1 + t < Q.dep (Sum.inr (Sum.inl i)) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have hval : ((Q.c (Sum.inr (Sum.inl i))) ⟨j + 1 + t, hm⟩ : ℕ) =
        ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
      have h1 : ((Q.c (Sum.inr (Sum.inl i))) ⟨j + 1 + t, hm⟩ : ℕ) =
          ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
        have hv := prependList_c_base_value F Bs (sPrefix r s j (by omega) (by omega))
          (Sum.inr (Sum.inl i)) (j + 1 + t) hm hge
        apply congrArg (fun v : ℕ+ => (v : ℕ))
        calc
          (Q.c (Sum.inr (Sum.inl i))) ⟨j + 1 + t, hm⟩
              = (Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length,
                  (by
                    have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
                    rw [hd] at hm
                    omega)⟩ := hv
          _ = (Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ := by
                congr 1
      have hcBs : Bs.c (Sum.inr (Sum.inl i)) = consVec (s ⟨j - 1, by omega⟩) (D.cB i) := by
        dsimp [Bs, ofBstarOver, D]
      have h2 : ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
          ((consVec (s ⟨j - 1, by omega⟩) (D.cB i)) ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
        apply congrArg (fun v : ℕ+ => (v : ℕ))
        exact congrFun hcBs ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩
      have hbp0 : (j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length = t + 2 := by
        rw [hlen]
        omega
      have h3 : ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
            ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
          ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
        have hcv := consVec_nat_value (s ⟨j - 1, by omega⟩) (D.cB i)
          ((j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length) b'
        have hnz : (j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length ≠ 0 := by omega
        calc
          ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
                ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ)
              = ((D.cB i) ⟨((j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length) - 1,
                  (by omega : ((j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length) - 1 < D.depB i)⟩ : ℕ) := by
                apply congrArg (fun v : ℕ+ => (v : ℕ))
                rw [hcv]
                simp [hnz]
          _ = ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
                rw [show (⟨((j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length) - 1,
                    (by omega : ((j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length) - 1 < D.depB i)⟩ :
                        Fin (D.depB i)) = ⟨t + 1, ht1b⟩ from (by
                  apply Fin.ext
                  simp
                  omega)]
      calc
        ((Q.c (Sum.inr (Sum.inl i))) ⟨j + 1 + t, hm⟩ : ℕ)
            = ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
        _ = ((consVec (s ⟨j - 1, by omega⟩) (D.cB i)) ⟨(j + 1 + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
        _ = ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := h3
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hm]
    have hdep : t < (D.depB i) - 1 := by omega
    rw [pad0_of_lt (expTail (D.cB i)) hdep]
    exact hval
  · have hgeQ : Q.dep (Sum.inr (Sum.inl i)) ≤ j + 1 + t := le_of_not_gt hm
    have hp1 : pad0 (Q.c (Sum.inr (Sum.inl i))) (j + 1 + t) = 0 := pad0_of_ge (Q.c (Sum.inr (Sum.inl i))) hgeQ
    rw [hp1]
    have hdep : (D.depB i) - 1 ≤ t := by
      have hge0 : Q.dep (Sum.inr (Sum.inl i)) ≤ j + 1 + t := hgeQ
      rw [hQdep, hBsdep, hlen] at hge0
      omega
    have hp2 : pad0 (expTail (D.cB i)) t = 0 := pad0_of_ge (expTail (D.cB i)) hdep
    rw [hp2]

/-- Type-2 prefix sum after the `(s_1..s_j, 1)` front: the `(j+1+m)`-prefix is
`psum s j + 1 + (m-prefix of the b-fiber tail)`. -/
lemma type2_psum_after (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (m : ℕ),
      psum (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m) =
        psum s j + 1 + psum (expTail (D.cB i)) m := by
  classical
  intro D Bs Q i m
  induction m with
  | zero =>
      have hpj : psum (Q.c (Sum.inr (Sum.inl i))) j = psum s j :=
        type2_psum_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
      have hsu := psum_succ (Q.c (Sum.inr (Sum.inl i))) j
      have h1 : psum (Q.c (Sum.inr (Sum.inl i))) (j + 1) =
          psum s j + pad0 (Q.c (Sum.inr (Sum.inl i))) j := by
        rw [hsu, hpj]
      have hdep : j < Q.dep (Sum.inr (Sum.inl i)) := by
        have hb2 : 1 < D.depB i := D.hB2 i
        have hQd : Q.dep (Sum.inr (Sum.inl i)) = (D.depB i + 1) + (j - 1) := by
          have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
            sPrefix_length r s j (by omega) (by omega)
          have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
              Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix r s j (by omega) (by omega)).length :=
            FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
          have hBsdep : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
            dsimp [Bs, ofBstarOver]
          rw [hQdep, hBsdep, hlen]
        rw [hQd]
        omega
      have hp1 : (pad0 (Q.c (Sum.inr (Sum.inl i))) j : ℕ) = 1 := by
        have hv := type2_one_at_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hdep
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hdep]
        exact hv
      calc
        psum (Q.c (Sum.inr (Sum.inl i))) (j + 1)
            = psum s j + pad0 (Q.c (Sum.inr (Sum.inl i))) j := h1
        _ = psum s j + 1 := by rw [hp1]
        _ = psum s j + 1 + 0 := by omega
        _ = psum s j + 1 + psum (expTail (D.cB i)) 0 := by simp [psum_zero]
  | succ m ih =>
      have hsu := psum_succ (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m)
      have ht := type2_tail_pad0 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i m
      have hsut := psum_succ (expTail (D.cB i)) m
      calc
        psum (Q.c (Sum.inr (Sum.inl i))) (j + 1 + (m + 1))
            = psum (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m) + pad0 (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m) := by
              have hjj : (j + 1 + m) + 1 = j + 1 + (m + 1) := by omega
              rw [← hjj]
              exact hsu
        _ = (psum s j + 1 + psum (expTail (D.cB i)) m) + pad0 (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m) := by
              rw [ih]
        _ = psum s j + 1 + (psum (expTail (D.cB i)) m + pad0 (expTail (D.cB i)) m) := by
              rw [ht]
              dsimp [D]
              omega
        _ = psum s j + 1 + psum (expTail (D.cB i)) (m + 1) := by
              rw [← hsut]

/-- If the padded entries `s_j..s_{m-1}` of a tuple are all the constant `q`, then the
`m`-prefix sum splits at `j` plus `(m−j)·q`. -/
lemma psum_const_block {r : ℕ} (s : Fin r → ℕ+) (j m : ℕ) (hjm : j ≤ m) (q : ℕ)
    (h : ∀ x : ℕ, j ≤ x → x < m → pad0 s x = q) :
    psum s m = psum s j + (m - j) * q := by
  classical
  have hjadd : j + (m - j) = m := by omega
  calc
    psum s m = (∑ x ∈ Finset.range m, pad0 s x) := by rfl
    _ = (∑ x ∈ Finset.range (j + (m - j)), pad0 s x) := by
          rw [hjadd]
    _ = (∑ x ∈ Finset.range j, pad0 s x) + (∑ t ∈ Finset.range (m - j), pad0 s (j + t)) := by
          rw [Finset.sum_range_add]
    _ = psum s j + (∑ t ∈ Finset.range (m - j), pad0 s (j + t)) := by rfl
    _ = psum s j + (m - j) * q := by
          have hs : (∑ t ∈ Finset.range (m - j), pad0 s (j + t)) = (m - j) * q := by
            calc
              (∑ t ∈ Finset.range (m - j), pad0 s (j + t)) = (∑ t ∈ Finset.range (m - j), q) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    have hjt : j + t < m := by
                      have ht' : t < m - j := Finset.mem_range.mp ht
                      omega
                    exact h (j + t) (by omega) hjt
              _ = (m - j) * q := by
                    rw [Finset.sum_const]
                    simp
          rw [hs]

/-- ★ Type-2 prefix sum at `k` is strictly smaller than that of `s` (the paper's
`t'₁+…+t'ₖ < s₁+…+sₖ`). -/
lemma type2_psum_lt_k (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
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
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inl i))) k < psum s k := by
  classical
  intro D Bs Q i
  have hkdec : j + 1 + (k - j - 1) = k := by omega
  have hdec := type2_psum_after F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i (k - j - 1)
  have hqN := BCq_fiber_prefix_qN F (k - j - 1) R0 hbhd i
  have hc1 : psum (Q.c (Sum.inr (Sum.inl i))) k =
      psum (Q.c (Sum.inr (Sum.inl i))) (j + 1 + (k - j - 1)) := by
    exact congrArg (psum (Q.c (Sum.inr (Sum.inl i)))) (by omega : k = j + 1 + (k - j - 1))
  have hle1 : psum (Q.c (Sum.inr (Sum.inl i))) k ≤ psum s j + 1 + (k - j - 1) * Nat.card F := by
    rw [hc1]
    rw [hdec]
    have hqN' : psum (expTail (D.cB i)) (k - j - 1) ≤ (k - j - 1) * Nat.card F := hqN
    exact add_le_add_right hqN' (psum s j + 1)
  -- psum s k = psum s j + (k−j−1)q + s_{k-1}
  have hkm1 : k - 1 < r := by omega
  have hp1 : psum s (k - 1) = psum s j + ((k - 1) - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hx1 hx2
      have hxr : x < r := by omega
      have hval : (s ⟨x, hxr⟩ : ℕ) = Nat.card F := hmid ⟨x, hxr⟩ hx1 hx2
      rw [pad0_of_lt s hxr]
      exact hval
  have hsu2 := psum_succ s (k - 1)
  have hkk : (k - 1) + 1 = k := by omega
  have hp2 : psum s k = psum s j + ((k - 1) - j) * Nat.card F + (s ⟨k - 1, hkm1⟩ : ℕ) := by
    rw [hkk] at hsu2
    rw [hsu2]
    rw [hp1]
    rw [pad0_of_lt s hkm1]
  have h1sk : 1 < (s ⟨k - 1, hkm1⟩ : ℕ) := by
    have hq2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  calc
    psum (Q.c (Sum.inr (Sum.inl i))) k ≤ psum s j + 1 + (k - j - 1) * Nat.card F := hle1
    _ < psum s j + ((k - 1) - j) * Nat.card F + (s ⟨k - 1, hkm1⟩ : ℕ) := by
          have hn : (k - 1) - j = k - j - 1 := by omega
          rw [hn]
          omega
    _ = psum s k := by
          rw [hp2]
end ZagierHoffmanPositiveChar
