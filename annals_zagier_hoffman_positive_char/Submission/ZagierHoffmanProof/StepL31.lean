import Submission.ZagierHoffmanProof.StepL30
import Submission.ZagierHoffmanProof.StepL29

set_option autoImplicit false
set_option maxHeartbeats 100000000
universe u
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L31: type-1 prefix-k bounds of the (2.14) chain (chunk 1: index transport)

The type-1 members `Q.c (inl i)` of the (2.14) chain have tuple `(s₁..s_j) ++ D.cA i`
with `D.cA i` the `n := k−j−1`-iterate `a`-tuple (`n` leading `q`'s then the original
`R0.cA i₀`).  This first chunk of StepL31 records the arbitrary-iterate-index
transport that the type-1 value facts need: an iterate `a`-index `i` is the base
index `i₀ := Eq.mpr (BCqIter_ιA n (toData R0)).symm i` transported back
(`RelData.BCqIter_index_cast`), the iterate `a`-depths add `n`
(`RelData.BCqIter_depA_cast`), and the `a`-coefficients are unchanged
(`RelData.BCqIter_aA_cast`); `eq_mpr_symm_id` is the generic transport-roundtrip.
With these, the existing iterIdx-form lemmas (StepL6 `RelData.BCqIter_cA_value` /
`BCqIter_depA_at` / `BCqIter_cA_at` = qsTuple) apply to arbitrary type-1 indices.
Next chunks: type-1 value facts at Q-positions `x ∈ [j, k−1)` (= q) and `k−1`
(= `(R0.cA i₀)₁`), then `psum (Q.c (inl i)) k = psum s j + (k−1−j)q + (R0.cA i₀)₁`
via `psum_const_block` + `psum_succ`, and the strict `< psum s k` from the
`hleA`-head hypothesis `(R0.cA i₀)₁ < s_k` + `hmid`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Transport along an equality and back is the identity (generic). -/
lemma eq_mpr_symm_id {α β : Sort u} (h : α = β) (x : α) :
    Eq.mpr h (Eq.mpr h.symm x) = x := by
  cases h
  rfl

/-- An arbitrary `a`-index of the `n`-fold iterate is the transported base index:
`iterIdx` is a roundtrip of the `BCqIter_ιA` equality. -/
lemma RelData.BCqIter_index_cast (n : ℕ) (D : RelData F) :
    ∀ i : (RelData.BCqIter F n D).ιA,
      RelData.iterIdx F n D (Eq.mpr (RelData.BCqIter_ιA F n D).symm i) = i := by
  intro i
  unfold RelData.iterIdx
  exact eq_mpr_symm_id (RelData.BCqIter_ιA F n D) i

/-- The `a`-depth at an arbitrary iterate index is the base depth plus `n`. -/
lemma RelData.BCqIter_depA_cast (n : ℕ) (D : RelData F) (i : (RelData.BCqIter F n D).ιA) :
    (RelData.BCqIter F n D).depA i =
      D.depA (Eq.mpr (RelData.BCqIter_ιA F n D).symm i) + n := by
  let i₀ : D.ιA := Eq.mpr (RelData.BCqIter_ιA F n D).symm i
  have hi : RelData.iterIdx F n D i₀ = i := RelData.BCqIter_index_cast F n D i
  have hd : (RelData.BCqIter F n D).depA (RelData.iterIdx F n D i₀) = D.depA i₀ + n :=
    RelData.BCqIter_depA_at F n D i₀
  calc
    (RelData.BCqIter F n D).depA i
        = (RelData.BCqIter F n D).depA (RelData.iterIdx F n D i₀) := by
          exact congrArg (fun j : (RelData.BCqIter F n D).ιA => (RelData.BCqIter F n D).depA j) hi.symm
    _ = D.depA i₀ + n := hd

/-- The `a`-coefficient at an arbitrary iterate index is the base one. -/
lemma RelData.BCqIter_aA_cast (n : ℕ) (D : RelData F) (i : (RelData.BCqIter F n D).ιA) :
    (RelData.BCqIter F n D).aA i = D.aA (Eq.mpr (RelData.BCqIter_ιA F n D).symm i) := by
  let i₀ : D.ιA := Eq.mpr (RelData.BCqIter_ιA F n D).symm i
  have hi : RelData.iterIdx F n D i₀ = i := RelData.BCqIter_index_cast F n D i
  calc
    (RelData.BCqIter F n D).aA i
        = (RelData.BCqIter F n D).aA (RelData.iterIdx F n D i₀) := by
          exact congrArg (fun j : (RelData.BCqIter F n D).ιA => (RelData.BCqIter F n D).aA j) hi.symm
    _ = D.aA i₀ := RelData.BCqIter_aA_at F n D i₀


/-- The first `n` padded entries of an iterate `a`-tuple (in iterIdx form) are `q`. -/
lemma BCqIter_cA_pad0_front (n : ℕ) (R0 : BinaryRel F) (i₀ : R0.ιA) (a : ℕ) (ha : a < n) :
    pad0 ((RelData.BCqIter F n (toData F R0)).cA (RelData.iterIdx F n (toData F R0) i₀)) a =
      Nat.card F := by
  classical
  have hdep : (RelData.BCqIter F n (toData F R0)).depA
      (RelData.iterIdx F n (toData F R0) i₀) = R0.depA i₀ + n :=
    RelData.BCqIter_depA_at F n (toData F R0) i₀
  have ha0 : a < R0.depA i₀ + n := by
    have hpos : 0 < R0.depA i₀ := R0.hdepA i₀
    omega
  have hb : a < (RelData.BCqIter F n (toData F R0)).depA
      (RelData.iterIdx F n (toData F R0) i₀) := by
    rw [hdep]
    exact ha0
  rw [pad0_of_lt ((RelData.BCqIter F n (toData F R0)).cA
      (RelData.iterIdx F n (toData F R0) i₀)) hb]
  have hidx : (⟨a, hb⟩ : Fin ((RelData.BCqIter F n (toData F R0)).depA
        (RelData.iterIdx F n (toData F R0) i₀))) =
      Fin.cast (RelData.BCqIter_depA_at F n (toData F R0) i₀).symm ⟨a, ha0⟩ := by
    apply Fin.ext
    simp
  rw [hidx]
  have hv := RelData.BCqIter_cA_value F n (toData F R0) i₀ ⟨a, ha0⟩
  have hv' := congrArg (fun t : ℕ+ => (t : ℕ)) hv
  rw [hv']
  simp [ha]
  rfl


/-- The `a`-head of the iterate `a`-tuple (in iterIdx form) is the base head: at
position `n` the `n` leading `q`'s end and the original tuple begins. -/
lemma BCqIter_cA_pad0_head (n : ℕ) (R0 : BinaryRel F) (i₀ : R0.ιA) :
    pad0 ((RelData.BCqIter F n (toData F R0)).cA (RelData.iterIdx F n (toData F R0) i₀)) n =
      ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
  classical
  have hdep : (RelData.BCqIter F n (toData F R0)).depA
      (RelData.iterIdx F n (toData F R0) i₀) = R0.depA i₀ + n :=
    RelData.BCqIter_depA_at F n (toData F R0) i₀
  have hn0 : n < R0.depA i₀ + n := by
    have hpos : 0 < R0.depA i₀ := R0.hdepA i₀
    omega
  have hb : n < (RelData.BCqIter F n (toData F R0)).depA
      (RelData.iterIdx F n (toData F R0) i₀) := by
    rw [hdep]
    exact hn0
  rw [pad0_of_lt ((RelData.BCqIter F n (toData F R0)).cA
      (RelData.iterIdx F n (toData F R0) i₀)) hb]
  have hidx : (⟨n, hb⟩ : Fin ((RelData.BCqIter F n (toData F R0)).depA
        (RelData.iterIdx F n (toData F R0) i₀))) =
      Fin.cast (RelData.BCqIter_depA_at F n (toData F R0) i₀).symm ⟨n, hn0⟩ := by
    apply Fin.ext
    simp
  rw [hidx]
  have hv := RelData.BCqIter_cA_value F n (toData F R0) i₀ ⟨n, hn0⟩
  have hv' := congrArg (fun t : ℕ+ => (t : ℕ)) hv
  rw [hv']
  simp
  rfl

/-- Type-1 members of the (2.14) chain at full positions `x ≥ j`: the value is the
`(x−j)`-th padded entry of the iterate `a`-tuple `D.cA i`. -/
lemma type1_pad0_shift (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιA, ∀ (x : ℕ), j ≤ x →
      pad0 (Q.c (Sum.inl i)) x = pad0 (D.cA i) (x - j) := by
  classical
  intro D Bs Q i x hxj
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inl i) =
      Bs.dep (Sum.inl i) + (sPrefix r s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i)
  have hBsdep : Bs.dep (Sum.inl i) = D.depA i + 1 := by
    dsimp [Bs, ofBstarOver]
  by_cases hm : x < Q.dep (Sum.inl i)
  · -- in range: value chain
    have hge : (sPrefix r s j (by omega) (by omega)).length ≤ x := by omega
    have b' : x - (sPrefix r s j (by omega) (by omega)).length < Bs.dep (Sum.inl i) := by
      rw [hBsdep]
      have hm0 : x < Q.dep (Sum.inl i) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have hxaj : x - j < D.depA i := by
      have hm0 : x < (D.depA i + 1) + (j - 1) := by
        rw [hQdep, hBsdep, hlen] at hm
        exact hm
      omega
    have h1 : ((Q.c (Sum.inl i)) ⟨x, hm⟩ : ℕ) =
        ((Bs.c (Sum.inl i)) ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
      have hv := prependList_c_base_value F Bs (sPrefix r s j (by omega) (by omega))
        (Sum.inl i) x hm hge
      apply congrArg (fun v : ℕ+ => (v : ℕ))
      calc
        (Q.c (Sum.inl i)) ⟨x, hm⟩
            = (Bs.c (Sum.inl i)) ⟨x - (sPrefix r s j (by omega) (by omega)).length,
                (by
                  have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i)
                  rw [hd] at hm
                  omega)⟩ := hv
        _ = (Bs.c (Sum.inl i)) ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩ := by
              congr 1
    have hcBs : Bs.c (Sum.inl i) = consVec (s ⟨j - 1, by omega⟩) (D.cA i) := by
      dsimp [Bs, ofBstarOver, D]
    have h2 : ((Bs.c (Sum.inl i)) ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
        ((consVec (s ⟨j - 1, by omega⟩) (D.cA i)) ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
      apply congrArg (fun v : ℕ+ => (v : ℕ))
      exact congrFun hcBs ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩
    have hbp : x - (sPrefix r s j (by omega) (by omega)).length = (x - j) + 1 := by omega
    have h3 : ((consVec (s ⟨j - 1, by omega⟩) (D.cA i))
          ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
        ((D.cA i) ⟨x - j, hxaj⟩ : ℕ) := by
      have hcv := consVec_nat_value (s ⟨j - 1, by omega⟩) (D.cA i)
        (x - (sPrefix r s j (by omega) (by omega)).length) b'
      have hnz : x - (sPrefix r s j (by omega) (by omega)).length ≠ 0 := by omega
      calc
        ((consVec (s ⟨j - 1, by omega⟩) (D.cA i))
              ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ)
            = ((D.cA i) ⟨(x - (sPrefix r s j (by omega) (by omega)).length) - 1,
                (by omega : (x - (sPrefix r s j (by omega) (by omega)).length) - 1 < D.depA i)⟩ : ℕ) := by
              apply congrArg (fun v : ℕ+ => (v : ℕ))
              rw [hcv]
              simp [hnz]
        _ = ((D.cA i) ⟨x - j, hxaj⟩ : ℕ) := by
              rw [show (⟨(x - (sPrefix r s j (by omega) (by omega)).length) - 1,
                  (by omega : (x - (sPrefix r s j (by omega) (by omega)).length) - 1 < D.depA i)⟩ :
                      Fin (D.depA i)) = ⟨x - j, hxaj⟩ from (by
                apply Fin.ext
                simp [hbp])]
    have hval : ((Q.c (Sum.inl i)) ⟨x, hm⟩ : ℕ) = ((D.cA i) ⟨x - j, hxaj⟩ : ℕ) := by
      calc
        ((Q.c (Sum.inl i)) ⟨x, hm⟩ : ℕ)
            = ((Bs.c (Sum.inl i)) ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
        _ = ((consVec (s ⟨j - 1, by omega⟩) (D.cA i)) ⟨x - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
        _ = ((D.cA i) ⟨x - j, hxaj⟩ : ℕ) := h3
    rw [pad0_of_lt (Q.c (Sum.inl i)) hm]
    rw [pad0_of_lt (D.cA i) hxaj]
    exact hval
  · -- out of range: both zero
    have hgeQ : Q.dep (Sum.inl i) ≤ x := le_of_not_gt hm
    have hp1 : pad0 (Q.c (Sum.inl i)) x = 0 := pad0_of_ge (Q.c (Sum.inl i)) hgeQ
    rw [hp1]
    have hdep : D.depA i ≤ x - j := by
      have hge0 : Q.dep (Sum.inl i) ≤ x := hgeQ
      rw [hQdep, hBsdep, hlen] at hge0
      omega
    have hp2 : pad0 (D.cA i) (x - j) = 0 := pad0_of_ge (D.cA i) hdep
    rw [hp2]


/-- Type-1 prefix sum at `k` (iterIdx-index form): the front `s₁..s_j`, the `n = k−j−1`
leading `q`'s of the iterate `a`-tuple, and the head of the original `a`-tuple. -/
lemma type1_psum_decompose (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      psum (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) k =
        psum s j + (k - 1 - j) * Nat.card F +
          ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
  classical
  intro D Bs Q i₀
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  have hsu := psum_succ (Q.c (Sum.inl i)) (k - 1)
  have hkk : (k - 1) + 1 = k := by omega
  have hpkm1 : psum (Q.c (Sum.inl i)) (k - 1) =
      psum (Q.c (Sum.inl i)) j + (k - 1 - j) * Nat.card F := by
    apply psum_const_block (s := Q.c (Sum.inl i)) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hxj hxkm1
      have hsh := type1_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i x hxj
      have hxa : x - j < k - j - 1 := by omega
      have hfront := BCqIter_cA_pad0_front F (k - j - 1) R0 i₀ (x - j) hxa
      rw [hsh]
      simpa [i] using hfront
  have hpj : psum (Q.c (Sum.inl i)) j = psum s j :=
    a_side_psum_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  have hlast : pad0 (Q.c (Sum.inl i)) (k - 1) = ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
    have hsh := type1_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i (k - 1) (by omega)
    have hsub : (k - 1) - j = k - j - 1 := by omega
    have hhead := BCqIter_cA_pad0_head F (k - j - 1) R0 i₀
    rw [hsh]
    rw [hsub]
    simpa [i] using hhead
  calc
    psum (Q.c (Sum.inl i)) k
        = psum (Q.c (Sum.inl i)) (k - 1) + pad0 (Q.c (Sum.inl i)) (k - 1) := by
          rw [hkk] at hsu
          exact hsu
    _ = (psum s j + (k - 1 - j) * Nat.card F) + pad0 (Q.c (Sum.inl i)) (k - 1) := by
          rw [hpkm1, hpj]
    _ = psum s j + (k - 1 - j) * Nat.card F + ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
          rw [hlast]


/-- Type-1 prefix sum at `k` is strictly below that of `s` when the original
`a`-tuple head is below `s_k` (the `hleA` first-entry bound): the paper's type-1
`t'₁+…+t'ₖ < s₁+…+sₖ`, dispatching type-1 outputs in Prop 3.2's inner induction. -/
lemma type1_psum_lt_k (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
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
    ∀ i₀ : R0.ιA,
      (((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) →
        psum (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) k < psum s k := by
  classical
  intro D Bs Q i₀ hhead
  have hdec := type1_psum_decompose F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀
  -- hdec : psum (Q.c (inl (iterIdx i₀))) k = psum s j + (k−1−j)q + head
  have hkm1 : k - 1 < r := by omega
  -- psum s (k−1) = psum s j + (k−1−j)·q:
  have hpkm1 : psum s (k - 1) = psum s j + (k - 1 - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hxj hxkm1
      have hxr : x < r := by omega
      have hm := hmid ⟨x, hxr⟩ hxj hxkm1
      rw [pad0_of_lt s hxr]
      exact hm
  have hsu := psum_succ s (k - 1)
  have hkk : (k - 1) + 1 = k := by omega
  -- psum s k = psum s (k−1) + s_{k−1}:
  have hpk : psum s k = psum s j + (k - 1 - j) * Nat.card F + (s ⟨k - 1, hkm1⟩ : ℕ) := by
    rw [hkk] at hsu
    rw [hsu]
    rw [hpkm1]
    rw [pad0_of_lt s hkm1]
  calc
    psum (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) k
        = psum s j + (k - 1 - j) * Nat.card F + ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := hdec
    _ < psum s j + (k - 1 - j) * Nat.card F + (s ⟨k - 1, hkm1⟩ : ℕ) := by
          exact Nat.add_lt_add_left hhead (psum s j + (k - 1 - j) * Nat.card F)
    _ = psum s k := by
          rw [hpk]


end ZagierHoffmanPositiveChar
