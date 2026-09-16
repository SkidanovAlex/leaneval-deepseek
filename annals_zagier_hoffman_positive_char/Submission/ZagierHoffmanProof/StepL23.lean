import Submission.ZagierHoffmanProof.StepL22

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L23: the pre-prefix leading-tuple value helpers

`bstarBase` is Lemma 2.9's merged head `(q+w1) :: (s_{k+1}, …, s_r)` at the
Prop-2.12 configuration (equal to `(s_k, …, s_r)`).  `bstarBase_head` /
`bstarBase_tail` record its values (head `s_k` via `w1Of_add_pnat`, tail = `sTail`),
and `qsTuple_qregion` the `q`-values in the leading `(k−j−1)`-`q` block.  These are
the three value-pieces of the main `bstarLeadingTuple_value` lemma (every position
equals the corresponding tail slice of `s`, given the middle-entries-are-`q`
hypothesis): head (done in StepL22), q-region (via `qsTuple_qregion` + `hmid`),
tail (via `bstarBase_tail` + the depth identity).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

-- helpers (from the StepL23 draft)
noncomputable def bstarBase (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) : Fin (r - k + 1) → ℕ+ :=
  consVec ⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
    Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩
    (sTail r s k hkr)

lemma bstarBase_head (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    (bstarBase F r s k hk1 hkr hbig) ⟨0, (by omega : 0 < r - k + 1)⟩ = s ⟨k - 1, by omega⟩ := by
  have hz := consVec_zero ⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
    Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩ (sTail r s k hkr)
  change (consVec ⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
      Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩
      (sTail r s k hkr)) ⟨0, (by omega : 0 < r - k + 1)⟩ = s ⟨k - 1, by omega⟩
  rw [hz]
  exact w1Of_add_pnat F r s k hk1 hkr hbig

lemma bstarBase_tail (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (idx : Fin (r - k)) :
    (bstarBase F r s k hk1 hkr hbig) ⟨(idx : ℕ) + 1, by omega⟩ = sTail r s k hkr idx := by
  change (consVec ⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
      Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩
      (sTail r s k hkr)) ⟨(idx : ℕ) + 1, by omega⟩ = sTail r s k hkr idx
  exact consVec_succ ⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
    Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩ (sTail r s k hkr) idx

lemma qsTuple_qregion (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (ℓ' : Fin ((r - k + 1) + (k - j - 1))) (hlt : (ℓ' : ℕ) < k - j - 1) :
    qsTuple F (k - j - 1) (r - k + 1) (bstarBase F r s k hk1 hkr hbig) ℓ' = qExp F := by
  have v := value_qsTuple F (k - j - 1) (r - k + 1) (bstarBase F r s k hk1 hkr hbig) ℓ'
  rw [v]
  simp [hlt]

/-- The pre-prefix leading tuple equals the tail slice of `s`: every position `ℓ`
has value `s_{j+ℓ}` (1-indexed `s_{j+ℓ}`), given the middle entries
`s_{j+1}, …, s_{k-1}` are all `q` (`hmid`). -/
lemma bstarLeadingTuple_value (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 →
      (s i : ℕ) = Nat.card F) :
    ∀ ℓ : Fin ((r - k + 1) + (k - j - 1) + 1),
      (bstarLeadingTuple F r s k j hk1 hkr hj1 hjk hbig) ℓ =
        s ⟨(j - 1) + (ℓ : ℕ), by
          have hlt : (ℓ : ℕ) < (r - k + 1) + (k - j - 1) + 1 := ℓ.isLt
          omega⟩ := by
  classical
  intro ℓ
  by_cases hz : (ℓ : ℕ) = 0
  · have hℓ0 : ℓ = ⟨0, (by omega : 0 < (r - k + 1) + (k - j - 1) + 1)⟩ := Fin.ext (by simpa using hz)
    rw [hℓ0]
    rw [bstarLeadingTuple_head F r s k j hk1 hkr hj1 hjk hbig]
    congr 1
  · have hpos : 0 < (ℓ : ℕ) := Nat.pos_of_ne_zero hz
    let ℓ' : Fin ((r - k + 1) + (k - j - 1)) := ⟨(ℓ : ℕ) - 1, by
      have hlt : (ℓ : ℕ) < (r - k + 1) + (k - j - 1) + 1 := ℓ.isLt
      omega⟩
    have hℓ : ℓ = ⟨(ℓ' : ℕ) + 1, by omega⟩ := by
      apply Fin.ext
      simp [ℓ']
      omega
    rw [hℓ]
    change (qsTuple F (k - j - 1) (r - k + 1) (bstarBase F r s k hk1 hkr hbig)) ℓ' =
      s ⟨(j - 1) + ((ℓ' : ℕ) + 1), by omega⟩
    by_cases h1 : (ℓ' : ℕ) < k - j - 1
    · have hq := qsTuple_qregion F r s k j hk1 hkr hj1 hjk hbig ℓ' h1
      rw [hq]
      have hidxr : (j - 1) + ((ℓ' : ℕ) + 1) < r := by
        have hlt' : (ℓ' : ℕ) < (r - k + 1) + (k - j - 1) := ℓ'.isLt
        omega
      have hge : (j : ℕ) ≤ (j - 1) + ((ℓ' : ℕ) + 1) := by omega
      have hltk : (j - 1) + ((ℓ' : ℕ) + 1) < k - 1 := by omega
      have hmid' : (s ⟨(j - 1) + ((ℓ' : ℕ) + 1), hidxr⟩ : ℕ) = Nat.card F := by
        apply hmid ⟨(j - 1) + ((ℓ' : ℕ) + 1), hidxr⟩
        · exact hge
        · exact hltk
      apply Subtype.ext
      change (qExp F : ℕ) = (s ⟨(j - 1) + ((ℓ' : ℕ) + 1), hidxr⟩ : ℕ)
      rw [hmid']
      rfl
    · have h2 : ¬ (ℓ' : ℕ) < k - j - 1 := h1
      have v := value_qsTuple F (k - j - 1) (r - k + 1) (bstarBase F r s k hk1 hkr hbig) ℓ'
      rw [v]
      simp [h2]
      let idx : Fin (r - k + 1) := ⟨(ℓ' : ℕ) - (k - j - 1), by
        have hlt' : (ℓ' : ℕ) < (r - k + 1) + (k - j - 1) := ℓ'.isLt
        omega⟩
      change (bstarBase F r s k hk1 hkr hbig) idx =
        s ⟨(j - 1) + ((ℓ' : ℕ) + 1), by omega⟩
      by_cases hz2 : (idx : ℕ) = 0
      · have hz2' : (ℓ' : ℕ) - (k - j - 1) = 0 := by simpa [idx] using hz2
        have hℓk : (ℓ' : ℕ) = k - j - 1 := by omega
        have hidx0 : idx = ⟨0, (by omega : 0 < r - k + 1)⟩ := Fin.ext (by simpa using hz2)
        rw [hidx0]
        rw [bstarBase_head F r s k hk1 hkr hbig]
        congr 1
        apply Fin.ext
        have hind : (k - 1) = (j - 1) + ((ℓ' : ℕ) + 1) := by omega
        exact hind
      · have hidx1 : 0 < (idx : ℕ) := Nat.pos_of_ne_zero hz2
        let idx' : Fin (r - k) := ⟨(idx : ℕ) - 1, by
          have hlti : (idx : ℕ) < r - k + 1 := idx.isLt
          omega⟩
        have hidx : idx = ⟨(idx' : ℕ) + 1, by omega⟩ := by
          apply Fin.ext
          simp [idx']
          omega
        rw [hidx]
        rw [bstarBase_tail F r s k hk1 hkr hbig idx']
        change s ⟨k + (idx' : ℕ), by omega⟩ =
          s ⟨(j - 1) + ((ℓ' : ℕ) + 1), by omega⟩
        congr 1
        apply Fin.ext
        have hind2 : k + (idx' : ℕ) = (j - 1) + ((ℓ' : ℕ) + 1) := by
          have h2' : k - j - 1 ≤ (ℓ' : ℕ) := by omega
          have hidx1' : 0 < (ℓ' : ℕ) - (k - j - 1) := by
            simpa [idx] using hidx1
          simp [idx, idx']
          rw [Nat.sub_sub]
          omega
        exact hind2

end ZagierHoffmanPositiveChar
