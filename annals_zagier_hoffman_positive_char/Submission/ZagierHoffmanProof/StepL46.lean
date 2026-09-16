import Submission.ZagierHoffmanProof.StepL35

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L46: the level-0 prefix-bound X telescopes into `s`-prefixes (CASE-1 ℓ>k stone)

Option-(i) first stone (PLAN SESSION 186): the per-member `prefix-ℓ ≤` orders for
CASE-1 at `ℓ ∈ (k, depth)` need the level-0 `b`-tail prefix bound
`X m := psumSeq (tupPadSum (single (qMinusExp F)) (consVec (w1Of …) (sTail …))) m`
(StepL34's `lemma_2_9_config_data` conjunct `hbndB`) converted into `s`-prefix data.
★ `lemma29_X_telescope`: for `m ≥ 1`,
    X m = (s⟨k−1⟩ − 1) + (psum s (k + m − 1) − psum s k),
so a type-3 member's `ℓ`-prefix (m = ℓ−k+1) and a type-2 member's `ℓ`-prefix
(m = ℓ−k) both collapse exactly onto `psum s ℓ` / `psum s (ℓ−1)` (the paper's
Props 2.12/2.13 per-type claims).  The helpers: `psum_sTail_add` (s-prefixes
telescope through `sTail`) and `psumSeq_tupPadSum_split`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `s`-prefixes telescope through the tail: `psum s (k + n) = psum s k + psum (sTail) n`. -/
lemma psum_sTail_add {r k : ℕ} (s : Fin r → ℕ+) (hkr : k ≤ r) (n : ℕ) :
    psum s (k + n) = psum s k + psum (sTail r s k hkr) n := by
  classical
  change (∑ x ∈ Finset.range (k + n), pad0 s x) =
    psum s k + psum (sTail r s k hkr) n
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [pad0_sTail]

/-- A `tupPadSum`-prefix is the sum of the two padded tuple-prefixes. -/
lemma psumSeq_tupPadSum_split {r k : ℕ} (a : Fin r → ℕ+) (b : Fin k → ℕ+) (m : ℕ) :
    psumSeq (tupPadSum a b) m = psum a m + psum b m := by
  classical
  dsimp [psumSeq, tupPadSum, psum]
  rw [Finset.sum_add_distrib]

/-- ★ The level-0 reference prefix bound `X` telescopes into `s`-prefixes:
`X m = (s_k − 1) + (psum s (k + m − 1) − psum s k)` for `m ≥ 1`.  (Extends
StepL35's `lemma29_X1_le`, which is the `m = 1` case, to all `m`.) -/
lemma lemma29_X_telescope (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) (m : ℕ) (hm : 1 ≤ m) :
    (psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) =
      ((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s (k + m - 1) - psum s k) := by
  classical
  let w1 : ℕ+ := w1Of F r s k hk1 hkr hbig
  let B : Fin (r - k) → ℕ+ := sTail r s k hkr
  have hsplit : psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 B)) m =
      psum (single (qMinusExp F)) m + psum (consVec w1 B) m := by
    exact psumSeq_tupPadSum_split (single (qMinusExp F)) (consVec w1 B) m
  have hq := psum_single_of_pos (qMinusExp F) (by omega : 0 < m)
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
    psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 B)) m
        = psum (single (qMinusExp F)) m + psum (consVec w1 B) m := hsplit
    _ = (qMinusExp F : ℕ) + psum (consVec w1 B) m := by rw [hq]
    _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + psum B (m - 1)) := by rw [hc]
    _ = ((qMinusExp F : ℕ) + (w1 : ℕ)) + (psum s (k + m - 1) - psum s k) := by
          rw [hB]
          omega
    _ = ((s ⟨k - 1, by omega⟩ : ℕ) - 1) + (psum s (k + m - 1) - psum s k) := by
          have hw1 : (w1 : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F := by
            dsimp [w1, w1Of]
          have hqmin : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
          rw [hqmin, hw1]
          have hq1 : 1 ≤ Nat.card F := by
            have h2 : 2 ≤ Nat.card F := card_ge_two F
            omega
          omega

end ZagierHoffmanPositiveChar
