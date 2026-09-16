import Submission.ZagierHoffmanProof.StepL121
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L122: the member-level type-2/3 tail form (SESSION 258l)

Assembly from StepL121's prefix bound to the paper's (2.13) member-level form
t ≤ (q^{k₁−j−1}, s_{k₁}−1, sTail): writing X(t) := psumSeq (tupPadSum (single
qMinus) (consVec w1 B)) t for the level-0 prefix, the two lemmas here are
  • type23_X_le: X(t) ≤ (s⟨k₁−1⟩ − 1) + psum (sTail-at-k₁) (t − 1)
      [unfolding X = psum(single qMinus) + psum(w1::B): (q−1)+w1 =
      s⟨k₁−1⟩−1 via q+w1 = s⟨k₁−1⟩];
  • type23_tail_member: composing type23_tail_prefix with type23_X_le at
      t = m − n gives, for every m,
      psum (expTail ((BCqIter n (toData R0)).cB i)) m
        ≤ n·q + (s⟨k₁−1⟩ − 1) + psum (sTail-at-k₁) (m − n − 1)
      — the member-level (q^{n}, s_{k₁}−1, sTail)-prefix form (tight for
      m ≥ n+1; the m ≤ n slack is harmless for the prefix assembly, which uses
      m = n (n·q) and m ≥ n+1 only).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The level-0 b-tail prefix X(t) is ≤ (s⟨k₁−1⟩ − 1) + (sTail prefix at t−1):
(q−1) + w1 = s⟨k₁−1⟩ − 1 (with w1 = s⟨k₁−1⟩ − q). -/
lemma type23_X_le (k₁ r : ℕ) (s : Fin r → ℕ+) (hk1 : 1 ≤ k₁) (hkr : k₁ ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k₁ - 1, by omega⟩ : ℕ)) (t : ℕ) :
    psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) t ≤
      ((s ⟨k₁ - 1, by omega⟩ : ℕ) - 1) + psum (sTail r s k₁ hkr) (t - 1) := by
  classical
  rw [psumSeq_tupPadSum_split (single (qMinusExp F))
    (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr)) t]
  have hq : psum (single (qMinusExp F)) t ≤ (qMinusExp F : ℕ) := by
    by_cases ht : 0 < t
    · have hp := psum_single_of_pos (qMinusExp F) ht
      omega
    · have ht0 : t = 0 := by omega
      subst t
      rw [psum_zero]
      have hq1 : 0 ≤ (qMinusExp F : ℕ) := by omega
      exact hq1
  have hw : psum (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr)) t ≤
      (w1Of F r s k₁ hk1 hkr hbig : ℕ) + psum (sTail r s k₁ hkr) (t - 1) := by
    by_cases ht : 0 < t
    · have hp := psum_consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr) (t - 1)
      -- hp : psum (consVec w1 B) ((t−1)+1) = w1 + psum B (t−1)
      have hts : (t - 1) + 1 = t := by omega
      rw [hts] at hp
      omega
    · have ht0 : t = 0 := by omega
      subst t
      rw [psum_zero]
      have hw0 : (w1Of F r s k₁ hk1 hkr hbig : ℕ) + psum (sTail r s k₁ hkr) 0 ≥ 0 := by omega
      exact hw0
  calc
    psum (single (qMinusExp F)) t + psum (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr)) t
        ≤ (qMinusExp F : ℕ) + ((w1Of F r s k₁ hk1 hkr hbig : ℕ) + psum (sTail r s k₁ hkr) (t - 1)) := by
          exact add_le_add hq hw
    _ = ((s ⟨k₁ - 1, by omega⟩ : ℕ) - 1) + psum (sTail r s k₁ hkr) (t - 1) := by
          have hqval : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
          have hwadd := w1Of_add F r s k₁ hk1 hkr hbig
          -- hwadd : (qExp F : ℕ) + (w1 : ℕ) = (s⟨k₁−1⟩ : ℕ)
          have hwval : (w1Of F r s k₁ hk1 hkr hbig : ℕ) = (s ⟨k₁ - 1, by omega⟩ : ℕ) - Nat.card F := by
            dsimp [w1Of]
          have hq2 : 2 ≤ Nat.card F := card_ge_two F
          omega

/-- ★ The member-level type-2/3 tail prefix form (paper (2.13)): the iterated
b-fiber tails at the (k₁,j)-chain satisfy, for every m,
psum (expTail (level-n .cB i)) m ≤ n·q + (s⟨k₁−1⟩ − 1) + psum(sTail)(m−n−1). -/
theorem type23_tail_member (k₁ r j : ℕ) (s : Fin r → ℕ+) (hk1 : 1 ≤ k₁) (hkr : k₁ ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k₁ - 1, by omega⟩ : ℕ))
    (hj1 : 1 ≤ j) (hjk : j ≤ k₁ - 1) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA),
      R0.aA u = 1 ∧
      (∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) ∧
      ∀ i : (RelData.BCqIter F (k₁ - j - 1) (toData F R0)).ιB, ∀ m : ℕ,
        psum (expTail ((RelData.BCqIter F (k₁ - j - 1) (toData F R0)).cB i)) m ≤
          (k₁ - j - 1) * Nat.card F + ((s ⟨k₁ - 1, by omega⟩ : ℕ) - 1) +
            psum (sTail r s k₁ hkr) (m - (k₁ - j - 1) - 1) := by
  classical
  rcases type23_tail_prefix F k₁ r j s hk1 hkr hbig hj1 hjk with ⟨R0, u, hau, hbhd, hbound⟩
  refine ⟨R0, u, hau, hbhd, ?_⟩
  intro i m
  have h1 := hbound i m
  -- h1 : psum (expTail (D.cB i)) m ≤ nq + X (m − n)
  have h2 := type23_X_le F k₁ r s hk1 hkr hbig (m - (k₁ - j - 1))
  calc
    psum (expTail ((RelData.BCqIter F (k₁ - j - 1) (toData F R0)).cB i)) m
        ≤ (k₁ - j - 1) * Nat.card F +
            psumSeq (tupPadSum (single (qMinusExp F))
              (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr)))
              (m - (k₁ - j - 1)) := h1
    _ ≤ (k₁ - j - 1) * Nat.card F + (((s ⟨k₁ - 1, by omega⟩ : ℕ) - 1) +
            psum (sTail r s k₁ hkr) ((m - (k₁ - j - 1)) - 1)) := by
          exact Nat.add_le_add_left h2 ((k₁ - j - 1) * Nat.card F)
    _ = (k₁ - j - 1) * Nat.card F + ((s ⟨k₁ - 1, by omega⟩ : ℕ) - 1) +
            psum (sTail r s k₁ hkr) (m - (k₁ - j - 1) - 1) := by omega

end ZagierHoffmanPositiveChar
