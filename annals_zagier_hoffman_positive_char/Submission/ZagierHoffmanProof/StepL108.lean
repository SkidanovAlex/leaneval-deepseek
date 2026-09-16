import Submission.ZagierHoffmanProof.StepL34
import Submission.ZagierHoffmanProof.StepL32
import Submission.ZagierHoffmanProof.StepC
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L108: \u2605 maink_config_full \u2014 the generic-k CASE-1 config package
(SESSION 255) \u2014 the first Lean file of the (k, k\u22121) splice

theorem maink_config_full (k r s hk1 hkr hbig) : \u2203 R0 u hdepu hau hc0 hbhd
  hwtA hhead hXw hbndB hpref, True \u2014 from ONE rcases of lemma_2_9_rel at
(r\u2212k, w1Of-at-k, sTail-at-k) on a tuple with s\u27e8k\u22121\u27e9 > q, ALL the
config conjuncts every level-k splice needs flow (k SYMBOLIC): hdepu (depA u =
(r\u2212k)+1), hau (aA u = 1), hc0 (bstarBase at k), hbhd (b-heads 1), hwtA (a-side
weights = psum s r \u2212 psum s (k\u22121)), hhead (a-heads < s\u27e8k\u22121\u27e9),
hXw (b-tail weights = psum s r \u2212 psum s (k\u22121) \u2212 1), hbndB/hpref (the
LePad-derived prefix bounds against the qExp/qMinusExp templates).  The proofs are
the generic-k calcs (hsum := psum_last at k, weight_sTail/weight_consVec,
w1Of_add, hleA/hleB .1/.2) \u2014 the exact preamble of main2T_case1_j1/
main3_case1_j1/g5T_case1, now at symbolic k with s\u27e8k\u22121\u27e9 (no literal hnorm).
NEXT (recorded): the (k, k\u22121) CASE-1 splice body on this package \u2014
zeta_214_reindexed at (k, k\u22121) (vacuous hmid) for the \u03b6-identity, the 3-family
fold, the per-member e (k-symbolic member (k\u22121)-adm / drop dispatch) and horder
(the type*_psum_ge_k_le at (k,k\u22121)); then CASE-2 via prop213_step1 at (k,k\u22121)
and A(k)@w via lk_induction (StepL107).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
set_option autoImplicit false
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]


/-- ★ The generic-k CASE-1 config package: from ONE rcases of lemma_2_9_rel at
(r−k, w1Of-at-k, sTail-at-k) on a tuple with s⟨k−1⟩ > q, the full
config conjuncts (hdepu/hau/hc0/hwtA/hhead/hXw/hbndB/hpref) flow — the preamble
every level-k splice (main(k) CASE-1 at (k,j)) starts with.  The proofs are the
generic-k calcs: weight-preservation through the rcases' LePad (hleA .1 / hleB .1),
weight_sTail/psum_last/hsum at k, and w1Of_add. -/
theorem maink_config_full (k r : ℕ) (s : Fin r → ℕ+) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hdepu : R0.depA u = (r - k) + 1)
      (hau : R0.aA u = 1)
      (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
          (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
            bstarBase F r s k hk1 hkr hbig)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
      (hwtA : ∀ i : R0.ιA, i ≠ u → weight (R0.depA i) (R0.cA i) =
          psum s r - psum s (k - 1))
      (hhead : ∀ i : R0.ιA, i ≠ u →
          ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
      (hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
          psum s r - psum s (k - 1) - 1)
      (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
          psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
            (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m)
      (hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
          psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
            (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m),
      True := by
  classical
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hsum : psum s k = psum s (k - 1) + (s ⟨k - 1, by omega⟩ : ℕ) := by
    have hpl := psum_last r s k hk1 hkr
    simpa using hpl
  have hmono : psum s k ≤ psum s r := psum_mono s hkr
  have hmono2 : psum s (k - 1) ≤ psum s r := psum_mono s (by omega : k - 1 ≤ r)
  let w1 : ℕ+ := w1Of F r s k hk1 hkr hbig
  let B : Fin (r - k) → ℕ+ := sTail r s k hkr
  rcases lemma_2_9_rel F (r - k) w1 B with ⟨R0, u, hdep, ha, hc, hleA, hbhd, hleB, hvalid⟩
  refine ⟨R0, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact hdep
  · exact ha
  · intro hd
    simpa [bstarBase, w1, B] using hc hd
  · exact hbhd
  · intro i hi
    have hL := hleA i hi
    have hw' : (w1 : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depA i) (R0.cA i)
          = weight 1 (single (qExp F)) + weight ((r - k) + 1) (consVec w1 B) := hL.1.1
      _ = (qExp F : ℕ) + ((w1 : ℕ) + weight (r - k) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = Nat.card F + ((w1 : ℕ) + (psum s r - psum s k)) := by
            rw [show (qExp F : ℕ) = Nat.card F by rfl]
            rw [weight_sTail r s k hkr]
      _ = psum s r - psum s (k - 1) := by
            rw [hw']
            omega
  · intro i hi
    have hL2 := (hleA i hi).2
    have hwadd : (qExp F : ℕ) + (w1 : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) := by
      dsimp [w1]
      exact w1Of_add F r s k hk1 hkr hbig
    simpa [hwadd] using hL2
  · intro j'
    have hL := hleB j'
    have hw' : (w1 : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depB j' - 1) (expTail (R0.cB j'))
          = weight 1 (single (qMinusExp F)) + weight ((r - k) + 1) (consVec w1 B) := hL.1
      _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + weight (r - k) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = (Nat.card F - 1) + ((w1 : ℕ) + (psum s r - psum s k)) := by
            rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
            rw [weight_sTail r s k hkr]
      _ = psum s r - psum s (k - 1) - 1 := by
            rw [hw']
            omega
  · intro j' m
    have hL := hleB j'
    simpa [w1, B] using (hL.2 m)
  · intro i hi m
    have hL := (hleA i hi).1
    simpa [w1, B] using (hL.2 m)

end ZagierHoffmanPositiveChar
