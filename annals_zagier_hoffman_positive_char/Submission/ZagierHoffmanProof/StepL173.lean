import Submission.ZagierHoffmanProof.StepL172
import Submission.ZagierHoffmanProof.StepL144
import Submission.ZagierHoffmanProof.StepL46

set_option autoImplicit false
set_option maxHeartbeats 20000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L173: ★★ the G5 b-side DEPTH invariant and AMBIENT STEP

The G5 (all-`q` front) chain of `maink_case1_j0` (StepL146) applied at its own level `k`
with AMBIENT target `Λ ≥ k` needs, for every b-member `D.cB p`, the measure descent
`ambNu Λ m < ambNu Λ s`.  This module supplies the missing ingredient: the STRICT depth
invariant

  ★ `maink_g5_bSide_dep_gt` : `r < (BCqIter F (k−1) (toData F R0)).depB p`,

i.e. every b-member is STRICTLY deeper than the input `s`.  (The plan asked only for
`r ≤ D.depB p` plus an `Init` tie-break; the strict form is what the uniform prefix bound
`BCqIterO_cB_psum_le` + the telescope `lemma29_X_telescope` actually give, and it makes the
equal-depth case VACUOUS — no `Init` analysis is needed.)

PROOF OF THE DEPTH INVARIANT (contradiction from `d ≤ r`, `d := D.depB p`):
the iterate prefix bound with the base bound `1 + G(m−1)` gives, for `k − 1 ≤ ℓ`,
`psum (D.cB p) ℓ ≤ (k−1)q + 1 + G(ℓ − k)`; with the telescope this is
`= psum s (ℓ−1)` as soon as `ℓ ≥ k+1`.  At `ℓ = d` (the member's own depth) the left side
is `weight (D.cB p) d = P_d(q)`-weight `= psum s r`, so `d ≤ r` forces
`psum s r ≤ psum s (d−1) < psum s r`, a contradiction.  (`d ≤ k` is even easier:
`psum s r ≤ (k−1)q + 1 < (k−1)q + s_{k−1} ≤ psum s r`.)
The remaining member facts (`weight`, ambient horder) are StepL144's
`maink_g5_bSide_weight` / `maink_g5_bSide_order`, assembled exactly along StepL172's a-side
ambient step (`ambNu_lt_of_depth_gt` decides every b-member).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ The G5 b-side STRICT depth invariant: every b-member of the iterate is strictly
deeper than the input `s`. -/
theorem maink_g5_bSide_dep_gt (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (hXw : ∀ j : R0.ιB, weight (R0.depB j - 1) (expTail (R0.cB j)) =
      psum s r - psum s (k - 1) - 1)
    (hbndB : ∀ j : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j)) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ p : D.ιB, r < D.depB p := by
  classical
  intro D p
  by_contra hcon
  push Not at hcon
  let G : ℕ → ℕ := fun m => psumSeq (tupPadSum (single (qMinusExp F))
    (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m
  have hbase := maink_g5_R0_b_psum_le F r s k hk1 hkr hbig R0 hbhd hbndB
  have h : RelData.BCqIterO F (k - 1) (toData F R0) = D :=
    RelData.BCqIterO_eq_BCqIter F (k - 1) (toData F R0)
  have hG0 : G 0 = 0 := by
    dsimp only [G, psumSeq]
    simp
  -- the member's weight is `psum s r`
  have hwt : psum (D.cB p) (D.depB p) = psum s r := by
    rw [psum_ge_depth (D.cB p) (le_refl (D.depB p))]
    rw [maink_g5_bSide_weight F r s k hk1 hkr hallq R0 hbhd hXw p, psum_self s]
  -- the uniform iterate prefix bound at the base bound `1 + G(·-1)`
  have hkey : ∀ ℓ : ℕ, k - 1 ≤ ℓ →
      psum (D.cB p) ℓ ≤ (k - 1) * Nat.card F + (1 + G (ℓ - k)) := by
    intro ℓ hℓ
    have hstep := RelData.BCqIterO_cB_psum_le F (k - 1) (toData F R0)
      (fun m => 1 + G (m - 1)) hbase (h.symm ▸ p) ℓ hℓ
    have hps := RelData.psum_cB_eq_of_eq F h p ℓ
    have hidx : ℓ - (k - 1) - 1 = ℓ - k := by omega
    rw [hps, hidx] at hstep
    exact hstep
  have hpk : psum s k = (k - 1) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) := by
    have hsu := psum_last r s k hk1 hkr
    rw [hsu, maink_g5_psum_front F r s k hallq]
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have hbig' : (Nat.card F : ℕ) + 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := by omega
  have hsk_le : (k - 1) * Nat.card F + ((Nat.card F) + 1) ≤ psum s r := by
    calc
      (k - 1) * Nat.card F + ((Nat.card F) + 1)
          ≤ (k - 1) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) :=
            Nat.add_le_add_left hbig' _
      _ = psum s k := hpk.symm
      _ ≤ psum s r := psum_mono s hkr
  rcases Nat.lt_or_ge (D.depB p) (k + 1) with hdk | hdklt
  · -- the member is too shallow: `psum s r ≤ (k−1)q + 1 < psum s r`
    have hmono := psum_mono (D.cB p) (by omega : D.depB p ≤ k)
    have hb := hkey k (by omega)
    have hGk : G (k - k) = 0 := by
      rw [show k - k = 0 from by omega]
      exact hG0
    rw [hGk] at hb
    have hfin : psum s r ≤ (k - 1) * Nat.card F + 1 := by
      rw [← hwt]
      exact le_trans hmono hb
    omega
  · -- the member is deeper than `k`: the telescope at its own depth
    have hd1 : 1 ≤ D.depB p := D.hdepB p
    have htel : G (D.depB p - k) = ((s ⟨k - 1, by omega⟩ : ℕ) - 1) +
        (psum s (D.depB p - 1) - psum s k) := by
      dsimp only [G]
      have htel := lemma29_X_telescope F r s k hk1 hkr hbig (D.depB p - k) (by omega)
      have hidx : k + (D.depB p - k) - 1 = D.depB p - 1 := by omega
      rw [hidx] at htel
      exact htel
    have hb := hkey (D.depB p) (by omega)
    rw [htel] at hb
    have hsum_eq : (k - 1) * Nat.card F + (1 + ((s ⟨k - 1, by omega⟩ : ℕ) - 1 +
        (psum s (D.depB p - 1) - psum s k))) = psum s (D.depB p - 1) := by
      rw [hpk]
      have hle1 : psum s k ≤ psum s (D.depB p - 1) := psum_mono s (by omega)
      have hsp : 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := (s ⟨k - 1, by omega⟩).pos
      omega
    have hle2 : psum s r ≤ psum s (D.depB p - 1) := by
      rw [← hwt]
      calc
        psum (D.cB p) (D.depB p)
            ≤ (k - 1) * Nat.card F + (1 + ((s ⟨k - 1, by omega⟩ : ℕ) - 1 +
                (psum s (D.depB p - 1) - psum s k))) := hb
        _ = psum s (D.depB p - 1) := hsum_eq
    have hlt : psum s (D.depB p - 1) < psum s r :=
      psum_lt_psum_of_lt s (by omega) (le_refl r)
    omega

/-- ★★ The G5 b-side AMBIENT STEP: every b-member decreases `ambNu Λ` from `s`. -/
theorem maink_g5_bSide_amb_step (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (hXw : ∀ j : R0.ιB, weight (R0.depB j - 1) (expTail (R0.cB j)) =
      psum s r - psum s (k - 1) - 1)
    (hbndB : ∀ j : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j)) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ p : D.ιB, ∀ (w : ℕ), weight r s = w → ∀ (Λ : ℕ), k ≤ Λ →
      ambNu Λ (Nat.card F) w (D.cB p) < ambNu Λ (Nat.card F) w s := by
  classical
  intro D p w hw Λ hΛ
  have hle := maink_g5_bSide_order F r s k hk1 hkr hbig hallq R0 hbhd hbndB p Λ hΛ
  have hdep := maink_g5_bSide_dep_gt F r s k hk1 hkr hbig hallq R0 hbhd hXw hbndB p
  have hmw : weight (D.depB p) (D.cB p) = w :=
    (maink_g5_bSide_weight F r s k hk1 hkr hallq R0 hbhd hXw p).trans hw
  have hmd_le : D.depB p ≤ w := by
    rw [← hmw]
    exact weight_ge_depth _ _
  have hs_le : r ≤ w := by
    rw [← hw]
    exact weight_ge_depth r s
  exact ambNu_lt_of_depth_gt Λ (Nat.card F) w s _ hs_le hmd_le hdep hle

end ZagierHoffmanPositiveChar
