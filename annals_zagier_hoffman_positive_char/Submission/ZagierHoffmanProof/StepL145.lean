import Submission.ZagierHoffmanProof.StepL144
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L145: the iterate `a`-prefix formula and the G5 a-side order (SESSION 259x)

  • ★ `RelData.BCqIter_cA_psum` — the iterate `a`-prefix formula
      `psum (cA_{n}(i)) ℓ = n·q + psum (cA_0 i) (ℓ−n)`  for `ℓ ≥ n`
    (the prefix companion of StepL32's `BCqIter_cA_weight`; each level contributes
    exactly the head `q` via `psum_consVec_sub_one`);
  • ★★ `maink_g5_aSide_order` — the G5 a-side order condition
      `∀ ℓ ≥ k, psum (D.cA i) ℓ ≤ psum s ℓ`  (`D := BCqIter (k−1) (toData R0)`)
    by `BCqIter_cA_psum` + the level-0 prefix bound `hpref` + the
    `qExp`-telescoping `lemma29_qExp_telescope` at `m = ℓ−k+1` and the all-q front
    (`maink_g5_psum_front`).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The iterate `a`-tuple prefix formula: each of the `n` prepended `q`'s shows up
as a `q` in the prefix sum. -/
lemma RelData.BCqIter_cA_psum (n : ℕ) (E : RelData F) (i : E.ιA) (ℓ : ℕ) (hℓ : n ≤ ℓ) :
    psum ((RelData.BCqIter F n E).cA (RelData.iterIdx F n E i)) ℓ =
      n * Nat.card F + psum (E.cA i) (ℓ - n) := by
  revert E i
  induction n with
  | zero =>
      intro E i
      change psum (E.cA i) ℓ = 0 * Nat.card F + psum (E.cA i) (ℓ - 0)
      rw [Nat.zero_mul, Nat.zero_add, Nat.sub_zero]
  | succ n ih =>
      intro E i
      change psum ((RelData.BCqIter F n (RelData.BCq F E)).cA
          (RelData.iterIdx F n (RelData.BCq F E) i)) ℓ =
        (n + 1) * Nat.card F + psum (E.cA i) (ℓ - (n + 1))
      have hih := ih (by omega : n ≤ ℓ) (RelData.BCq F E) i
      have hstep : psum ((RelData.BCq F E).cA i) (ℓ - n) =
          Nat.card F + psum (E.cA i) (ℓ - n - 1) := by
        change psum (consVec (qExp F) (E.cA i)) (ℓ - n) =
          Nat.card F + psum (E.cA i) (ℓ - n - 1)
        rw [psum_consVec_sub_one (qExp F) (E.cA i) (ℓ - n) (by omega)]
        rfl
      rw [hih, hstep]
      have hidx : ℓ - n - 1 = ℓ - (n + 1) := by omega
      rw [hidx, Nat.succ_mul]
      omega

/-- ★★ The G5 a-side order condition: `a`-members are prefix-`≤ s` for all `ℓ ≥ k`. -/
theorem maink_g5_aSide_order (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ i : D.ιA, i ≠ RelData.iterIdx F (k - 1) (toData F R0) u →
      ∀ ℓ : ℕ, k ≤ ℓ → psum (D.cA i) ℓ ≤ psum s ℓ := by
  classical
  intro D i hi ℓ hℓ
  let i₀ : R0.ιA := Eq.mpr (RelData.BCqIter_ιA F (k - 1) (toData F R0)).symm i
  have hiter : RelData.iterIdx F (k - 1) (toData F R0) i₀ = i := by
    dsimp only [RelData.iterIdx, i₀]
    exact eq_mpr_symm_id (RelData.BCqIter_ιA F (k - 1) (toData F R0)) i
  have hps := RelData.BCqIter_cA_psum F (k - 1) (toData F R0) i₀ ℓ (by omega)
  rw [hiter] at hps
  rw [hps]
  have hpre := hpref i₀ (by intro hc; exact hi (by rw [← hiter, hc])) (ℓ - (k - 1))
  have htel := lemma29_qExp_telescope F r s k hk1 hkr hbig (ℓ - (k - 1)) (by omega)
  have htel' : psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (ℓ - (k - 1)) =
      (s ⟨k - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k) := by
    rw [htel]
    congr 1
    have hidx : k + (ℓ - (k - 1)) - 1 = ℓ := by omega
    rw [hidx]
  have hb : psum ((toData F R0).cA i₀) (ℓ - (k - 1)) ≤
      (s ⟨k - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k) := by
    rw [← htel']
    exact hpre
  -- psum s k = (k−1)·q + s_{k−1}
  have hpk : psum s k = (k - 1) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) := by
    have hsucc := psum_succ s (k - 1)
    have hk : (k - 1) + 1 = k := by omega
    rw [hk] at hsucc
    rw [hsucc, pad0_of_lt s (by omega : k - 1 < r), maink_g5_psum_front F r s k hallq]
  have hmono : psum s k ≤ psum s ℓ := psum_mono s hℓ
  omega

end ZagierHoffmanPositiveChar
