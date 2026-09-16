import Submission.ZagierHoffmanProof.StepL143
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L144: the G5 b-side weight, prefix drop and order (SESSION 259w)

The b-side member facts of the G5 (j = 0) CASE-1 chain at SYMBOLIC `k`, i.e. for
`D := BCqIter F (k−1) (toData R0)`:
  • ★ `maink_g5_R0_b_weight` — the base `b`-tuples have weight
    `psum s r − psum s (k−1)` (base fold: `weight_head_tail` + head 1 + `hXw`);
  • ★ `maink_g5_bSide_weight` — every b-member has weight `weight r s = w`
    (the iterate weight `BCqIterO_cB_weight` + the base fold + the all-q front);
  • ★ `RelData.BCqIterO_cB_psum_le` — the iterate PREFIX bound with a UNIFORM
    base prefix bound `g`: `psum = n·q + g(ℓ−n)` (each level adds `1 + (q−1)`);
  • ★ `maink_g5_R0_b_psum_le` — the base prefix bound `1 + G(m−1)`
    (from `hbhd` + `hbndB`);
  • ★★ `maink_g5_bSide_psum_lt` — the strict drop `psum (D.cB p) k < psum s k`
    (the `ℓ = k` instance: `(k−1)q + 1 < (k−1)q + s_{k−1}` since `s_{k−1} > q`);
  • ★★ `maink_g5_bSide_order` — the order condition
    `∀ ℓ ≥ k, psum (D.cB p) ℓ ≤ psum s ℓ` (`lemma29_X_telescope` at `m = ℓ−k`).

WHY THIS SUFFICES for the (e) dispatch (SESSION 259w analysis): a b-member `m`
with weight `w` and `psum m k < psum s k` is dispatched by
  k-adm → `admExpT_self`;  else (k−1)-adm → `rec` via `MainkStep` (the drop is
  the `Or.inl`);  else `maink_not_k1adm_member_e` (its `hmdrop` is the drop and
  its `Ak1` is the chain's hypothesis) — NO entry-level bounds of the iterated
  tuples are needed (the SESSION 259v plan's worry).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## Transport of the prefix sums across an equality of `RelData`s -/

lemma RelData.psum_cB_eq_of_eq {A B : RelData F} (h : A = B) (p : B.ιB) (m : ℕ) :
    psum (A.cB (h.symm ▸ p)) m = psum (B.cB p) m := by
  cases h; rfl

/-! ## Bounds on singleton prefix sums -/

lemma psum_single_le (x : ℕ+) (m : ℕ) : psum (single x) m ≤ (x : ℕ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm, psum_zero]; exact Nat.zero_le _
  · exact le_of_eq (psum_single_of_pos x hm)

/-! ## The iterate prefix bound with a uniform base bound -/

/-- ★ The iterate prefix bound: with a UNIFORM base prefix bound `g`, the `n`-fold
iterate prefix is `n·q + g(ℓ−n)` (each level adds `1 + (q−1) = q`). -/
lemma RelData.BCqIterO_cB_psum_le (n : ℕ) (R : RelData F) (g : ℕ → ℕ)
    (hg : ∀ j : R.ιB, ∀ m : ℕ, psum (R.cB j) m ≤ g m) :
    ∀ p : (RelData.BCqIterO F n R).ιB, ∀ ℓ : ℕ, n ≤ ℓ →
      psum ((RelData.BCqIterO F n R).cB p) ℓ ≤ n * Nat.card F + g (ℓ - n) := by
  induction n with
  | zero => intro p ℓ _; simpa [RelData.BCqIterO] using hg p ℓ
  | succ n ih =>
      intro p ℓ hℓ
      let X := p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
        ((RelData.BCqIterO F n R).cB p.1)
      have hℓ1 : 1 ≤ ℓ := by omega
      have hstep : psum ((RelData.BCqIterO F (n + 1) R).cB p) ℓ =
          (1 : ℕ) + psum (X.c p.2) (ℓ - 1) := by
        show psum (consVec oneExp (X.c p.2)) ℓ = (1 : ℕ) + psum (X.c p.2) (ℓ - 1)
        rw [psum_consVec_sub_one oneExp (X.c p.2) ℓ hℓ1]
        rfl
      have hX : psum (X.c p.2) (ℓ - 1) ≤ (qMinusExp F : ℕ)
          + psum ((RelData.BCqIterO F n R).cB p.1) (ℓ - 1) := by
        calc
          psum (X.c p.2) (ℓ - 1)
              ≤ psumSeq (tupPadSum (single (qMinusExp F))
                  ((RelData.BCqIterO F n R).cB p.1)) (ℓ - 1) := (X.hle p.2).2 (ℓ - 1)
          _ = psum (single (qMinusExp F)) (ℓ - 1)
                + psum ((RelData.BCqIterO F n R).cB p.1) (ℓ - 1) :=
                psumSeq_tupPadSum_split (single (qMinusExp F)) _ (ℓ - 1)
          _ ≤ (qMinusExp F : ℕ) + psum ((RelData.BCqIterO F n R).cB p.1) (ℓ - 1) :=
                Nat.add_le_add_right (psum_single_le (qMinusExp F) (ℓ - 1)) _
      have hIH := ih p.1 (ℓ - 1) (by omega)
      have hidx : ℓ - 1 - n = ℓ - (n + 1) := by omega
      rw [hidx] at hIH
      have hq1 : 1 ≤ Nat.card F := by have h2 := card_ge_two F; omega
      have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
      rw [hqm] at hX
      have hsum : 1 + ((Nat.card F - 1) + (n * Nat.card F + g (ℓ - (n + 1)))) =
          (n + 1) * Nat.card F + g (ℓ - (n + 1)) := by
        rw [Nat.succ_mul]
        omega
      rw [hstep, ← hsum]
      omega

/-! ## The G5 base prefix bound and base weight -/

/-- ★ The base `b`-tuples satisfy the uniform prefix bound `1 + G(m−1)`. -/
theorem maink_g5_R0_b_psum_le (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (hbndB : ∀ j : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j)) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    ∀ j : R0.ιB, ∀ m : ℕ,
      psum (R0.cB j) m ≤ 1 + psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (m - 1) := by
  intro j m
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm, psum_zero]; exact Nat.zero_le _
  · have hp := psum_head_expTail (R0.hdepB j) (R0.cB j) (m - 1)
    have hms : (m - 1) + 1 = m := by omega
    rw [hms] at hp
    rw [hp, hbhd j]
    have hb := hbndB j (m - 1)
    omega

/-- ★ The G5 base `b`-tuples have weight `psum s r − psum s (k−1)`. -/
theorem maink_g5_R0_b_weight (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (hXw : ∀ j : R0.ιB, weight (R0.depB j - 1) (expTail (R0.cB j)) =
      psum s r - psum s (k - 1) - 1) :
    ∀ j : R0.ιB, weight (R0.depB j) (R0.cB j) = psum s r - psum s (k - 1) := by
  intro j
  have hwt := weight_head_tail (R0.hdepB j) (R0.cB j)
  rw [hbhd j] at hwt
  rw [hXw j] at hwt
  rw [hwt]
  have hW1 : psum s (k - 1) + 1 ≤ psum s r := by
    have hsucc := psum_succ s (k - 1)
    have hk : (k - 1) + 1 = k := by omega
    rw [hk] at hsucc
    have hmono : psum s k ≤ psum s r := psum_mono s hkr
    have hpad : 1 ≤ pad0 s (k - 1) := by
      rw [pad0_of_lt s (by omega : k - 1 < r)]
      exact (s ⟨k - 1, by omega⟩).pos
    omega
  omega

/-! ## The G5 b-side member weight -/

/-- ★ Every b-member of the G5 chain has weight `weight r s = w`. -/
theorem maink_g5_bSide_weight (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (hXw : ∀ j : R0.ιB, weight (R0.depB j - 1) (expTail (R0.cB j)) =
      psum s r - psum s (k - 1) - 1) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ p : D.ιB, weight (D.depB p) (D.cB p) = weight r s := by
  classical
  intro D p
  have hbase : ∀ j : (toData F R0).ιB,
      weight ((toData F R0).depB j) ((toData F R0).cB j) = psum s r - psum s (k - 1) :=
    maink_g5_R0_b_weight F r s k hk1 hkr R0 hbhd hXw
  have h : RelData.BCqIterO F (k - 1) (toData F R0) = D :=
    RelData.BCqIterO_eq_BCqIter F (k - 1) (toData F R0)
  have hwT := RelData.cB_weight_eq_of_eq F h p
  have hwO := RelData.BCqIterO_cB_weight F (k - 1) (toData F R0)
    (psum s r - psum s (k - 1)) hbase (h.symm ▸ p)
  rw [← hwT, hwO]
  have hpf := maink_g5_psum_front F r s k hallq
  have hmono : (k - 1) * Nat.card F ≤ psum s r := by
    rw [← hpf]
    exact psum_mono s (by omega)
  rw [hpf]
  rw [← psum_self s]
  omega

/-! ## The G5 b-side strict drop at `k` -/

/-- ★★ The strict drop of every b-member at `k`. -/
theorem maink_g5_bSide_psum_lt (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (hbndB : ∀ j : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j)) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ p : D.ιB, psum (D.cB p) k < psum s k := by
  classical
  intro D p
  let G : ℕ → ℕ := fun m => psumSeq (tupPadSum (single (qMinusExp F))
    (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m
  have hbase := maink_g5_R0_b_psum_le F r s k hk1 hkr hbig R0 hbhd hbndB
  have h : RelData.BCqIterO F (k - 1) (toData F R0) = D :=
    RelData.BCqIterO_eq_BCqIter F (k - 1) (toData F R0)
  have hps := RelData.psum_cB_eq_of_eq F h p k
  have hstep := RelData.BCqIterO_cB_psum_le F (k - 1) (toData F R0)
    (fun m => 1 + G (m - 1)) hbase (h.symm ▸ p) k (by omega)
  have hidx : k - (k - 1) - 1 = 0 := by omega
  rw [hidx] at hstep
  have hzero : G 0 = 0 := by
    dsimp only [G, psumSeq]
    simp
  rw [hzero] at hstep
  have hpk : psum s k = (k - 1) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) := by
    have hsucc := psum_succ s (k - 1)
    have hk : (k - 1) + 1 = k := by omega
    rw [hk] at hsucc
    rw [hsucc, pad0_of_lt s (by omega : k - 1 < r), maink_g5_psum_front F r s k hallq]
  calc
    psum (D.cB p) k = psum ((RelData.BCqIterO F (k - 1) (toData F R0)).cB (h.symm ▸ p)) k := hps.symm
    _ ≤ (k - 1) * Nat.card F + (1 + 0) := hstep
    _ < psum s k := by
          rw [hpk]
          have hq2 : 2 ≤ Nat.card F := card_ge_two F
          have hbig' : (Nat.card F : ℕ) + 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := by omega
          omega

/-- ★★ The G5 b-side order condition: every b-member is prefix-`≤ s` for all `ℓ ≥ k`. -/
theorem maink_g5_bSide_order (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (hbndB : ∀ j : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j)) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ p : D.ιB, ∀ ℓ : ℕ, k ≤ ℓ → psum (D.cB p) ℓ ≤ psum s ℓ := by
  classical
  intro D p ℓ hℓ
  let G : ℕ → ℕ := fun m => psumSeq (tupPadSum (single (qMinusExp F))
    (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m
  have hbase := maink_g5_R0_b_psum_le F r s k hk1 hkr hbig R0 hbhd hbndB
  have h : RelData.BCqIterO F (k - 1) (toData F R0) = D :=
    RelData.BCqIterO_eq_BCqIter F (k - 1) (toData F R0)
  have hps := RelData.psum_cB_eq_of_eq F h p ℓ
  have hstep := RelData.BCqIterO_cB_psum_le F (k - 1) (toData F R0)
    (fun m => 1 + G (m - 1)) hbase (h.symm ▸ p) ℓ (by omega)
  have hidx : ℓ - (k - 1) - 1 = ℓ - k := by omega
  rw [hidx] at hstep
  have hpk : psum s k = (k - 1) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) := by
    have hsucc := psum_succ s (k - 1)
    have hk : (k - 1) + 1 = k := by omega
    rw [hk] at hsucc
    rw [hsucc, pad0_of_lt s (by omega : k - 1 < r), maink_g5_psum_front F r s k hallq]
  have hfin : (k - 1) * Nat.card F + (1 + G (ℓ - k)) ≤ psum s ℓ := by
    rcases Nat.eq_or_lt_of_le hℓ with heq | hlt
    · rw [← heq]
      have hzero : G (k - k) = 0 := by
        have h0 : k - k = 0 := by omega
        rw [h0]
        dsimp only [G, psumSeq]
        simp
      rw [hzero, hpk]
      have hbig' : (Nat.card F : ℕ) + 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := by omega
      omega
    · have hm : 1 ≤ ℓ - k := by omega
      have htel := lemma29_X_telescope F r s k hk1 hkr hbig (ℓ - k) hm
      have hidx2 : k + (ℓ - k) - 1 = ℓ - 1 := by omega
      rw [hidx2] at htel
      show (k - 1) * Nat.card F + (1 + G (ℓ - k)) ≤ psum s ℓ
      rw [show G (ℓ - k) = (s ⟨k - 1, by omega⟩ : ℕ) - 1
        + (psum s (ℓ - 1) - psum s k) from htel]
      rw [hpk]
      have hmono : psum s (ℓ - 1) ≤ psum s ℓ := psum_mono s (by omega)
      have hmono2 : psum s k ≤ psum s (ℓ - 1) := psum_mono s (by omega)
      have hpos : 1 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := (s ⟨k - 1, by omega⟩).pos
      omega
  calc
    psum (D.cB p) ℓ = psum ((RelData.BCqIterO F (k - 1) (toData F R0)).cB (h.symm ▸ p)) ℓ := hps.symm
    _ ≤ (k - 1) * Nat.card F + (1 + G (ℓ - k)) := hstep
    _ ≤ psum s ℓ := hfin

end ZagierHoffmanPositiveChar
