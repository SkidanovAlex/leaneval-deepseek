import Submission.CertPacked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

open scoped BigOperators
open Finset

/-!
# A degree-aware bound on the slot coefficients

The packed representation (`Submission/CertPacked.lean`) stores one `BB`-bit block per state, so
reading off a coefficient (`unpack_pack`) needs every coefficient *at a certificate state* to be
below `2^BB`.  The states all have weighted degree `degV m ≤ 24`, and at such `m` the
coefficients of the slot products are far smaller than the sum of *all* coefficients (the crude
capacity bound `xslots_le_cap`), which is dominated by the high-degree monomials.

The bound used here evaluates the slot polynomials at `x_v = E^(-2(v+1))` and clears the
denominators: for every slot list `L` and every `m`,

  `xslots L m · E^(24·|L|) ≤ (∏_{s ∈ L} slotEval E s) · E^(degV m)`   (`xslots_scaled_le`),

where `slotEval E s = E^24 · s(E^(-2), …, E^(-24))` is a natural number.  At a state
(`degV m ≤ 24`) this gives `xslots L m · E^(24·|L|) ≤ (∏ slotEval E s) · E^24`, and the right-hand
side is checked against `2^BB · E^(24·|L|)` by one kernel computation per level, over the 272
states (`slotBound_50`, `slotBound_49`).  With `E = 2^7` this certifies coefficients below `2^248`
(the true maximum is below `2^204`), so `BB = 256` suffices.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The scaled value `E^24 · s(E^(-2), …, E^(-24))` of a slot polynomial. -/
def slotEval (E : ℕ) : CertSlot → ℕ
  | CertSlot.A =>
      E ^ 24 + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1)) * E ^ (24 - 2 * ((v : ℕ) + 1))
  | CertSlot.H w =>
      Nat.factorial (2 * ((w : ℕ) + 1)) * E ^ 24
        + ∑ v : Fin 12,
            Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)) * E ^ (24 - 2 * ((v : ℕ) + 1))

theorem degV_zero : degV (0 : MV) = 0 := by
  simp [degV]

/-- One term of the slot recursion, under the induction hypothesis for the tail. -/
theorem slot_term_le (E K : ℕ) (t : List CertSlot)
    (ih : ∀ m : MV, xslots t m * E ^ (24 * t.length) ≤ K * E ^ degV m)
    (v : Fin 12) (m : MV) (c : ℕ) :
    (if 1 ≤ m v then c * xslots t (m - evec v) else 0) * E ^ (24 * (t.length + 1))
      ≤ c * E ^ (24 - 2 * ((v : ℕ) + 1)) * (K * E ^ degV m) := by
  split_ifs with h
  · have hd := degV_sub_evec_add m v h
    have hv : (v : ℕ) < 12 := v.2
    have hexp : degV (m - evec v) + 24 = (24 - 2 * ((v : ℕ) + 1)) + degV m := by omega
    have hpow : E ^ (24 * (t.length + 1)) = E ^ (24 * t.length) * E ^ 24 := by
      rw [Nat.mul_succ, pow_add]
    have h1 : c * xslots t (m - evec v) * E ^ (24 * (t.length + 1))
        = c * (xslots t (m - evec v) * E ^ (24 * t.length)) * E ^ 24 := by
      rw [hpow]; ring
    have h2 : c * (xslots t (m - evec v) * E ^ (24 * t.length)) * E ^ 24
        ≤ c * (K * E ^ degV (m - evec v)) * E ^ 24 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (ih _))
    have h3 : c * (K * E ^ degV (m - evec v)) * E ^ 24
        = c * E ^ (24 - 2 * ((v : ℕ) + 1)) * (K * E ^ degV m) := by
      have : E ^ degV (m - evec v) * E ^ 24 = E ^ (24 - 2 * ((v : ℕ) + 1)) * E ^ degV m := by
        rw [← pow_add, ← pow_add, hexp]
      calc c * (K * E ^ degV (m - evec v)) * E ^ 24
          = c * K * (E ^ degV (m - evec v) * E ^ 24) := by ring
        _ = c * K * (E ^ (24 - 2 * ((v : ℕ) + 1)) * E ^ degV m) := by rw [this]
        _ = c * E ^ (24 - 2 * ((v : ℕ) + 1)) * (K * E ^ degV m) := by ring
    rw [h1]
    exact le_of_le_of_eq h2 h3
  · simp

/-- **The scaled coefficient bound.** -/
theorem xslots_scaled_le (E : ℕ) (L : List CertSlot) (m : MV) :
    xslots L m * E ^ (24 * L.length) ≤ (L.map (slotEval E)).prod * E ^ degV m := by
  induction L generalizing m with
  | nil =>
      rw [xslots_nil]
      split_ifs with h
      · subst h; simp [degV_zero]
      · simp
  | cons s t ih =>
      have hpow : E ^ (24 * (t.length + 1)) = E ^ (24 * t.length) * E ^ 24 := by
        rw [Nat.mul_succ, pow_add]
      have h0 : ∀ c : ℕ, c * xslots t m * E ^ (24 * (t.length + 1))
          ≤ c * E ^ 24 * ((t.map (slotEval E)).prod * E ^ degV m) := by
        intro c
        have e1 : c * xslots t m * E ^ (24 * (t.length + 1))
            = c * (xslots t m * E ^ (24 * t.length)) * E ^ 24 := by rw [hpow]; ring
        have e2 : c * ((t.map (slotEval E)).prod * E ^ degV m) * E ^ 24
            = c * E ^ 24 * ((t.map (slotEval E)).prod * E ^ degV m) := by ring
        rw [e1, ← e2]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (ih m))
      rw [List.map_cons, List.prod_cons, List.length_cons]
      cases s with
      | A =>
          rw [xslots_cons_A, add_mul, Finset.sum_mul]
          have hA := h0 1
          rw [one_mul, one_mul] at hA
          refine le_trans (add_le_add hA (Finset.sum_le_sum (fun v _ =>
            slot_term_le E ((t.map (slotEval E)).prod) t ih v m
              (Nat.factorial (2 * ((v : ℕ) + 1)))))) (le_of_eq ?_)
          rw [← Finset.sum_mul, slotEval]
          ring
      | H w =>
          rw [xslots_cons_H, add_mul, Finset.sum_mul]
          refine le_trans (add_le_add (h0 (Nat.factorial (2 * ((w : ℕ) + 1))))
            (Finset.sum_le_sum (fun v _ =>
              slot_term_le E ((t.map (slotEval E)).prod) t ih v m
                (Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)))))) (le_of_eq ?_)
          rw [← Finset.sum_mul, slotEval]
          ring

/-- A coefficient at a state is below `2^BB` once the scaled bound is checked. -/
theorem xslots_lt_of_bound (E : ℕ) (hE : 0 < E) (L : List CertSlot) (m : MV)
    (hm : degV m ≤ 24)
    (hb : (L.map (slotEval E)).prod * E ^ 24 < 2 ^ BB * E ^ (24 * L.length)) :
    xslots L m < 2 ^ BB := by
  have h1 := xslots_scaled_le E L m
  have h2 : E ^ degV m ≤ E ^ 24 := Nat.pow_le_pow_right hE hm
  have h3 : xslots L m * E ^ (24 * L.length) < 2 ^ BB * E ^ (24 * L.length) :=
    lt_of_le_of_lt (le_trans h1 (Nat.mul_le_mul_left _ h2)) hb
  exact Nat.lt_of_mul_lt_mul_right h3

/-- The scaled bound at level `50`, for every certificate state as row signature. -/
theorem slotBound_50 : certStates.all (fun n => decide
    (((slotList 50 n).map (slotEval (2 ^ 7))).prod * (2 ^ 7) ^ 24
      < 2 ^ BB * (2 ^ 7) ^ (24 * (slotList 50 n).length))) = true := by
  decide +kernel

/-- The scaled bound at level `49`, for every certificate state as row signature. -/
theorem slotBound_49 : certStates.all (fun n => decide
    (((slotList 49 n).map (slotEval (2 ^ 7))).prod * (2 ^ 7) ^ 24
      < 2 ^ BB * (2 ^ 7) ^ (24 * (slotList 49 n).length))) = true := by
  decide +kernel

/-- **Coefficients at the states are below the block size** (level `50`). -/
theorem xslots_state_lt_50 (n : MV) (hn : n ∈ certStates) (m : MV) (hm : m ∈ certStates) :
    xslots (slotList 50 n) m < 2 ^ BB :=
  xslots_lt_of_bound (2 ^ 7) (by norm_num) _ m (degV_le_of_mem_certStates m hm)
    (of_decide_eq_true (List.all_eq_true.mp slotBound_50 n hn))

/-- **Coefficients at the states are below the block size** (level `49`). -/
theorem xslots_state_lt_49 (n : MV) (hn : n ∈ certStates) (m : MV) (hm : m ∈ certStates) :
    xslots (slotList 49 n) m < 2 ^ BB :=
  xslots_lt_of_bound (2 ^ 7) (by norm_num) _ m (degV_le_of_mem_certStates m hm)
    (of_decide_eq_true (List.all_eq_true.mp slotBound_49 n hn))

end Commons.NumberTheory.MaynardSieve
