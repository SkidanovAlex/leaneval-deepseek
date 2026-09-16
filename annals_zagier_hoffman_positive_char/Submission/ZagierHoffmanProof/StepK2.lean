import Submission.ZagierHoffmanProof.StepK

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step K2: full (r,k) Part-1 recursion content (r,k ≥ 2)

The level identity `p1_level_merge` (Prop 2.1 Part 1 at the level of first entries):
`S_d(a)·S_d(b) = P_d(a1+b1)·(S_<d(a⁻)·S_<d(b⁻)) + Σ_i Δ^i P_d(a1+b1−i)·(S_<d(i)·S_<d(a⁻)S_<d(b⁻))`
for `a = (a1 :: a⁻)` of depth r ≥ 2, `b = (b1 :: b⁻)` of depth k ≥ 2 — the generalisation
of `p1cons_level` (StepG, which covered r = 1).  From it the Data carrier theorem
`p1_full_cons` builds `P1Full r k` for r,k ≥ 2 from `P2Full (r−1) (k−1)` and the
depth-1-left family (nested Δ parts), exactly as the PLAN Session-77 design prescribes.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ Part 1 level-merge identity at depths (r,k), r,k ≥ 2 (generalises `p1cons_level`). -/
lemma p1_level_merge {r k : ℕ} (hr1 : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (hk1 : 1 < k) (hk0 : 0 < k) (hkT : 0 < k - 1)
    (a : Fin r → ℕ+) (b : Fin k → ℕ+) (d : ℕ) :
    S F r hr0 a d * S F k hk0 b d =
      P F d ⟨((a ⟨0, hr0⟩ : ℕ) + (b ⟨0, hk0⟩ : ℕ)),
            Nat.add_pos_left (PNat.pos (a ⟨0, hr0⟩)) (b ⟨0, hk0⟩ : ℕ)⟩ *
        (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d) +
      ∑ i : dIdx (a ⟨0, hr0⟩) (b ⟨0, hk0⟩),
        (ChenDeltaZ F ((a ⟨0, hr0⟩ : ℕ)) ((b ⟨0, hk0⟩ : ℕ)) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d (dHead (a ⟨0, hr0⟩) (b ⟨0, hk0⟩) i) *
          (S_lt F 1 (by omega : 0 < 1) (single (dPn (a ⟨0, hr0⟩) (b ⟨0, hk0⟩) i)) d *
            (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d))) := by
  classical
  let a1 : ℕ+ := a ⟨0, hr0⟩
  let b1 : ℕ+ := b ⟨0, hk0⟩
  let K := RatFunc.CompletionAtInfty F
  calc
    S F r hr0 a d * S F k hk0 b d
        = (P F d a1 * S_lt F (r - 1) hrT (expTail a) d) *
            (P F d b1 * S_lt F (k - 1) hkT (expTail b) d) := by
          rw [S_d_recursion F r hr1 hr0 hrT a d, S_d_recursion F k hk1 hk0 hkT b d]
          change (P F d a1 * S_lt F (r - 1) hrT (expTail a) d) *
              (P F d b1 * S_lt F (k - 1) hkT (expTail b) d) =
            (P F d a1 * S_lt F (r - 1) hrT (expTail a) d) *
              (P F d b1 * S_lt F (k - 1) hkT (expTail b) d)
          rfl
    _ = (P F d a1 * P F d b1) *
          (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d) := by
          ring
    _ = (P F d ⟨(a1 : ℕ) + (b1 : ℕ), Nat.add_pos_left (PNat.pos a1) (b1 : ℕ)⟩ +
          ∑ i : dIdx a1 b1,
            (ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : K) *
              S F 2 (by omega : 0 < 2) (thakurExp (a1 : ℕ) (b1 : ℕ) i) d) *
          (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d) := by
          rw [diag_level F d a1 b1]
    _ = P F d ⟨(a1 : ℕ) + (b1 : ℕ), Nat.add_pos_left (PNat.pos a1) (b1 : ℕ)⟩ *
            (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d) +
          (∑ i : dIdx a1 b1,
            (ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : K) *
              S F 2 (by omega : 0 < 2) (thakurExp (a1 : ℕ) (b1 : ℕ) i) d) *
            (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d) := by
          rw [add_mul]
    _ = P F d ⟨(a1 : ℕ) + (b1 : ℕ), Nat.add_pos_left (PNat.pos a1) (b1 : ℕ)⟩ *
            (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d) +
          ∑ i : dIdx a1 b1,
            ((ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : K) *
              S F 2 (by omega : 0 < 2) (thakurExp (a1 : ℕ) (b1 : ℕ) i) d *
              (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d)) := by
          rw [Finset.sum_mul]
    _ = P F d ⟨(a1 : ℕ) + (b1 : ℕ), Nat.add_pos_left (PNat.pos a1) (b1 : ℕ)⟩ *
            (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d) +
          ∑ i : dIdx a1 b1,
            (ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : K) *
              (P F d (dHead a1 b1 i) *
                (S_lt F 1 (by omega : 0 < 1) (single (dPn a1 b1 i)) d *
                  (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          let Y : K := S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d
          let Δi : K := (ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : K)
          let S1 : K := S_lt F 1 (by omega : 0 < 1) (single (dPn a1 b1 i)) d
          calc
            (Δi * S F 2 (by omega : 0 < 2) (thakurExp (a1 : ℕ) (b1 : ℕ) i) d) * Y
                = Δi * ((P F d (dHead a1 b1 i) * S1) * Y) := by
                  rw [thakur_S_two_eq F d (a1 : ℕ) (b1 : ℕ) i]
                  change (Δi * (P F d (dHead a1 b1 i) * S1)) * Y =
                    Δi * ((P F d (dHead a1 b1 i) * S1) * Y)
                  ring
            _ = Δi * (P F d (dHead a1 b1 i) * (S1 * Y)) := by
                  congr 1
                  ring
            _ = (ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : K) *
                  (P F d (dHead a1 b1 i) *
                    (S_lt F 1 (by omega : 0 < 1) (single (dPn a1 b1 i)) d *
                      (S_lt F (r - 1) hrT (expTail a) d * S_lt F (k - 1) hkT (expTail b) d))) := by
                  rfl



/-- Head-merge LePad: `(a1+b1) :: u ≤ (a1 :: A) + (b1 :: B)` from `u ≤ A + B`
(the pure-output bound of the full Part-1 cons step). -/
lemma LePad_merge_heads {L r k : ℕ} (a1 b1 : ℕ+) (u : Fin L → ℕ+)
    (A : Fin r → ℕ+) (B : Fin k → ℕ+) (h : LePad u A B) :
    LePad (consVec ⟨(a1 : ℕ) + (b1 : ℕ), Nat.add_pos_left (PNat.pos a1) (b1 : ℕ)⟩ u)
      (consVec a1 A) (consVec b1 B) := by
  classical
  let hd : ℕ+ := ⟨(a1 : ℕ) + (b1 : ℕ), Nat.add_pos_left (PNat.pos a1) (b1 : ℕ)⟩
  change LePad (consVec hd u) (consVec a1 A) (consVec b1 B)
  have hhd : (hd : ℕ) = (a1 : ℕ) + (b1 : ℕ) := rfl
  constructor
  · rw [weight_consVec, weight_consVec, weight_consVec, h.1]
    rw [hhd]
    omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        have hpre := h.2 n
        have hpre' := psumSeq_tupPadSum A B n
        rw [hpre'] at hpre
        have htg := psumSeq_tupPadSum (consVec a1 A) (consVec b1 B) (n + 1)
        rw [htg]
        rw [psum_consVec a1 A n, psum_consVec b1 B n]
        rw [hhd]
        omega



/-- Δ-output LePad: `hd :: u ≤ (a1 :: A) + (b1 :: B)` from `u ≤ (i) + C`, `C ≤ A + B`
and `hd + i = a1 + b1` (the Δ-output bound of the full Part-1 cons step). -/
lemma LePad_cons_delta {U C2 r k : ℕ} (hd i a1 b1 : ℕ+) (u : Fin U → ℕ+)
    (C : Fin C2 → ℕ+) (A : Fin r → ℕ+) (B : Fin k → ℕ+)
    (hhd : (hd : ℕ) + (i : ℕ) = (a1 : ℕ) + (b1 : ℕ))
    (h1 : LePad u (single i) C) (h2 : LePad C A B) :
    LePad (consVec hd u) (consVec a1 A) (consVec b1 B) := by
  classical
  constructor
  · calc
      weight (U + 1) (consVec hd u) = (hd : ℕ) + weight U u := weight_consVec hd u
      _ = (hd : ℕ) + ((i : ℕ) + weight C2 C) := by
            rw [h1.1, weight_single]
      _ = (hd : ℕ) + ((i : ℕ) + (weight r A + weight k B)) := by rw [h2.1]
      _ = weight (r + 1) (consVec a1 A) + weight (k + 1) (consVec b1 B) := by
            rw [weight_consVec a1 A, weight_consVec b1 B]
            omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        have hp1 := h1.2 n
        have hp1' := psumSeq_tupPadSum (single i) C n
        rw [hp1'] at hp1
        have hp2 := h2.2 n
        have hp2' := psumSeq_tupPadSum A B n
        rw [hp2'] at hp2
        have htg := psumSeq_tupPadSum (consVec a1 A) (consVec b1 B) (n + 1)
        rw [htg]
        rw [psum_consVec a1 A n, psum_consVec b1 B n]
        have hsi : psum (single i) n ≤ (i : ℕ) := by
          by_cases hn : n = 0
          · subst n
            rw [psum_zero]
            exact Nat.zero_le (i : ℕ)
          · exact (psum_single_of_pos i (Nat.pos_of_ne_zero hn)).le
        omega


/-- `consVec_zero` with a free positivity proof (the StepB8 version is bound to `by omega`;
proof irrelevance makes the two instances equal, but `simp` cannot match the bound form). -/
lemma consVec_zero' (x : ℕ+) {m : ℕ} (𝔰 : Fin m → ℕ+) {h : 0 < m + 1} :
    consVec x 𝔰 ⟨0, h⟩ = x := by
  exact consVec_zero x 𝔰

/-- Cons-form of the Part-1 level-merge identity (depths r+1, k+1 from tails of depth r,k). -/
lemma p1_level_merge_cons (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (a1 b1 : ℕ+) (A : Fin r → ℕ+) (B : Fin k → ℕ+) (d : ℕ) :
    S F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) d *
      S F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) d =
      P F d (dMerge a1 b1) * (S_lt F r hr A d * S_lt F k hk B d) +
      ∑ i : dIdx a1 b1,
        (ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d (dHead a1 b1 i) *
          (S_lt F 1 (by omega : 0 < 1) (single (dPn a1 b1 i)) d *
            (S_lt F r hr A d * S_lt F k hk B d))) := by
  classical
  rw [p1_level_merge (r := r + 1) (k := k + 1) F
    (by omega : 1 < r + 1) (by omega : 0 < r + 1) (by omega : 0 < (r + 1) - 1)
    (by omega : 1 < k + 1) (by omega : 0 < k + 1) (by omega : 0 < (k + 1) - 1)
    (consVec a1 A) (consVec b1 B) d]
  rw [consVec_zero]
  rw [consVec_zero]
  simp [expTail_consVec, dMerge, dHead, dPn]


theorem p1_full_cons (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (hP2 : P2Full F r k) (a1 b1 : ℕ+) (A : Fin r → ℕ+) (B : Fin k → ℕ+) :
    Nonempty (P1Data F (r + 1) (k + 1) (by omega : 0 < r + 1) (by omega : 0 < k + 1)
      (consVec a1 A) (consVec b1 B)) := by
  classical
  let D2 : P2Data F r k hr hk A B := Classical.choice (hP2 hr hk A B)
  letI : Fintype D2.ι := D2.fin
  let w3 : ∀ (i : dIdx a1 b1) (e : D2.ι),
      P2Data F 1 (D2.dep e) (by omega : 0 < 1) (D2.hdep e) (single (dPn a1 b1 i)) (D2.c e) :=
    fun i e => Classical.choice ((p1p2D_all F (D2.dep e) (D2.hdep e)).2 (dPn a1 b1 i) (D2.c e))
  letI : ∀ (i : dIdx a1 b1) (e : D2.ι), Fintype ((w3 i e).ι) := fun i e => (w3 i e).fin
  let ι0 : Type := D2.ι ⊕ (Σ i : dIdx a1 b1, Σ e : D2.ι, (w3 i e).ι)
  let dep0 : ι0 → ℕ := fun x => match x with
    | Sum.inl e => D2.dep e + 1
    | Sum.inr p => (w3 p.1 p.2.1).dep p.2.2 + 1
  let hdep0 : ∀ x : ι0, 0 < dep0 x := by
    intro x
    cases x with
    | inl e => dsimp [dep0]; have hp := D2.hdep e; omega
    | inr p => dsimp [dep0]; have hp := (w3 p.1 p.2.1).hdep p.2.2; omega
  let f0 : ι0 → ℤ := fun x => match x with
    | Sum.inl e => D2.f e
    | Sum.inr p => ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) p.1.1 * D2.f p.2.1 * (w3 p.1 p.2.1).f p.2.2
  let c0 : ∀ x : ι0, Fin (dep0 x) → ℕ+ := fun x => match x with
    | Sum.inl e => consVec (dMerge a1 b1) (D2.c e)
    | Sum.inr p => consVec (dHead a1 b1 p.1) ((w3 p.1 p.2.1).c p.2.2)
  have hid0 : ∀ d : ℕ,
      S F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) d *
          S F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) d =
      ∑ x : ι0, ((f0 x : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep0 x) (hdep0 x) (c0 x) d := by
    intro d
    let K := RatFunc.CompletionAtInfty F
    let G : ι0 → K := fun x => ((f0 x : ℤ) : K) * S F (dep0 x) (hdep0 x) (c0 x) d
    have hsplit1 : (∑ x : ι0, G x) = (∑ e : D2.ι, G (Sum.inl e)) +
        ∑ p : (Σ i : dIdx a1 b1, Σ e : D2.ι, (w3 i e).ι), G (Sum.inr p) := by
      have hsum := Fintype.sum_sum_type (f := G)
      rw [hsum]
    have hsplit2 : (∑ p : (Σ i : dIdx a1 b1, Σ e : D2.ι, (w3 i e).ι), G (Sum.inr p)) =
        ∑ i : dIdx a1 b1, ∑ e : D2.ι, ∑ e' : (w3 i e).ι, G (Sum.inr ⟨i, e, e'⟩) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Fintype.sum_sigma]
    have hPure : P F d (dMerge a1 b1) * (S_lt F r hr A d * S_lt F k hk B d) =
        ∑ e : D2.ι, G (Sum.inl e) := by
      calc
        P F d (dMerge a1 b1) * (S_lt F r hr A d * S_lt F k hk B d)
            = P F d (dMerge a1 b1) *
                (∑ e : D2.ι, ((D2.f e : ℤ) : K) * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d) := by
              congr 1
              exact D2.hid d
        _ = ∑ e : D2.ι, G (Sum.inl e) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e he
              calc
                P F d (dMerge a1 b1) * (((D2.f e : ℤ) : K) * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d)
                    = ((D2.f e : ℤ) : K) * (P F d (dMerge a1 b1) * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d) := by ring
                _ = ((D2.f e : ℤ) : K) * S F (D2.dep e + 1) (by omega) (consVec (dMerge a1 b1) (D2.c e)) d := by
                      rw [S_prepend F d (dMerge a1 b1) (D2.hdep e) (D2.c e)]
                _ = G (Sum.inl e) := by
                      simp [G, f0, dep0, c0, hdep0]
    have hPer : ∀ i : dIdx a1 b1,
        (ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : K) *
          (P F d (dHead a1 b1 i) *
            (S_lt F 1 (by omega : 0 < 1) (single (dPn a1 b1 i)) d *
              (S_lt F r hr A d * S_lt F k hk B d))) =
        ∑ e : D2.ι, ∑ e' : (w3 i e).ι, G (Sum.inr ⟨i, e, e'⟩) := by
      intro i
      let Δi : ℤ := ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1
      let hd : ℕ+ := dHead a1 b1 i
      have hPer' : (ChenDeltaZ F (a1 : ℕ) (b1 : ℕ) i.1 : K) *
            (P F d (dHead a1 b1 i) *
              (S_lt F 1 (by omega : 0 < 1) (single (dPn a1 b1 i)) d *
                (S_lt F r hr A d * S_lt F k hk B d))) =
          ∑ e : D2.ι, ∑ e' : (w3 i e).ι,
            ((Δi * D2.f e * (w3 i e).f e' : ℤ) : K) *
            S F ((w3 i e).dep e' + 1) (by omega) (consVec hd ((w3 i e).c e')) d := by
        let S1 : K := S_lt F 1 (by omega : 0 < 1) (single (dPn a1 b1 i)) d
        let Y : K := S_lt F r hr A d * S_lt F k hk B d
        let Z : ∀ e : D2.ι, K := fun e =>
          ∑ e' : (w3 i e).ι, (((w3 i e).f e' : ℤ) : K) * S_lt F ((w3 i e).dep e') ((w3 i e).hdep e') ((w3 i e).c e') d
        calc
          (Δi : K) * (P F d hd * (S1 * Y))
              = (Δi : K) * (P F d hd * (S1 * (∑ e : D2.ι,
                  ((D2.f e : ℤ) : K) * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d))) := by
                exact congrArg (fun q : K => (Δi : K) * (P F d hd * (S1 * q))) (D2.hid d)
          _ = (Δi : K) * (P F d hd * (∑ e : D2.ι,
                ((D2.f e : ℤ) : K) * (S1 * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d))) := by
                have hd1 : S1 * (∑ e : D2.ι,
                    ((D2.f e : ℤ) : K) * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d) =
                    ∑ e : D2.ι,
                    ((D2.f e : ℤ) : K) * (S1 * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro e he
                      ring
                exact congrArg (fun q : K => (Δi : K) * (P F d hd * q)) hd1
          _ = (Δi : K) * (P F d hd * (∑ e : D2.ι, ((D2.f e : ℤ) : K) * Z e)) := by
                have hd2 : (∑ e : D2.ι,
                    ((D2.f e : ℤ) : K) * (S1 * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d)) =
                    ∑ e : D2.ι, ((D2.f e : ℤ) : K) * Z e := by
                      apply Finset.sum_congr rfl
                      intro e he
                      dsimp [Z]
                      congr 1
                      exact (w3 i e).hid d
                exact congrArg (fun q : K => (Δi : K) * (P F d hd * q)) hd2
          _ = ∑ e : D2.ι, ∑ e' : (w3 i e).ι,
                ((Δi * D2.f e * (w3 i e).f e' : ℤ) : K) *
                S F ((w3 i e).dep e' + 1) (by omega) (consVec hd ((w3 i e).c e')) d := by
                have hd3 : (Δi : K) * (P F d hd * (∑ e : D2.ι, ((D2.f e : ℤ) : K) * Z e)) =
                    (Δi : K) * (∑ e : D2.ι, ((D2.f e : ℤ) : K) * (P F d hd * Z e)) := by
                  have hd3a : P F d hd * (∑ e : D2.ι, ((D2.f e : ℤ) : K) * Z e) =
                      ∑ e : D2.ι, ((D2.f e : ℤ) : K) * (P F d hd * Z e) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro e he
                    ring
                  exact congrArg (fun q : K => (Δi : K) * q) hd3a
                have hd4 : (Δi : K) * (∑ e : D2.ι, ((D2.f e : ℤ) : K) * (P F d hd * Z e)) =
                    ∑ e : D2.ι, ((Δi * D2.f e : ℤ) : K) * (P F d hd * Z e) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro e he
                  rw [Int.cast_mul]
                  ring
                have hd5 : ∀ e : D2.ι, P F d hd * Z e =
                    ∑ e' : (w3 i e).ι, (((w3 i e).f e' : ℤ) : K) *
                      S F ((w3 i e).dep e' + 1) (by omega) (consVec hd ((w3 i e).c e')) d := by
                  intro e
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro e' he'
                  calc
                    P F d hd * ((((w3 i e).f e' : ℤ) : K) * S_lt F ((w3 i e).dep e') ((w3 i e).hdep e') ((w3 i e).c e') d)
                        = (((w3 i e).f e' : ℤ) : K) * (P F d hd * S_lt F ((w3 i e).dep e') ((w3 i e).hdep e') ((w3 i e).c e') d) := by ring
                    _ = (((w3 i e).f e' : ℤ) : K) * S F ((w3 i e).dep e' + 1) (by omega) (consVec hd ((w3 i e).c e')) d := by
                          rw [S_prepend F d hd ((w3 i e).hdep e') ((w3 i e).c e')]
                calc
                  (Δi : K) * (P F d hd * (∑ e : D2.ι, ((D2.f e : ℤ) : K) * Z e))
                      = ∑ e : D2.ι, ((Δi * D2.f e : ℤ) : K) * (P F d hd * Z e) := by
                        rw [hd3, hd4]
                  _ = ∑ e : D2.ι, ∑ e' : (w3 i e).ι,
                        (((Δi * D2.f e : ℤ) : K) * (((w3 i e).f e' : ℤ) : K)) *
                        S F ((w3 i e).dep e' + 1) (by omega) (consVec hd ((w3 i e).c e')) d := by
                        apply Finset.sum_congr rfl
                        intro e he
                        calc
                          ((Δi * D2.f e : ℤ) : K) * (P F d hd * Z e)
                              = ((Δi * D2.f e : ℤ) : K) * (∑ e' : (w3 i e).ι,
                                  (((w3 i e).f e' : ℤ) : K) *
                                    S F ((w3 i e).dep e' + 1) (by omega) (consVec hd ((w3 i e).c e')) d) := by
                                congr 1
                                exact hd5 e
                          _ = ∑ e' : (w3 i e).ι,
                                (((Δi * D2.f e : ℤ) : K) * (((w3 i e).f e' : ℤ) : K)) *
                                S F ((w3 i e).dep e' + 1) (by omega) (consVec hd ((w3 i e).c e')) d := by
                                rw [Finset.mul_sum]
                                apply Finset.sum_congr rfl
                                intro e' he'
                                ring
                  _ = ∑ e : D2.ι, ∑ e' : (w3 i e).ι,
                        ((Δi * D2.f e * (w3 i e).f e' : ℤ) : K) *
                        S F ((w3 i e).dep e' + 1) (by omega) (consVec hd ((w3 i e).c e')) d := by
                        apply Finset.sum_congr rfl
                        intro e he
                        apply Finset.sum_congr rfl
                        intro e' he'
                        rw [← Int.cast_mul]
      simpa [G, f0, dep0, c0, hdep0] using hPer'
    change S F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) d *
        S F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) d = ∑ x : ι0, G x
    rw [p1_level_merge_cons F r k hr hk a1 b1 A B d]
    rw [hsplit1, hsplit2]
    rw [hPure]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hPer i
  have hle0 : ∀ x : ι0, LePad (c0 x) (consVec a1 A) (consVec b1 B) := by
    intro x
    cases x with
    | inl e =>
      simpa [c0, dep0, dMerge] using LePad_merge_heads a1 b1 (D2.c e) A B (D2.hle e)
    | inr p =>
      refine LePad_cons_delta (dHead a1 b1 p.1) (dPn a1 b1 p.1) a1 b1
        ((w3 p.1 p.2.1).c p.2.2) (D2.c p.2.1) A B ?hhd ?h1 ?h2
      · have hv1 : (dHead a1 b1 p.1 : ℕ) = (a1 : ℕ) + (b1 : ℕ) - p.1.1 := rfl
        have hv2 : (dPn a1 b1 p.1 : ℕ) = p.1.1 := rfl
        rw [hv1, hv2]
        have hle : p.1.1 ≤ (a1 : ℕ) + (b1 : ℕ) := by
          have hin : p.1.1 ≤ (a1 : ℕ) + (b1 : ℕ) - 1 := (Finset.mem_Icc.mp p.1.2).2
          have hy : 1 ≤ (a1 : ℕ) := PNat.pos a1
          omega
        exact Nat.sub_add_cancel hle
      · exact (w3 p.1 p.2.1).hle p.2.2
      · exact D2.hle p.2.1
  have hbd0 : ∀ x : ι0, dep0 x ≤ (r + 1) + (k + 1) := by
    intro x
    cases x with
    | inl e =>
      dsimp [dep0]
      have hb := D2.hbd e
      omega
    | inr p =>
      dsimp [dep0]
      have hb := (w3 p.1 p.2.1).hbd p.2.2
      have hb2 := D2.hbd p.2.1
      omega
  let D : P1Data F (r + 1) (k + 1) (by omega : 0 < r + 1) (by omega : 0 < k + 1)
      (consVec a1 A) (consVec b1 B) := {
    ι := ι0
    fin := inferInstance
    dep := dep0
    hdep := hdep0
    f := f0
    c := c0
    hid := hid0
    hle := hle0
    hbd := hbd0 }
  exact ⟨D⟩


/-- `a1 :: u ≤ (a1 :: A) + (b1 :: B)` from `u ≤ A + (b1 :: B)` (Part-2 A-group bound). -/
lemma LePad_cons_move {L r k : ℕ} (a1 b1 : ℕ+) (u : Fin L → ℕ+) (A : Fin r → ℕ+)
    (B : Fin k → ℕ+) (h : LePad u A (consVec b1 B)) :
    LePad (consVec a1 u) (consVec a1 A) (consVec b1 B) := by
  classical
  constructor
  · calc
      weight (L + 1) (consVec a1 u) = (a1 : ℕ) + weight L u := weight_consVec a1 u
      _ = (a1 : ℕ) + (weight r A + weight (k + 1) (consVec b1 B)) := by rw [h.1]
      _ = weight (r + 1) (consVec a1 A) + weight (k + 1) (consVec b1 B) := by
            rw [weight_consVec a1 A]
            omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        have hpre := h.2 n
        have hpre' := psumSeq_tupPadSum A (consVec b1 B) n
        rw [hpre'] at hpre
        have htg := psumSeq_tupPadSum (consVec a1 A) (consVec b1 B) (n + 1)
        rw [htg]
        rw [psum_consVec a1 A n, psum_consVec b1 B n]
        have hbt : psum (consVec b1 B) n ≤ (b1 : ℕ) + psum B n := by
          by_cases hn : n = 0
          · subst n
            rw [psum_zero]
            exact Nat.zero_le (b1 : ℕ)
          · have hc := psum_consVec b1 B (n - 1)
            rw [show (n - 1) + 1 = n by omega] at hc
            rw [hc]
            have hm : psum B (n - 1) ≤ psum B n := psum_mono B (by omega)
            omega
        omega

/-- `b1 :: u ≤ (a1 :: A) + (b1 :: B)` from `u ≤ (a1 :: A) + B` (Part-2 B-group bound). -/
lemma LePad_cons_move_right {L r k : ℕ} (a1 b1 : ℕ+) (u : Fin L → ℕ+) (A : Fin r → ℕ+)
    (B : Fin k → ℕ+) (h : LePad u (consVec a1 A) B) :
    LePad (consVec b1 u) (consVec a1 A) (consVec b1 B) := by
  classical
  constructor
  · calc
      weight (L + 1) (consVec b1 u) = (b1 : ℕ) + weight L u := weight_consVec b1 u
      _ = (b1 : ℕ) + (weight (r + 1) (consVec a1 A) + weight k B) := by rw [h.1]
      _ = weight (r + 1) (consVec a1 A) + weight (k + 1) (consVec b1 B) := by
            rw [weight_consVec b1 B]
            omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        have hpre := h.2 n
        have hpre' := psumSeq_tupPadSum (consVec a1 A) B n
        rw [hpre'] at hpre
        have htg := psumSeq_tupPadSum (consVec a1 A) (consVec b1 B) (n + 1)
        rw [htg]
        rw [psum_consVec a1 A n, psum_consVec b1 B n]
        have hbt : psum (consVec a1 A) n ≤ (a1 : ℕ) + psum A n := by
          by_cases hn : n = 0
          · subst n
            rw [psum_zero]
            exact Nat.zero_le (a1 : ℕ)
          · have hc := psum_consVec a1 A (n - 1)
            rw [show (n - 1) + 1 = n by omega] at hc
            rw [hc]
            have hm : psum A (n - 1) ≤ psum A n := psum_mono A (by omega)
            omega
        omega


theorem p2_full_cons (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (hP2A : P2Full F r (k + 1)) (hP2B : P2Full F (r + 1) k) (hP2 : P2Full F r k)
    (a1 b1 : ℕ+) (A : Fin r → ℕ+) (B : Fin k → ℕ+) :
    Nonempty (P2Data F (r + 1) (k + 1) (by omega : 0 < r + 1) (by omega : 0 < k + 1)
      (consVec a1 A) (consVec b1 B)) := by
  classical
  let D_A : P2Data F r (k + 1) hr (by omega : 0 < k + 1) A (consVec b1 B) :=
    Classical.choice (hP2A hr (by omega : 0 < k + 1) A (consVec b1 B))
  let D_B : P2Data F (r + 1) k (by omega : 0 < r + 1) hk (consVec a1 A) B :=
    Classical.choice (hP2B (by omega : 0 < r + 1) hk (consVec a1 A) B)
  let D1 : P1Data F (r + 1) (k + 1) (by omega : 0 < r + 1) (by omega : 0 < k + 1)
      (consVec a1 A) (consVec b1 B) :=
    Classical.choice (p1_full_cons F r k hr hk hP2 a1 b1 A B)
  letI : Fintype D_A.ι := D_A.fin
  letI : Fintype D_B.ι := D_B.fin
  letI : Fintype D1.ι := D1.fin
  let ι0 : Type := D_A.ι ⊕ D_B.ι ⊕ D1.ι
  let dep0 : ι0 → ℕ := fun x => match x with
    | Sum.inl e => D_A.dep e + 1
    | Sum.inr (Sum.inl e) => D_B.dep e + 1
    | Sum.inr (Sum.inr x) => D1.dep x
  let hdep0 : ∀ x : ι0, 0 < dep0 x := by
    intro x
    cases x with
    | inl e => dsimp [dep0]; have hp := D_A.hdep e; omega
    | inr p => cases p with
      | inl e => dsimp [dep0]; have hp := D_B.hdep e; omega
      | inr x => dsimp [dep0]; have hp := D1.hdep x; omega
  let f0 : ι0 → ℤ := fun x => match x with
    | Sum.inl e => D_A.f e
    | Sum.inr (Sum.inl e) => D_B.f e
    | Sum.inr (Sum.inr x) => D1.f x
  let c0 : ∀ x : ι0, Fin (dep0 x) → ℕ+ := fun x => match x with
    | Sum.inl e => consVec a1 (D_A.c e)
    | Sum.inr (Sum.inl e) => consVec b1 (D_B.c e)
    | Sum.inr (Sum.inr x) => D1.c x
  have hle0 : ∀ x : ι0, LePad (c0 x) (consVec a1 A) (consVec b1 B) := by
    intro x
    cases x with
    | inl e =>
      simpa [c0, dep0] using LePad_cons_move a1 b1 (D_A.c e) A B (D_A.hle e)
    | inr p => cases p with
      | inl e =>
        simpa [c0, dep0] using LePad_cons_move_right a1 b1 (D_B.c e) A B (D_B.hle e)
      | inr x =>
        simpa [c0, dep0] using D1.hle x
  have hbd0 : ∀ x : ι0, dep0 x ≤ (r + 1) + (k + 1) := by
    intro x
    cases x with
    | inl e =>
      dsimp [dep0]
      have hb := D_A.hbd e
      omega
    | inr p => cases p with
      | inl e =>
        dsimp [dep0]
        have hb := D_B.hbd e
        omega
      | inr x =>
        dsimp [dep0]
        have hb := D1.hbd x
        omega
  have hid0 : ∀ d : ℕ,
      S_lt F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) d *
          S_lt F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) d =
      ∑ x : ι0, ((f0 x : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (dep0 x) (hdep0 x) (c0 x) d := by
    intro d
    let K := RatFunc.CompletionAtInfty F
    let G : ι0 → K := fun x => ((f0 x : ℤ) : K) * S_lt F (dep0 x) (hdep0 x) (c0 x) d
    let Aℓ : ℕ → K := fun ℓ => S F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) ℓ
    let Bm : ℕ → K := fun m => S F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) m
    have hT1 : (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, Aℓ ℓ * Bm m) =
        ∑ e : D_A.ι, ((D_A.f e : ℤ) : K) *
          S_lt F (D_A.dep e + 1) (by omega) (consVec a1 (D_A.c e)) d := by
      calc
        (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, Aℓ ℓ * Bm m)
            = ∑ ℓ ∈ Finset.range d, Aℓ ℓ * (∑ m ∈ Finset.range ℓ, Bm m) := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              exact (Finset.mul_sum (s := Finset.range ℓ) (a := Aℓ ℓ) (f := Bm)).symm
        _ = ∑ ℓ ∈ Finset.range d, S F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) ℓ *
            S_lt F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) ℓ := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              rw [← S_lt_eq_sum_levels F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) ℓ]
        _ = ∑ ℓ ∈ Finset.range d, P F ℓ a1 * (S_lt F r hr A ℓ * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) ℓ) := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              rw [S_cons_rec F hr a1 A ℓ]
              ring
        _ = ∑ ℓ ∈ Finset.range d, P F ℓ a1 *
              (∑ e : D_A.ι, ((D_A.f e : ℤ) : K) * S_lt F (D_A.dep e) (D_A.hdep e) (D_A.c e) ℓ) := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              congr 1
              exact D_A.hid ℓ
        _ = ∑ e : D_A.ι, ((D_A.f e : ℤ) : K) *
              S_lt F (D_A.dep e + 1) (by omega) (consVec a1 (D_A.c e)) d := by
              calc
                (∑ ℓ ∈ Finset.range d, P F ℓ a1 *
                    (∑ e : D_A.ι, ((D_A.f e : ℤ) : K) * S_lt F (D_A.dep e) (D_A.hdep e) (D_A.c e) ℓ))
                    = ∑ ℓ ∈ Finset.range d, ∑ e : D_A.ι,
                        ((D_A.f e : ℤ) : K) * (P F ℓ a1 * S_lt F (D_A.dep e) (D_A.hdep e) (D_A.c e) ℓ) := by
                      apply Finset.sum_congr rfl
                      intro ℓ hℓ
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro e he
                      ring
                _ = ∑ e : D_A.ι,
                      ((D_A.f e : ℤ) : K) * (∑ ℓ ∈ Finset.range d,
                        P F ℓ a1 * S_lt F (D_A.dep e) (D_A.hdep e) (D_A.c e) ℓ) := by
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro e he
                      exact (Finset.mul_sum (s := Finset.range d)
                        (a := ((D_A.f e : ℤ) : K))
                        (f := fun ℓ : ℕ => P F ℓ a1 * S_lt F (D_A.dep e) (D_A.hdep e) (D_A.c e) ℓ)).symm
                _ = ∑ e : D_A.ι,
                      ((D_A.f e : ℤ) : K) * (∑ ℓ ∈ Finset.range d,
                        S F (D_A.dep e + 1) (by omega) (consVec a1 (D_A.c e)) ℓ) := by
                      apply Finset.sum_congr rfl
                      intro e he
                      congr 1
                      apply Finset.sum_congr rfl
                      intro ℓ hℓ
                      rw [S_prepend F ℓ a1 (D_A.hdep e) (D_A.c e)]
                _ = ∑ e : D_A.ι,
                      ((D_A.f e : ℤ) : K) * S_lt F (D_A.dep e + 1) (by omega) (consVec a1 (D_A.c e)) d := by
                      apply Finset.sum_congr rfl
                      intro e he
                      rw [← S_lt_eq_sum_levels F (D_A.dep e + 1) (by omega) (consVec a1 (D_A.c e)) d]

    have hT2 : (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, Aℓ ℓ * Bm m) =
        ∑ e : D_B.ι, ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F) *
          S_lt F (D_B.dep e + 1) (by omega) (consVec b1 (D_B.c e)) d := by
      calc
        (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, Aℓ ℓ * Bm m)
            = ∑ m ∈ Finset.range d, (∑ ℓ ∈ Finset.range m, Aℓ ℓ) * Bm m := by
              apply Finset.sum_congr rfl
              intro m hm
              exact (Finset.sum_mul (s := Finset.range m) (f := Aℓ) (a := Bm m)).symm
        _ = ∑ m ∈ Finset.range d, S_lt F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) m *
            S F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) m := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [← S_lt_eq_sum_levels F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) m]
        _ = ∑ m ∈ Finset.range d, P F m b1 * (S_lt F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) m * S_lt F k hk B m) := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [S_cons_rec F hk b1 B m]
              ring
        _ = ∑ m ∈ Finset.range d, P F m b1 *
              (∑ e : D_B.ι, ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (D_B.dep e) (D_B.hdep e) (D_B.c e) m) := by
              apply Finset.sum_congr rfl
              intro m hm
              congr 1
              exact D_B.hid m
        _ = ∑ e : D_B.ι, ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D_B.dep e + 1) (by omega) (consVec b1 (D_B.c e)) d := by
              calc
                (∑ m ∈ Finset.range d, P F m b1 *
                    (∑ e : D_B.ι, ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (D_B.dep e) (D_B.hdep e) (D_B.c e) m))
                    = ∑ m ∈ Finset.range d, ∑ e : D_B.ι,
                        ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F) * (P F m b1 * S_lt F (D_B.dep e) (D_B.hdep e) (D_B.c e) m) := by
                      apply Finset.sum_congr rfl
                      intro m hm
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro e he
                      ring
                _ = ∑ e : D_B.ι,
                      ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F) * (∑ m ∈ Finset.range d,
                        P F m b1 * S_lt F (D_B.dep e) (D_B.hdep e) (D_B.c e) m) := by
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro e he
                      exact (Finset.mul_sum (s := Finset.range d)
                        (a := ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F))
                        (f := fun m : ℕ => P F m b1 * S_lt F (D_B.dep e) (D_B.hdep e) (D_B.c e) m)).symm
                _ = ∑ e : D_B.ι,
                      ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F) * (∑ m ∈ Finset.range d,
                        S F (D_B.dep e + 1) (by omega) (consVec b1 (D_B.c e)) m) := by
                      apply Finset.sum_congr rfl
                      intro e he
                      congr 1
                      apply Finset.sum_congr rfl
                      intro m hm
                      rw [S_prepend F m b1 (D_B.hdep e) (D_B.c e)]
                _ = ∑ e : D_B.ι,
                      ((D_B.f e : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (D_B.dep e + 1) (by omega) (consVec b1 (D_B.c e)) d := by
                      apply Finset.sum_congr rfl
                      intro e he
                      rw [← S_lt_eq_sum_levels F (D_B.dep e + 1) (by omega) (consVec b1 (D_B.c e)) d]


    have hT3 : (∑ ℓ ∈ Finset.range d, Aℓ ℓ * Bm ℓ) =
        ∑ x : D1.ι, ((D1.f x : ℤ) : RatFunc.CompletionAtInfty F) *
          S_lt F (D1.dep x) (D1.hdep x) (D1.c x) d := by
      calc
        (∑ ℓ ∈ Finset.range d, Aℓ ℓ * Bm ℓ)
            = ∑ ℓ ∈ Finset.range d, S F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) ℓ *
                S F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) ℓ := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              dsimp [Aℓ, Bm]
        _ = ∑ ℓ ∈ Finset.range d, ∑ x : D1.ι,
              ((D1.f x : ℤ) : RatFunc.CompletionAtInfty F) * S F (D1.dep x) (D1.hdep x) (D1.c x) ℓ := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              exact (D1.hid ℓ)
        _ = ∑ x : D1.ι,
              ((D1.f x : ℤ) : RatFunc.CompletionAtInfty F) * (∑ ℓ ∈ Finset.range d,
                S F (D1.dep x) (D1.hdep x) (D1.c x) ℓ) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro x hx
              exact (Finset.mul_sum (s := Finset.range d)
                (a := ((D1.f x : ℤ) : RatFunc.CompletionAtInfty F))
                (f := fun ℓ : ℕ => S F (D1.dep x) (D1.hdep x) (D1.c x) ℓ)).symm
        _ = ∑ x : D1.ι,
              ((D1.f x : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (D1.dep x) (D1.hdep x) (D1.c x) d := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [← S_lt_eq_sum_levels F (D1.dep x) (D1.hdep x) (D1.c x) d]

    change S_lt F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) d *
        S_lt F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) d = ∑ x : ι0, G x
    calc
      S_lt F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) d *
          S_lt F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) d
          = (∑ ℓ ∈ Finset.range d, Aℓ ℓ) * (∑ m ∈ Finset.range d, Bm m) := by
            rw [S_lt_eq_sum_levels F (r + 1) (by omega : 0 < r + 1) (consVec a1 A) d,
                S_lt_eq_sum_levels F (k + 1) (by omega : 0 < k + 1) (consVec b1 B) d]
      _ = (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, Aℓ ℓ * Bm m) +
          (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, Aℓ ℓ * Bm m) +
          (∑ ℓ ∈ Finset.range d, Aℓ ℓ * Bm ℓ) := by
            exact Commons.Data.Finset.sum_range_mul_split (R := K) d Aℓ Bm
      _ = (∑ e : D_A.ι, ((D_A.f e : ℤ) : K) *
              S_lt F (D_A.dep e + 1) (by omega) (consVec a1 (D_A.c e)) d) +
          (∑ e : D_B.ι, ((D_B.f e : ℤ) : K) *
              S_lt F (D_B.dep e + 1) (by omega) (consVec b1 (D_B.c e)) d) +
          (∑ x : D1.ι, ((D1.f x : ℤ) : K) *
              S_lt F (D1.dep x) (D1.hdep x) (D1.c x) d) := by
            rw [hT1, hT2, hT3]
      _ = ∑ x : ι0, G x := by
            have hsplit1 : (∑ x : ι0, G x) = (∑ e : D_A.ι, G (Sum.inl e)) +
                ∑ p : D_B.ι ⊕ D1.ι, G (Sum.inr p) := by
              have hsum := Fintype.sum_sum_type (f := G)
              rw [hsum]
            have hsplit2 : (∑ p : D_B.ι ⊕ D1.ι, G (Sum.inr p)) =
                (∑ e : D_B.ι, G (Sum.inr (Sum.inl e))) +
                  ∑ x : D1.ι, G (Sum.inr (Sum.inr x)) := by
              have hsum := Fintype.sum_sum_type
                (f := fun p : D_B.ι ⊕ D1.ι => G (Sum.inr p))
              rw [hsum]
            rw [hsplit1, hsplit2]
            have hA : (∑ e : D_A.ι, ((D_A.f e : ℤ) : K) *
                  S_lt F (D_A.dep e + 1) (by omega) (consVec a1 (D_A.c e)) d) =
                ∑ e : D_A.ι, G (Sum.inl e) := by
              apply Finset.sum_congr rfl
              intro e he
              simp [G, f0, dep0, c0, hdep0]
            have hB : (∑ e : D_B.ι, ((D_B.f e : ℤ) : K) *
                  S_lt F (D_B.dep e + 1) (by omega) (consVec b1 (D_B.c e)) d) =
                ∑ e : D_B.ι, G (Sum.inr (Sum.inl e)) := by
              apply Finset.sum_congr rfl
              intro e he
              simp [G, f0, dep0, c0, hdep0]
            have hC : (∑ x : D1.ι, ((D1.f x : ℤ) : K) *
                  S_lt F (D1.dep x) (D1.hdep x) (D1.c x) d) =
                ∑ x : D1.ι, G (Sum.inr (Sum.inr x)) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp [G, f0, dep0, c0, hdep0]
            rw [hA, hB, hC]
            ac_rfl
  let D : P2Data F (r + 1) (k + 1) (by omega : 0 < r + 1) (by omega : 0 < k + 1)
      (consVec a1 A) (consVec b1 B) := {
    ι := ι0
    fin := inferInstance
    dep := dep0
    hdep := hdep0
    f := f0
    c := c0
    hid := hid0
    hle := hle0
    hbd := hbd0 }
  exact ⟨D⟩


/-- ★ Stage theorem: second-depth k+1 families from all Part-2 families at depth k. -/
theorem p1p2_full_stage (k : ℕ) (hk : 0 < k) (hPrev : ∀ r : ℕ, 0 < r → P2Full F r k) :
    ∀ r : ℕ, 0 < r → P1Full F r (k + 1) ∧ P2Full F r (k + 1) := by
  classical
  intro r
  induction r with
  | zero => intro hr; omega
  | succ m ih =>
    intro hr
    constructor
    · by_cases hm : m = 0
      · subst m
        exact (p1p2_full_left_one F (k + 1) (by omega : 0 < k + 1)).1
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        intro hr1 hk1 a b
        have hdecA := fin_succ_eq_consVec (m := m) a
        have hdecB := fin_succ_eq_consVec (m := k) b
        rw [hdecA, hdecB]
        exact p1_full_cons F m k hmpos hk (hPrev m hmpos) (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)
          (fun j : Fin m => a ⟨j.1 + 1, by omega⟩) (fun j : Fin k => b ⟨j.1 + 1, by omega⟩)
    · by_cases hm : m = 0
      · subst m
        exact (p1p2_full_left_one F (k + 1) (by omega : 0 < k + 1)).2
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        intro hr1 hk1 a b
        have hdecA := fin_succ_eq_consVec (m := m) a
        have hdecB := fin_succ_eq_consVec (m := k) b
        rw [hdecA, hdecB]
        exact p2_full_cons F m k hmpos hk (ih hmpos).2 (hPrev (m + 1) (by omega : 0 < m + 1)) (hPrev m hmpos)
          (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)
          (fun j : Fin m => a ⟨j.1 + 1, by omega⟩) (fun j : Fin k => b ⟨j.1 + 1, by omega⟩)

/-- ★ Full Prop 2.1(1)(2): both families at every depth pair. -/
theorem p1p2_full_all : ∀ (k : ℕ) (hk : 0 < k), ∀ r : ℕ, 0 < r →
    P1Full F r k ∧ P2Full F r k := by
  classical
  intro k
  induction k with
  | zero => intro hk; omega
  | succ n ih =>
    intro hk
    by_cases hn : n = 0
    · subst n
      intro r hr
      exact p1p2_full_right_one F r hr
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hPrev : ∀ r : ℕ, 0 < r → P2Full F r n := fun r hr => (ih hnpos r hr).2
      exact p1p2_full_stage F n hnpos hPrev



/-- Data witness for Prop 2.1 Part (3): `S_<d(a)·S_d(b)` as an F-combination of `S_d`. -/
structure P3Data (r k : ℕ) (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+) where
  ι : Type
  fin : Fintype ι
  dep : ι → ℕ
  hdep : ∀ i, 0 < dep i
  f : ι → ℤ
  c : ∀ i, Fin (dep i) → ℕ+
  hid : ∀ d : ℕ,
    S_lt F r hr a d * S F k hk b d =
      ∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep i) (hdep i) (c i) d
  hle : ∀ i, LePad (c i) a b
  hbd : ∀ i, dep i ≤ r + k

/-- Prop 2.1 Part (3) at depths (r,k): all mixed `S_<d(a)·S_d(b)` products. -/
def P3Full (r k : ℕ) : Prop :=
  ∀ (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+),
    Nonempty (P3Data F r k hr hk a b)


/-- `x :: 𝔰 ≤ 𝔰 + (x)`: the single-output bound of Part (3)'s depth-1 case. -/
lemma LePad_prepend_single {r : ℕ} (x : ℕ+) (𝔰 : Fin r → ℕ+) :
    LePad (consVec x 𝔰) 𝔰 (single x) := by
  classical
  constructor
  · rw [weight_consVec, weight_single]
    omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        have hpre' := psumSeq_tupPadSum 𝔰 (single x) (n + 1)
        rw [hpre']
        rw [psum_single_of_pos x (by omega : 0 < n + 1)]
        have hmono : psum 𝔰 n ≤ psum 𝔰 (n + 1) := psum_mono 𝔰 (Nat.le_succ n)
        omega


/-- Part (3), second tuple of depth 1: `S_<d(s)·S_d(v) = S_d(v :: s)` (single output). -/
theorem p3_full_cons_depth1 (r : ℕ) (hr : 0 < r) (s1 t1 : ℕ+) (St : Fin r → ℕ+) :
    Nonempty (P3Data F (r + 1) 1 (by omega : 0 < r + 1) (by omega : 0 < 1)
      (consVec s1 St) (single t1)) := by
  classical
  let D : P3Data F (r + 1) 1 (by omega : 0 < r + 1) (by omega : 0 < 1)
      (consVec s1 St) (single t1) := {
    ι := PUnit.{1}
    fin := inferInstance
    dep := fun _ => r + 2
    hdep := by intro i; omega
    f := fun _ => (1 : ℤ)
    c := fun _ => consVec t1 (consVec s1 St)
    hid := by
      intro d
      calc
        S_lt F (r + 1) (by omega : 0 < r + 1) (consVec s1 St) d *
            S F 1 (by omega : 0 < 1) (single t1) d
            = S_lt F (r + 1) (by omega : 0 < r + 1) (consVec s1 St) d * P F d t1 := by
              rw [S_one_eq_P F d (by omega : 0 < 1) (single t1)]
              simp [single]
        _ = P F d t1 * S_lt F (r + 1) (by omega : 0 < r + 1) (consVec s1 St) d := by
              rw [mul_comm]
        _ = S F (r + 2) (by omega : 0 < r + 2) (consVec t1 (consVec s1 St)) d := by
              rw [S_prepend F d t1 (by omega : 0 < r + 1) (consVec s1 St)]
        _ = ∑ i : PUnit.{1}, ((1 : ℤ) : RatFunc.CompletionAtInfty F) *
              S F (r + 2) (by omega : 0 < r + 2) (consVec t1 (consVec s1 St)) d := by
              rw [show (Finset.univ : Finset PUnit.{1}) = {PUnit.unit} by
                ext i
                simp]
              simp
    hle := by
      intro i
      exact LePad_prepend_single t1 (consVec s1 St)
    hbd := by
      intro i
      omega }
  exact ⟨D⟩


/-- Part (3) cons case, second depth k+1 ≥ 2: `S_<d(a)·S_d(t1::T)` via the
`P2Full (r+1) k` witness on `(a, T)` with `t1` prepended per output. -/
theorem p3_full_cons (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (hP2 : P2Full F (r + 1) k) (s1 t1 : ℕ+) (St : Fin r → ℕ+) (T : Fin k → ℕ+) :
    Nonempty (P3Data F (r + 1) (k + 1) (by omega : 0 < r + 1) (by omega : 0 < k + 1)
      (consVec s1 St) (consVec t1 T)) := by
  classical
  let D2 : P2Data F (r + 1) k (by omega : 0 < r + 1) hk (consVec s1 St) T :=
    Classical.choice (hP2 (by omega : 0 < r + 1) hk (consVec s1 St) T)
  letI : Fintype D2.ι := D2.fin
  let ι0 : Type := D2.ι
  let dep0 : ι0 → ℕ := fun e => D2.dep e + 1
  let hdep0 : ∀ e : ι0, 0 < dep0 e := by
    intro e
    dsimp [dep0]
    have hp := D2.hdep e
    omega
  let f0 : ι0 → ℤ := fun e => D2.f e
  let c0 : ∀ e : ι0, Fin (dep0 e) → ℕ+ := fun e => consVec t1 (D2.c e)
  have hid0 : ∀ d : ℕ,
      S_lt F (r + 1) (by omega : 0 < r + 1) (consVec s1 St) d *
          S F (k + 1) (by omega : 0 < k + 1) (consVec t1 T) d =
      ∑ e : ι0, ((f0 e : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep0 e) (hdep0 e) (c0 e) d := by
    intro d
    let K := RatFunc.CompletionAtInfty F
    calc
      S_lt F (r + 1) (by omega : 0 < r + 1) (consVec s1 St) d *
          S F (k + 1) (by omega : 0 < k + 1) (consVec t1 T) d
          = S_lt F (r + 1) (by omega : 0 < r + 1) (consVec s1 St) d *
              (P F d t1 * S_lt F k hk T d) := by
            rw [S_cons_rec F hk t1 T d]
      _ = P F d t1 * (S_lt F (r + 1) (by omega : 0 < r + 1) (consVec s1 St) d * S_lt F k hk T d) := by
            ring
      _ = P F d t1 * (∑ e : D2.ι, ((D2.f e : ℤ) : K) *
              S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d) := by
            congr 1
            exact D2.hid d
      _ = ∑ e : D2.ι, ((D2.f e : ℤ) : K) *
              S F (D2.dep e + 1) (by omega) (consVec t1 (D2.c e)) d := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            calc
              P F d t1 * (((D2.f e : ℤ) : K) * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d)
                  = ((D2.f e : ℤ) : K) * (P F d t1 * S_lt F (D2.dep e) (D2.hdep e) (D2.c e) d) := by ring
              _ = ((D2.f e : ℤ) : K) * S F (D2.dep e + 1) (by omega) (consVec t1 (D2.c e)) d := by
                    rw [S_prepend F d t1 (D2.hdep e) (D2.c e)]
      _ = ∑ e : ι0, ((f0 e : ℤ) : RatFunc.CompletionAtInfty F) *
              S F (dep0 e) (hdep0 e) (c0 e) d := by
            apply Finset.sum_congr rfl
            intro e he
            simp [f0, dep0, c0, hdep0]
  have hle0 : ∀ e : ι0, LePad (c0 e) (consVec s1 St) (consVec t1 T) := by
    intro e
    simpa [c0, dep0] using LePad_cons_cons t1 (D2.c e) (consVec s1 St) T (D2.hle e)
  have hbd0 : ∀ e : ι0, dep0 e ≤ (r + 1) + (k + 1) := by
    intro e
    dsimp [dep0]
    have hb := D2.hbd e
    omega
  let D : P3Data F (r + 1) (k + 1) (by omega : 0 < r + 1) (by omega : 0 < k + 1)
      (consVec s1 St) (consVec t1 T) := {
    ι := ι0
    fin := inferInstance
    dep := dep0
    hdep := hdep0
    f := f0
    c := c0
    hid := hid0
    hle := hle0
    hbd := hbd0 }
  exact ⟨D⟩

end ZagierHoffmanPositiveChar
