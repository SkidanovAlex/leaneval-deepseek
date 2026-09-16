import Submission.ZagierHoffmanProof.StepF

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step G: the mutual induction frame for the depth-1 family

The mutual statements (already in StepE):
  P1one k : ∀ v W (W of depth k), P1W F 1 k (single v) W
  P2one k : ∀ v W, P2W F 1 k (single v) W
with bases at k = 1 (p1one_one/p2one_one) and the cons cases at k = 2 (p1two/p2two,
family versions p1one_two/p2one_two).  This file records the base-family conjunction,
the tail/cons-recursion facts needed by the general cons step, and the general depth-k
cons LEVEL identities (products left intact; carriers assembled next).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Depth 1 and 2 base cases of both families. -/
theorem p1p2_bases :
    (P1one F 1 (by omega : 0 < 1) ∧ P2one F 1 (by omega : 0 < 1)) ∧
    (P1one F 2 (by omega : 0 < 2) ∧ P2one F 2 (by omega : 0 < 2)) := by
  exact ⟨⟨p1one_one F, p2one_one F⟩, ⟨p1one_two F, p2one_two F⟩⟩

/-- The tail of a prepended tuple is the original tuple. -/
lemma expTail_consVec {k : ℕ} (w1 : ℕ+) (W : Fin k → ℕ+) : expTail (consVec w1 W) = W := by
  funext j
  dsimp [expTail]
  change consVec w1 W ⟨j.1 + 1, by omega⟩ = W j
  have hc := consVec_succ w1 W ⟨j.1, by
    have hj : j.1 < k := j.2
    omega⟩
  -- ⟨j.1+1,…⟩ = ⟨j.1+1, …⟩ from consVec_succ
  simpa using hc

/-- Recursion for a prepended tuple at depth k+1: `S F (k+1)(w1::W) = P(w1)·S_lt W`. -/
lemma S_cons_rec {k : ℕ} (hk : 0 < k) (w1 : ℕ+) (W : Fin k → ℕ+) (d : ℕ) :
    S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
      P F d w1 * S_lt F k hk W d := by
  classical
  rw [S_d_recursion F (k + 1) (by omega : 1 < k + 1) (by omega : 0 < k + 1)
    (by omega : 0 < (k + 1) - 1) (consVec w1 W) d]
  have h0 : (consVec w1 W) ⟨0, by omega⟩ = w1 := by
    exact consVec_zero w1 W
  have ht : (fun j : Fin k => (consVec w1 W) ⟨j.1 + 1, by omega⟩) = W := by
    funext j
    have hc := consVec_succ w1 W ⟨j.1, j.2⟩
    simpa using hc
  rw [h0]
  change P F d w1 * S_lt F k hk (fun j : Fin k => (consVec w1 W) ⟨j.1 + 1, by omega⟩) d =
    P F d w1 * S_lt F k hk W d
  rw [ht]

/-- The general depth-k cons LEVEL identity for Part 1 (products left intact). -/
lemma p1cons_level {k : ℕ} (hk : 0 < k) (v w1 : ℕ+) (W : Fin k → ℕ+) (d : ℕ) :
    S F 1 (by omega : 0 < 1) (single v) d * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
      S F (k + 1) (by omega : 0 < k + 1)
        (consVec ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ W) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (w1 : ℕ) - 1)},
        (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d ⟨(v : ℕ) + (w1 : ℕ) - i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          have hin : i.1 ≤ (v : ℕ) + (w1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
          omega⟩ *
        (S_lt F 1 (by omega : 0 < 1) (single ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
          S_lt F k hk W d)) := by
  classical
  calc
    S F 1 (by omega : 0 < 1) (single v) d * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d
        = P F d v * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d := by
          rw [S_one_eq_P F d (by omega) (single v)]
          simp [single]
    _ = P F d v * (P F d w1 * S_lt F k hk W d) := by
          rw [S_cons_rec F hk w1 W d]
    _ = (P F d v * P F d w1) * S_lt F k hk W d := by
          rw [mul_assoc]
    _ = (P F d ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (w1 : ℕ) - 1)},
            (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            S F 2 (by omega : 0 < 2) (thakurExp (v : ℕ) (w1 : ℕ) i) d) *
        S_lt F k hk W d := by
          rw [diag_level F d v w1]
    _ = P F d ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ * S_lt F k hk W d +
        (∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (w1 : ℕ) - 1)},
          (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega : 0 < 2) (thakurExp (v : ℕ) (w1 : ℕ) i) d) *
        S_lt F k hk W d := by
          rw [add_mul]
    _ = S F (k + 1) (by omega : 0 < k + 1)
          (consVec ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ W) d +
        (∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (w1 : ℕ) - 1)},
          (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega : 0 < 2) (thakurExp (v : ℕ) (w1 : ℕ) i) d) *
        S_lt F k hk W d := by
          rw [S_prepend F d ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ hk W]
    _ = S F (k + 1) (by omega : 0 < k + 1)
          (consVec ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ W) d +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (w1 : ℕ) - 1)},
          (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          (S F 2 (by omega : 0 < 2) (thakurExp (v : ℕ) (w1 : ℕ) i) d *
            S_lt F k hk W d) := by
          rw [Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_assoc]
    _ = S F (k + 1) (by omega : 0 < k + 1)
          (consVec ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ W) d +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (w1 : ℕ) - 1)},
          (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          (P F d ⟨(v : ℕ) + (w1 : ℕ) - i.1, by
              have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
              have hin : i.1 ≤ (v : ℕ) + (w1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
              omega⟩ *
            (S_lt F 1 (by omega : 0 < 1) (single ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
              S_lt F k hk W d)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          calc
            S F 2 (by omega : 0 < 2) (thakurExp (v : ℕ) (w1 : ℕ) i) d * S_lt F k hk W d
                = (P F d ⟨(v : ℕ) + (w1 : ℕ) - i.1, by
                      have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
                      have hin : i.1 ≤ (v : ℕ) + (w1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
                      omega⟩ *
                    S_lt F 1 (by omega : 0 < 1) (single ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d) *
                    S_lt F k hk W d := by
                      rw [thakur_S_two_eq F d (v : ℕ) (w1 : ℕ) i]
                      rw [show (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) =
                          single ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩ by rfl]
                _ = P F d ⟨(v : ℕ) + (w1 : ℕ) - i.1, by
                      have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
                      have hin : i.1 ≤ (v : ℕ) + (w1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
                      omega⟩ *
                      (S_lt F 1 (by omega : 0 < 1) (single ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
                        S_lt F k hk W d) := by
                      rw [mul_assoc]

/-- The general depth-k Part-2 cons LEVEL identity (paper (2.4)) with tails, products intact:
`S_<d(v)·S_<d(w1::W) = S_<d(v,w1,W) + Σ_i S_i(w1)·(S_<i(v)·S_<i(W)) + Σ_i S_i(v)·S_i(w1::W)`. -/
lemma p2cons_level {k : ℕ} (hk : 0 < k) (v w1 : ℕ+) (W : Fin k → ℕ+) (d : ℕ) :
    S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
      S_lt F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) d +
      (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single w1) i *
          (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i)) +
      (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single v) i *
          S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) i) := by
  classical
  let A : ℕ → RatFunc.CompletionAtInfty F := fun i => S F 1 (by omega : 0 < 1) (single v) i
  let B : ℕ → RatFunc.CompletionAtInfty F := fun j => S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) j
  have h1 : (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, A ℓ * B m) =
      S_lt F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) d := by
    calc
      (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, A ℓ * B m)
          = ∑ ℓ ∈ Finset.range d, A ℓ * (∑ m ∈ Finset.range ℓ, B m) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            exact (Finset.mul_sum (s := Finset.range ℓ) (a := A ℓ) (f := B)).symm
      _ = ∑ ℓ ∈ Finset.range d, S F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) ℓ := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            calc
              A ℓ * (∑ m ∈ Finset.range ℓ, B m)
                  = A ℓ * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) ℓ := by
                    rw [← S_lt_eq_sum_levels F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) ℓ]
              _ = S F 1 (by omega : 0 < 1) (single v) ℓ * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) ℓ := by
                    rfl
              _ = S F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) ℓ := by
                    -- S F1 (single v) ℓ = P ℓ v, then S_prepend at level ℓ
                    have hP : S F 1 (by omega : 0 < 1) (single v) ℓ = P F ℓ v := by
                      rw [S_one_eq_P F ℓ (by omega) (single v)]
                      simp [single]
                    rw [hP]
                    rw [S_prepend F ℓ v (by omega : 0 < k + 1) (consVec w1 W)]
      _ = S_lt F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) d := by
            exact (S_lt_eq_sum_levels F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) d).symm
  have h2 : (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, A ℓ * B m) =
      (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single w1) i *
          (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i)) := by
    calc
      (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, A ℓ * B m)
          = ∑ m ∈ Finset.range d, (∑ ℓ ∈ Finset.range m, A ℓ) * B m := by
            apply Finset.sum_congr rfl
            intro m hm
            exact (Finset.sum_mul (s := Finset.range m) (f := A) (a := B m)).symm
      _ = ∑ m ∈ Finset.range d, (S_lt F 1 (by omega : 0 < 1) (single v) m) * B m := by
            apply Finset.sum_congr rfl
            intro m hm
            congr 1
            simpa [A] using (S_lt_eq_sum_levels F 1 (by omega : 0 < 1) (single v) m).symm
      _ = ∑ i ∈ Finset.range d, S F 1 (by omega : 0 < 1) (single w1) i *
            (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i) := by
            apply Finset.sum_congr rfl
            intro m hm
            calc
              S_lt F 1 (by omega : 0 < 1) (single v) m * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) m
                  = S_lt F 1 (by omega : 0 < 1) (single v) m *
                      (P F m w1 * S_lt F k hk W m) := by
                    rw [S_cons_rec F hk w1 W m]
              _ = P F m w1 * (S_lt F 1 (by omega : 0 < 1) (single v) m * S_lt F k hk W m) := by
                    ring
              _ = S F 1 (by omega : 0 < 1) (single w1) m *
                    (S_lt F 1 (by omega : 0 < 1) (single v) m * S_lt F k hk W m) := by
                    rw [S_one_eq_P F m (by omega) (single w1)]
                    simp [single]
  calc
    S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d
        = (∑ i ∈ Finset.range d, A i) * (∑ j ∈ Finset.range d, B j) := by
          rw [S_lt_eq_sum_levels F 1 (by omega : 0 < 1) (single v) d]
          rw [S_lt_eq_sum_levels F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d]
    _ = (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, A ℓ * B m) +
        (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, A ℓ * B m) +
        (∑ ℓ ∈ Finset.range d, A ℓ * B ℓ) := by
          exact Commons.Data.Finset.sum_range_mul_split (R := RatFunc.CompletionAtInfty F) d A B
    _ = S_lt F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) d +
        (∑ i ∈ Finset.range d, S F 1 (by omega : 0 < 1) (single w1) i *
          (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i)) +
        (∑ ℓ ∈ Finset.range d, A ℓ * B ℓ) := by
          rw [h1, h2]
    _ = S_lt F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) d +
        (∑ i ∈ Finset.range d, S F 1 (by omega : 0 < 1) (single w1) i *
          (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i)) +
        (∑ i ∈ Finset.range d, S F 1 (by omega : 0 < 1) (single v) i *
          S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) i) := by
          apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
            S_lt F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) d +
            (∑ i ∈ Finset.range d, S F 1 (by omega : 0 < 1) (single w1) i *
              (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i)) + t)
          -- third group is the diagonal: A ℓ · B ℓ
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          rfl

end ZagierHoffmanPositiveChar
