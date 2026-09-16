import Submission.ZagierHoffmanProof.StepB7

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step B8: singleton × depth-k shuffle (first merge, paper (2.2) for depth-1 × depth-k)

`S_mul_P_first`: `P F d v * S F k 𝔱 d` merges `v` into slot 0 (all depths `k ≥ 2`),
leaving the depth-one `S_lt [i]` and the depth-`k-1` `S_lt` tail intact in the Δ-terms.
This is the general version of `StepB7.S_two_mul_P_first` (the `k = 2` case).
-/

namespace ZagierHoffmanPositiveChar
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- General first merge: `P F d v * S F k hr0 𝔱 d` for depth `k ≥ 2`; merges `v` into
slot 0 (paper (2.2) for a depth-1 × depth-k product), leaving the depth-one `S_lt [i]`
and the depth-`k-1` `S_lt` tail intact. -/
lemma S_mul_P_first (d : ℕ) (hd : 1 ≤ d) {k : ℕ} (hk : 1 < k) (hr0 : 0 < k) (v : ℕ+)
    (𝔱 : Fin k → ℕ+) :
    P F d v * S F k hr0 𝔱 d =
      S F k hr0 (headAdd v hr0 𝔱) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - 1)},
        (ChenDeltaZ F (v : ℕ) (𝔱 ⟨0, hr0⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - i.1, by
            have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
            have hin : i.1 ≤ (v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
            omega⟩ *
          S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
          S_lt F (k - 1) (by omega : 0 < k - 1)
            (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d) := by
  classical
  have hrec : S F k hr0 𝔱 d = P F d (𝔱 ⟨0, hr0⟩) *
      S_lt F (k - 1) (by omega : 0 < k - 1) (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d := by
    rw [S_d_recursion F k hk hr0 (by omega : 0 < k - 1) 𝔱 d]
  have hrecM : S F k hr0 (headAdd v hr0 𝔱) d =
      P F d ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ), Nat.add_pos_left (PNat.pos v) (𝔱 ⟨0, hr0⟩ : ℕ)⟩ *
      S_lt F (k - 1) (by omega : 0 < k - 1) (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d := by
    calc
      S F k hr0 (headAdd v hr0 𝔱) d
          = P F d ((headAdd v hr0 𝔱) ⟨0, hr0⟩) *
            S_lt F (k - 1) (by omega : 0 < k - 1)
              (fun j : Fin (k - 1) => (headAdd v hr0 𝔱) ⟨j.1 + 1, by omega⟩) d := by
            exact (S_d_recursion F k hk hr0 (by omega : 0 < k - 1) (headAdd v hr0 𝔱) d)
      _ = P F d ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ), Nat.add_pos_left (PNat.pos v) (𝔱 ⟨0, hr0⟩ : ℕ)⟩ *
            S_lt F (k - 1) (by omega : 0 < k - 1)
              (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d := by
            have hhead : (headAdd v hr0 𝔱) ⟨0, hr0⟩ =
                ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ), Nat.add_pos_left (PNat.pos v) (𝔱 ⟨0, hr0⟩ : ℕ)⟩ := by
              dsimp [headAdd]
            have htail : (fun j : Fin (k - 1) => (headAdd v hr0 𝔱) ⟨j.1 + 1, by omega⟩) =
                (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) := by
              funext j
              dsimp [headAdd]
            rw [hhead, htail]
  calc
    P F d v * S F k hr0 𝔱 d
        = P F d v * (P F d (𝔱 ⟨0, hr0⟩) *
            S_lt F (k - 1) (by omega : 0 < k - 1) (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d) := by
          rw [hrec]
    _ = (P F d v * P F d (𝔱 ⟨0, hr0⟩)) *
          S_lt F (k - 1) (by omega : 0 < k - 1) (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d := by
          ring
    _ = (P F d ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ), Nat.add_pos_left (PNat.pos v) (𝔱 ⟨0, hr0⟩ : ℕ)⟩ +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - 1)},
            (ChenDeltaZ F (v : ℕ) (𝔱 ⟨0, hr0⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            S F 2 (by omega) (thakurExp (v : ℕ) (𝔱 ⟨0, hr0⟩ : ℕ) i) d) *
          S_lt F (k - 1) (by omega : 0 < k - 1) (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d := by
          rw [← thakur_prod_one F d hd v (𝔱 ⟨0, hr0⟩)]
    _ = S F k hr0 (headAdd v hr0 𝔱) d +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - 1)},
            (ChenDeltaZ F (v : ℕ) (𝔱 ⟨0, hr0⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            (P F d ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - i.1, by
                have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
                have hin : i.1 ≤ (v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
                omega⟩ *
              S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
              S_lt F (k - 1) (by omega : 0 < k - 1)
                (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d) := by
          rw [add_mul]
          rw [Finset.sum_mul]
          rw [← hrecM]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [thakur_S_two_eq F d (v : ℕ) (𝔱 ⟨0, hr0⟩ : ℕ) i]
          ring
    _ = S F k hr0 (headAdd v hr0 𝔱) d +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - 1)},
            (ChenDeltaZ F (v : ℕ) (𝔱 ⟨0, hr0⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            (P F d ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - i.1, by
                have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
                have hin : i.1 ≤ (v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
                omega⟩ *
              S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
              S_lt F (k - 1) (by omega : 0 < k - 1)
                (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d) := by
          rfl
/-- Prepend a singleton exponent `x` to a length-`m` exponent vector. -/
noncomputable def consVec (x : ℕ+) {m : ℕ} (𝔰 : Fin m → ℕ+) : Fin (m + 1) → ℕ+ :=
  Fin.cons x 𝔰

lemma consVec_zero (x : ℕ+) {m : ℕ} (𝔰 : Fin m → ℕ+) :
    consVec x 𝔰 ⟨0, (by omega : 0 < m + 1)⟩ = x := by
  dsimp [consVec]
  exact Fin.cons_zero (α := fun _ : Fin (m + 1) => ℕ+) x 𝔰

lemma consVec_succ (x : ℕ+) {m : ℕ} (𝔰 : Fin m → ℕ+) (j : Fin m) :
    consVec x 𝔰 ⟨j.1 + 1, (by omega : j.1 + 1 < m + 1)⟩ = 𝔰 j := by
  dsimp [consVec]
  exact Fin.cons_succ (α := fun _ : Fin (m + 1) => ℕ+) x 𝔰 j

/-- The reverse of the level-`d` recursion: `P_d(x) · S_<d(𝔰) = S_{d}(x :: 𝔰)` at depth `m+1`. -/
lemma S_prepend (d : ℕ) (x : ℕ+) {m : ℕ} (hm : 0 < m) (𝔰 : Fin m → ℕ+) :
    P F d x * S_lt F m hm 𝔰 d = S F (m + 1) (by omega : 0 < m + 1) (consVec x 𝔰) d := by
  classical
  have hhead : consVec x 𝔰 ⟨0, (by omega : 0 < m + 1)⟩ = x := consVec_zero x 𝔰
  have htail : (fun j : Fin m => consVec x 𝔰 ⟨j.1 + 1, (by omega : j.1 + 1 < m + 1)⟩) = 𝔰 := by
    funext j
    exact consVec_succ x 𝔰 j
  calc
    P F d x * S_lt F m hm 𝔰 d
        = P F d (consVec x 𝔰 ⟨0, (by omega : 0 < m + 1)⟩) *
            S_lt F m hm (fun j : Fin m => consVec x 𝔰 ⟨j.1 + 1, (by omega : j.1 + 1 < m + 1)⟩) d := by
          rw [hhead]
          rw [htail]
    _ = S F (m + 1) (by omega : 0 < m + 1) (consVec x 𝔰) d := by
          exact (S_d_recursion F (m + 1) (by omega : 1 < m + 1) (by omega : 0 < m + 1) hm
            (consVec x 𝔰) d).symm
/-- The depth-(1,2) shuffle with the depth-1×depth-1 `S_<d` stuffle fully expanded:
`P_d(v)·S_d(t1,t2)` becomes `S_d(v+t1,t2)` plus, for each `0<i<v+t1`,
`Δ^i_{v,t1}·P_d(v+t1-i)` times the depth-1 stuffle of `(i)` and `(t2)`. -/
lemma S_two_mul_P_stuffle (d : ℕ) (hd : 1 ≤ d) (v t1 t2 : ℕ+) :
    P F d v * S F 2 (by omega : 0 < 2) (fun j : Fin 2 => if (j : ℕ) = 0 then t1 else t2) d =
      S F 2 (by omega : 0 < 2) (fun j : Fin 2 =>
        if (j : ℕ) = 0 then
          ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ else t2) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (t1 : ℕ) - 1)},
        (ChenDeltaZ F (v : ℕ) (t1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        P F d ⟨(v : ℕ) + (t1 : ℕ) - i.1, by
            have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
            have hin : i.1 ≤ (v : ℕ) + (t1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
            omega⟩ *
        (S_lt F 2 (by omega : 0 < 2) (fun j : Fin 2 =>
            if (j : ℕ) = 0 then ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩ else t2) d +
         S_lt F 2 (by omega : 0 < 2) (fun j : Fin 2 =>
            if (j : ℕ) = 0 then t2 else ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d +
         S_lt F 1 (by omega : 0 < 1) (fun _ : Fin 1 =>
            ⟨i.1 + (t2 : ℕ), Nat.add_pos_left (Finset.mem_Icc.mp i.2).1 (t2 : ℕ)⟩) d +
         ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (i.1 + (t2 : ℕ) - 1)},
           (ChenDeltaZ F i.1 (t2 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
           S_lt F 2 (by omega : 0 < 2) (thakurExp i.1 (t2 : ℕ) j) d) := by
  classical
  rw [S_two_mul_P_first F d hd v t1 t2]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
  have hst := S_lt_one_stuffle F d ⟨i.1, hi1⟩ t2
  rw [mul_assoc]
  rw [hst]
  rw [← mul_assoc]
  rfl
end ZagierHoffmanPositiveChar
