import Submission.ZagierHoffmanProof.StepJ

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step K: the full (r,k) Prop 2.1 — statement and anchor layer

`P1Full r k` / `P2Full r k` are the ALL-depths Prop 2.1 statements (paper Prop 2.1(1)/(2)
= 2022 arXiv 2205.07165 Prop 1.2(1)/(2)): for every tuple pair of depths (r,k),
`S_d(a)·S_d(b)` (resp. `S_<d(a)·S_<d(b)`) is an F-combination of level-`d` blocks of
tuples `u ≤ a+b` with depth ≤ r+k, witnessed by `P1Data`/`P2Data`.

This file records the statements, the Data-level symmetric instances `p1oneD_sym`/
`p2oneD_sym`, and the ANCHOR: all families with `min(r,k) = 1` (r = 1 via the
depth-1-left family `p1p2D_all`, k = 1 via the symmetric Data instances).  The
`r,k ≥ 2` cons content (Part 1 from `P2Full(r−1,k−1)` + the depth-1-left family for
the nested Δ-parts; Part 2 from `P2Full(r−1,k)`, `P2Full(r,k−1)` and `P1Full(r,k)`)
is the next milestone (StepK2+).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Part 1 of Prop 2.1 at depths (r,k): all products `S_d(a)·S_d(b)`. -/
def P1Full (r k : ℕ) : Prop :=
  ∀ (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+),
    Nonempty (P1Data F r k hr hk a b)

/-- Part 2 of Prop 2.1 at depths (r,k): all products `S_<d(a)·S_<d(b)`. -/
def P2Full (r k : ℕ) : Prop :=
  ∀ (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+),
    Nonempty (P2Data F r k hr hk a b)

/-- Data-level symmetric Part-1 family (depth `k` on the left, singleton on the right). -/
theorem p1oneD_sym {k : ℕ} (hk : 0 < k) (h : P1oneD F k hk) :
    ∀ (W : Fin k → ℕ+) (v : ℕ+),
      Nonempty (P1Data F k 1 hk (by omega : 0 < 1) W (single v)) := by
  classical
  intro W v
  rcases h v W with ⟨D⟩
  letI : Fintype D.ι := D.fin
  let D' : P1Data F k 1 hk (by omega : 0 < 1) W (single v) := {
    ι := D.ι
    fin := D.fin
    dep := D.dep
    hdep := D.hdep
    f := D.f
    c := D.c
    hid := by
      intro d
      calc
        S F k hk W d * S F 1 (by omega : 0 < 1) (single v) d
            = S F 1 (by omega : 0 < 1) (single v) d * S F k hk W d := by rw [mul_comm]
        _ = ∑ i : D.ι, ((D.f i : ℤ) : RatFunc.CompletionAtInfty F) *
              S F (D.dep i) (D.hdep i) (D.c i) d := D.hid d
    hle := by
      intro i
      exact (LePad_swap (D.c i) (single v) W).mp (D.hle i)
    hbd := by
      intro i
      have hb := D.hbd i
      omega }
  exact ⟨D'⟩

/-- Data-level symmetric Part-2 family (depth `k` on the left, singleton on the right). -/
theorem p2oneD_sym {k : ℕ} (hk : 0 < k) (h : P2oneD F k hk) :
    ∀ (W : Fin k → ℕ+) (v : ℕ+),
      Nonempty (P2Data F k 1 hk (by omega : 0 < 1) W (single v)) := by
  classical
  intro W v
  rcases h v W with ⟨D⟩
  letI : Fintype D.ι := D.fin
  let D' : P2Data F k 1 hk (by omega : 0 < 1) W (single v) := {
    ι := D.ι
    fin := D.fin
    dep := D.dep
    hdep := D.hdep
    f := D.f
    c := D.c
    hid := by
      intro d
      calc
        S_lt F k hk W d * S_lt F 1 (by omega : 0 < 1) (single v) d
            = S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F k hk W d := by rw [mul_comm]
        _ = ∑ i : D.ι, ((D.f i : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep i) (D.hdep i) (D.c i) d := D.hid d
    hle := by
      intro i
      exact (LePad_swap (D.c i) (single v) W).mp (D.hle i)
    hbd := by
      intro i
      have hb := D.hbd i
      omega }
  exact ⟨D'⟩

/-- Anchor: first depth 1 — both parts at every second depth (from `p1p2D_all`). -/
theorem p1p2_full_left_one (k : ℕ) (hk : 0 < k) : P1Full F 1 k ∧ P2Full F 1 k := by
  classical
  constructor
  · intro hr hk' a b
    have h := (p1p2D_all F k hk').1
    rw [fin1_eq_single a]
    exact h (a ⟨0, by omega⟩) b
  · intro hr hk' a b
    have h := (p1p2D_all F k hk').2
    rw [fin1_eq_single a]
    exact h (a ⟨0, by omega⟩) b

/-- Anchor: second depth 1 — both parts at every first depth (symmetric instances). -/
theorem p1p2_full_right_one (r : ℕ) (hr : 0 < r) : P1Full F r 1 ∧ P2Full F r 1 := by
  classical
  constructor
  · intro hr' hk a b
    have h := (p1p2D_all F r hr').1
    rw [fin1_eq_single b]
    exact p1oneD_sym F hr' h a (b ⟨0, by omega⟩)
  · intro hr' hk a b
    have h := (p1p2D_all F r hr').2
    rw [fin1_eq_single b]
    exact p2oneD_sym F hr' h a (b ⟨0, by omega⟩)

/-- Anchor: both families at every depth pair with `min(r,k) = 1`. -/
theorem p1p2_full_anchor (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    r = 1 ∨ k = 1 → P1Full F r k ∧ P2Full F r k := by
  intro h
  rcases h with h1 | h1
  · subst r
    exact p1p2_full_left_one F k hk
  · subst k
    exact p1p2_full_right_one F r hr

end ZagierHoffmanPositiveChar
