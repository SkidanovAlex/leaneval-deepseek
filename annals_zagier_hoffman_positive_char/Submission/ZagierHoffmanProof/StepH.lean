import Submission.ZagierHoffmanProof.StepG

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step H: the mutual induction frame for `P1one`/`P2one`

The families close over all depths once the two CONS steps are available:
  P1c(k) : P2one k → the depth-(k+1) Part-1 product is a P1W carrier combo,
  P2c(k) : P1one k → P2one k → the depth-(k+1) Part-2 product is a P2W carrier combo.
This file proves the induction structure itself (base at depth 1, cons propagation) —
so once `P1c`/`P2c` are proved (the carrier work on top of p1cons_level/p2cons_level),
the full families follow mechanically.  Also: the head/tail decomposition of tuples.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Any depth-(m+1) tuple is `consVec` of its head and tail. -/
lemma fin_succ_eq_consVec {m : ℕ} (W' : Fin (m + 1) → ℕ+) :
    W' = consVec (W' ⟨0, by omega⟩) (fun j : Fin m => W' ⟨j.1 + 1, by omega⟩) := by
  funext i
  by_cases hi : (i : ℕ) = 0
  · have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi)
    rw [hi0]
    exact (consVec_zero (W' ⟨0, by omega⟩) (fun j : Fin m => W' ⟨j.1 + 1, by omega⟩)).symm
  · have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi
    have hiL : (i : ℕ) < m + 1 := i.2
    let j : Fin m := ⟨(i : ℕ) - 1, by omega⟩
    have hjm : (j.1 : ℕ) + 1 = i.1 := by dsimp [j]; omega
    have hi' : i = ⟨j.1 + 1, by omega⟩ := Fin.ext (by exact hjm.symm)
    rw [hi']
    have hc := consVec_succ (W' ⟨0, by omega⟩) (fun k : Fin m => W' ⟨k.1 + 1, by omega⟩) j
    rw [hc]

/-- The two cons hypotheses of the mutual induction. -/
def P1c (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), P2one F k hk →
    ∀ (v w1 : ℕ+) (W : Fin k → ℕ+),
      P1W F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1) (single v) (consVec w1 W)

def P2c (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), P1one F k hk → P2one F k hk →
    ∀ (v w1 : ℕ+) (W : Fin k → ℕ+),
      P2W F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1) (single v) (consVec w1 W)

/-- The mutual induction: base at depth 1, propagation by the cons hypotheses. -/
theorem p1p2_induction (h1c : P1c F) (h2c : P2c F) (n : ℕ) :
    P1one F (n + 1) (by omega : 0 < n + 1) ∧ P2one F (n + 1) (by omega : 0 < n + 1) := by
  classical
  induction n with
  | zero =>
    exact ⟨p1one_one F, p2one_one F⟩
  | succ n ih =>
    -- depth n+2; get P1one(n+2), P2one(n+2) from the depth-(n+1) family and the cons steps
    have h1 := h1c (n + 1) (by omega : 0 < n + 1) ih.2
    have h2 := h2c (n + 1) (by omega : 0 < n + 1) ih.1 ih.2
    constructor
    · intro v W'
      -- W' : Fin (n+2) = Fin ((n+1)+1)
      have hdec := fin_succ_eq_consVec (m := n + 1) W'
      rw [hdec]
      exact h1 v (W' ⟨0, by omega⟩) (fun j : Fin (n + 1) => W' ⟨j.1 + 1, by omega⟩)
    · intro v W'
      have hdec := fin_succ_eq_consVec (m := n + 1) W'
      rw [hdec]
      exact h2 v (W' ⟨0, by omega⟩) (fun j : Fin (n + 1) => W' ⟨j.1 + 1, by omega⟩)

/-- Both families hold at every positive depth, given the cons steps. -/
theorem p1p2_all (h1c : P1c F) (h2c : P2c F) : ∀ (k : ℕ) (hk : 0 < k),
    P1one F k hk ∧ P2one F k hk := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ n ih =>
    intro hk
    by_cases hn : n = 0
    · subst n
      exact ⟨p1one_one F, p2one_one F⟩
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hP1n := (ih (by omega : 0 < n)).1
      have hP2n := (ih (by omega : 0 < n)).2
      constructor
      · intro v W'
        have hdec := fin_succ_eq_consVec (m := n) W'
        rw [hdec]
        exact (h1c (n) (by omega : 0 < n) hP2n) v (W' ⟨0, by omega⟩)
          (fun j : Fin n => W' ⟨j.1 + 1, by omega⟩)
      · intro v W'
        have hdec := fin_succ_eq_consVec (m := n) W'
        rw [hdec]
        exact (h2c (n) (by omega : 0 < n) hP1n hP2n) v (W' ⟨0, by omega⟩)
          (fun j : Fin n => W' ⟨j.1 + 1, by omega⟩)

end ZagierHoffmanPositiveChar
