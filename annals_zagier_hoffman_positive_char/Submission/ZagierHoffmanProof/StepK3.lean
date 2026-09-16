import Submission.ZagierHoffmanProof.StepK2

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step K3: full depth coverage of Prop 2.1 Part (3) (paper (2.7) family)

`P3Full r k` (defined in StepK2): every mixed product `S_<d(a)·S_d(b)` (a of depth r,
b of depth k) is an F-combination of level-`d` blocks `S_d(c_i)` with `c_i ≤ a+b` and
depth `≤ r+k`.

StepK2 established two cons pieces:
  - `p3_full_cons_depth1`: second depth = 1, first depth = r+1 ≥ 2
    (`S_<d(s1::St)·S_d(t1) = S_d(t1::s1::St)`, single output);
  - `p3_full_cons`: both depths ≥ 2, from `P2Full (r+1) k`.
This file adds the two missing corners — the (1,1) base `p3Data_one_one` and the
first-depth-1 cons step `p3_full_cons_left1` (second depth k+1 ≥ 2, from
`P2Full 1 k`) — and assembles the full family `p3_full_all`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `x :: (y)` as depth-two tuple equals `(x, y)`. -/
lemma consVec_single_eq_pair (x y : ℕ+) : consVec x (single y) = pair x y := by
  funext j
  fin_cases j
  · dsimp [consVec, single, pair]
    rfl
  · dsimp [consVec, single, pair]
    rfl

/-- Base of Part (3), depths (1,1): `S_<d(s)·S_d(t) = S_d(t,s)` (single output). -/
theorem p3Data_one_one (s1 t1 : ℕ+) :
    Nonempty (P3Data F 1 1 (by omega : 0 < 1) (by omega : 0 < 1) (single s1) (single t1)) := by
  classical
  let D : P3Data F 1 1 (by omega : 0 < 1) (by omega : 0 < 1) (single s1) (single t1) := {
    ι := PUnit.{1}
    fin := inferInstance
    dep := fun _ => 2
    hdep := by intro i; omega
    f := fun _ => (1 : ℤ)
    c := fun _ => pair t1 s1
    hid := by
      intro d
      calc
        S_lt F 1 (by omega : 0 < 1) (single s1) d * S F 1 (by omega : 0 < 1) (single t1) d
            = S_lt F 1 (by omega : 0 < 1) (single s1) d * P F d t1 := by
              rw [S_one_eq_P F d (by omega : 0 < 1) (single t1)]
              simp [single]
        _ = P F d t1 * S_lt F 1 (by omega : 0 < 1) (single s1) d := by
              rw [mul_comm]
        _ = S F 2 (by omega : 0 < 2) (pair t1 s1) d := by
              rw [S_prepend F d t1 (by omega : 0 < 1) (single s1)]
              rw [consVec_single_eq_pair]
        _ = ∑ i : PUnit.{1}, ((1 : ℤ) : RatFunc.CompletionAtInfty F) *
              S F 2 (by omega : 0 < 2) (pair t1 s1) d := by
              rw [show (Finset.univ : Finset PUnit.{1}) = {PUnit.unit} by
                ext i
                simp]
              simp
    hle := by
      intro i
      exact LePad_pair_swap_of_sum s1 t1
    hbd := by
      intro i
      omega }
  exact ⟨D⟩

/-- Part (3) cons case, first depth 1, second depth k+1 ≥ 2: `S_<d(s)·S_d(t1::T)` via the
`P2Full 1 k` witness on `((s), T)` with `t1` prepended per output. -/
theorem p3_full_cons_left1 (k : ℕ) (hk : 0 < k)
    (hP2 : P2Full F 1 k) (s1 t1 : ℕ+) (T : Fin k → ℕ+) :
    Nonempty (P3Data F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1)
      (single s1) (consVec t1 T)) := by
  classical
  let D2 : P2Data F 1 k (by omega : 0 < 1) hk (single s1) T :=
    Classical.choice (hP2 (by omega : 0 < 1) hk (single s1) T)
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
      S_lt F 1 (by omega : 0 < 1) (single s1) d *
          S F (k + 1) (by omega : 0 < k + 1) (consVec t1 T) d =
      ∑ e : ι0, ((f0 e : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep0 e) (hdep0 e) (c0 e) d := by
    intro d
    let K := RatFunc.CompletionAtInfty F
    calc
      S_lt F 1 (by omega : 0 < 1) (single s1) d *
          S F (k + 1) (by omega : 0 < k + 1) (consVec t1 T) d
          = S_lt F 1 (by omega : 0 < 1) (single s1) d *
              (P F d t1 * S_lt F k hk T d) := by
            rw [S_cons_rec F hk t1 T d]
      _ = P F d t1 * (S_lt F 1 (by omega : 0 < 1) (single s1) d * S_lt F k hk T d) := by
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
            simp [f0, dep0, c0]
  have hle0 : ∀ e : ι0, LePad (c0 e) (single s1) (consVec t1 T) := by
    intro e
    simpa [c0, dep0] using LePad_cons_cons t1 (D2.c e) (single s1) T (D2.hle e)
  have hbd0 : ∀ e : ι0, dep0 e ≤ 1 + (k + 1) := by
    intro e
    dsimp [dep0]
    have hb := D2.hbd e
    omega
  let D : P3Data F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1)
      (single s1) (consVec t1 T) := {
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

/-- Part (3) at every first depth with second depth 1. -/
theorem p3_full_right_one (r : ℕ) (hr : 0 < r) : P3Full F r 1 := by
  classical
  induction r with
  | zero => intro h; omega
  | succ m ih =>
    intro hr
    by_cases hm : m = 0
    · subst m
      intro hk1 a b
      have hdecA := fin1_eq_single a
      have hdecB := fin1_eq_single b
      rw [hdecA, hdecB]
      exact p3Data_one_one F (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      intro hk1 a b
      have hdecA := fin_succ_eq_consVec (m := m) a
      have hdecB := fin1_eq_single b
      rw [hdecA, hdecB]
      exact p3_full_cons_depth1 F m hmpos (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)
        (fun j : Fin m => a ⟨j.1 + 1, by omega⟩)

/-- ★ Full Prop 2.1 Part (3) (paper (2.7)): the mixed family at every depth pair. -/
theorem p3_full_all : ∀ (k : ℕ) (hk : 0 < k), ∀ (r : ℕ) (hr : 0 < r), P3Full F r k := by
  classical
  intro k
  induction k with
  | zero => intro hk; omega
  | succ n ih =>
    intro hk
    by_cases hn : n = 0
    · subst n
      intro r hr
      exact p3_full_right_one F r hr
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      intro r
      induction r with
      | zero => intro hr; omega
      | succ m ih2 =>
        intro hr
        by_cases hm : m = 0
        · subst m
          have hP2 : P2Full F 1 n :=
            (p1p2_full_all F n hnpos 1 (by omega : 0 < 1)).2
          intro hr1 hk1 a b
          have hdecA := fin1_eq_single a
          have hdecB := fin_succ_eq_consVec (m := n) b
          rw [hdecA, hdecB]
          exact p3_full_cons_left1 F n hnpos hP2 (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)
            (fun j : Fin n => b ⟨j.1 + 1, by omega⟩)
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
          have hP2 : P2Full F (m + 1) n :=
            (p1p2_full_all F n hnpos (m + 1) (by omega : 0 < m + 1)).2
          intro hr1 hk1 a b
          have hdecA := fin_succ_eq_consVec (m := m) a
          have hdecB := fin_succ_eq_consVec (m := n) b
          rw [hdecA, hdecB]
          exact p3_full_cons F m n hmpos hnpos hP2 (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)
            (fun j : Fin m => a ⟨j.1 + 1, by omega⟩)
            (fun j : Fin n => b ⟨j.1 + 1, by omega⟩)

end ZagierHoffmanPositiveChar
