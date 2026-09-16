import Submission.ZagierHoffmanProof.StepE
import Submission.Commons.Data.Finset.sum_range_mul_split

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step F: Part 2 cons case at depth (1,2) — the (2.4)-level machinery

`S_<d(v)·S_<d(w1,w2) = G1 + G2 + G3` with (paper (2.4), a = (v) depth 1, b = (w1,w2)):
  G1 = S_<d(v,w1,w2)                     (first group: v above both entries)
  G2 = Σ_t p2F·S_<d(w1 :: c_t) over t : P2Idx v w2   (second group)
  G3 = Σ_a p1twoF·S_<d(c_a) over a : p1twoIdx v w1 w2 (diagonal, Part 1 at all levels)
This file proves the level-sum pieces: p1two_carrier_id (Part 1 at each level, concrete),
g1eq, g3eq; g2eq and the assembled p2two_level / carrier P2W(1,2) follow.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Part 1 depth (1,2): the carrier sum equals the product at every level `i`
(concrete witness from StepE; no ∃ needed). -/
lemma p1two_carrier_id (v w1 w2 : ℕ+) (i : ℕ) :
    (∑ a : p1twoIdx v w1 w2,
      ((p1twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
      S F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a) (p1twoC v w1 w2 a) i) =
    S F 1 (by omega : 0 < 1) (single v) i * S F 2 (by omega : 0 < 2) (pair w1 w2) i := by
  classical
  exact (p1two_rhs_eq F v w1 w2 i).trans (p1two_level_wit F v w1 w2 i).symm

/-- G1: `Σ_{i<d} S_i(v)·S_<i(W) = S_<d(v,W)` (level sums of the pure merge). -/
lemma g1eq (v w1 w2 : ℕ+) (d : ℕ) :
    (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single v) i *
          (∑ j ∈ Finset.range i, S F 2 (by omega : 0 < 2) (pair w1 w2) j)) =
    S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d := by
  classical
  calc
    (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single v) i *
          (∑ j ∈ Finset.range i, S F 2 (by omega : 0 < 2) (pair w1 w2) j))
        = ∑ i ∈ Finset.range d,
            S F 1 (by omega : 0 < 1) (single v) i * S_lt F 2 (by omega : 0 < 2) (pair w1 w2) i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← S_lt_eq_sum_levels F 2 (by omega : 0 < 2) (pair w1 w2) i]
    _ = ∑ i ∈ Finset.range d, S F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) i := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            S F 1 (by omega : 0 < 1) (single v) i * S_lt F 2 (by omega : 0 < 2) (pair w1 w2) i
                = P F i v * S_lt F 2 (by omega : 0 < 2) (pair w1 w2) i := by
                  rw [S_one_eq_P F i (by omega) (single v)]
                  simp [single]
            _ = S F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) i := by
                  exact S_prepend F i v (by omega : 0 < 2) (pair w1 w2)
    _ = S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d := by
          exact (S_lt_eq_sum_levels F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d).symm

/-- G3: the diagonal `Σ_i S_i(v)·S_i(W)` equals Part 1's combo in `S_<d` form. -/
lemma g3eq (v w1 w2 : ℕ+) (d : ℕ) :
    (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single v) i * S F 2 (by omega : 0 < 2) (pair w1 w2) i) =
    ∑ a : p1twoIdx v w1 w2,
      ((p1twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a) (p1twoC v w1 w2 a) d := by
  classical
  calc
    (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single v) i * S F 2 (by omega : 0 < 2) (pair w1 w2) i)
        = (∑ i ∈ Finset.range d,
            ∑ a : p1twoIdx v w1 w2,
              ((p1twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
              S F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a) (p1twoC v w1 w2 a) i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (p1two_carrier_id F v w1 w2 i).symm
    _ = ∑ a : p1twoIdx v w1 w2,
          ((p1twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
          (∑ i ∈ Finset.range d,
            S F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a) (p1twoC v w1 w2 a) i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          exact (Finset.mul_sum (s := Finset.range d)
            (a := ((p1twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F))
            (f := fun i : ℕ => S F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a)
              (p1twoC v w1 w2 a) i)).symm
    _ = ∑ a : p1twoIdx v w1 w2,
          ((p1twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
          S_lt F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a) (p1twoC v w1 w2 a) d := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← S_lt_eq_sum_levels F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a)
            (p1twoC v w1 w2 a) d]

/-- Depth-two recursion with pair: `S F 2 (w1,w2) m = P F m w1 · S_lt F 1 (w2) m`. -/
lemma S_two_pair_rec (w1 w2 : ℕ+) (m : ℕ) :
    S F 2 (by omega : 0 < 2) (pair w1 w2) m = P F m w1 * S_lt F 1 (by omega : 0 < 1) (single w2) m := by
  classical
  rw [S_d_recursion F 2 (by omega : 1 < 2) (by omega : 0 < 2) (by omega : 0 < 1) (pair w1 w2) m]
  congr 1

/-- G2: `Σ_{m<d} S_m(W)·S_<m(v) = Σ_t p2F·S_<d(w1 :: c_t)` over the (v,w2) stuffle. -/
lemma g2eq (v w1 w2 : ℕ+) (d : ℕ) :
    (∑ m ∈ Finset.range d,
        S F 2 (by omega : 0 < 2) (pair w1 w2) m *
          (∑ ℓ ∈ Finset.range m, S F 1 (by omega : 0 < 1) (single v) ℓ)) =
    ∑ t : P2Idx v w2,
      ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F (p2Dep v w2 t + 1) (by omega)
        (consVec w1 (p2C v w2 t)) d := by
  classical
  calc
    (∑ m ∈ Finset.range d,
        S F 2 (by omega : 0 < 2) (pair w1 w2) m *
          (∑ ℓ ∈ Finset.range m, S F 1 (by omega : 0 < 1) (single v) ℓ))
        = ∑ m ∈ Finset.range d,
            S F 2 (by omega : 0 < 2) (pair w1 w2) m * S_lt F 1 (by omega : 0 < 1) (single v) m := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [← S_lt_eq_sum_levels F 1 (by omega : 0 < 1) (single v) m]
    _ = ∑ m ∈ Finset.range d,
          P F m w1 * (S_lt F 1 (by omega : 0 < 1) (single w2) m *
            S_lt F 1 (by omega : 0 < 1) (single v) m) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [S_two_pair_rec F w1 w2 m]
          rw [mul_assoc]
    _ = ∑ m ∈ Finset.range d,
          P F m w1 * (S_lt F 1 (by omega : 0 < 1) (single v) m *
            S_lt F 1 (by omega : 0 < 1) (single w2) m) := by
          apply Finset.sum_congr rfl
          intro m hm
          congr 1
          exact mul_comm (S_lt F 1 (by omega : 0 < 1) (single w2) m)
            (S_lt F 1 (by omega : 0 < 1) (single v) m)
    _ = ∑ m ∈ Finset.range d,
          P F m w1 * (∑ t : P2Idx v w2,
            ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (p2Dep v w2 t) (p2Dep_pos v w2 t) (p2C v w2 t) m) := by
          apply Finset.sum_congr rfl
          intro m hm
          congr 1
          exact (p2stuffle_eq F v w2 m).symm
    _ = ∑ m ∈ Finset.range d,
          ∑ t : P2Idx v w2,
            ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
            (P F m w1 * S_lt F (p2Dep v w2 t) (p2Dep_pos v w2 t) (p2C v w2 t) m) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
    _ = ∑ t : P2Idx v w2,
          ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
          (∑ m ∈ Finset.range d,
            S F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) m) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t ht
          calc
            (∑ m ∈ Finset.range d,
                ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
                (P F m w1 * S_lt F (p2Dep v w2 t) (p2Dep_pos v w2 t) (p2C v w2 t) m))
                = ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
                  (∑ m ∈ Finset.range d,
                    P F m w1 * S_lt F (p2Dep v w2 t) (p2Dep_pos v w2 t) (p2C v w2 t) m) := by
                  exact (Finset.mul_sum (s := Finset.range d)
                    (a := ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F))
                    (f := fun m : ℕ => P F m w1 *
                      S_lt F (p2Dep v w2 t) (p2Dep_pos v w2 t) (p2C v w2 t) m)).symm
            _ = ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
                  (∑ m ∈ Finset.range d,
                    S F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) m) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro m hm
                  rw [S_prepend F m w1 (p2Dep_pos v w2 t) (p2C v w2 t)]
    _ = ∑ t : P2Idx v w2,
          ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
          S_lt F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [← S_lt_eq_sum_levels F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d]

/-- The depth-(1,2) `S_<d` product identity (paper (2.4)) in carrier-friendly form:
`S_<d(v)·S_<d(w1,w2) = G1 + G2 + G3`, valid ∀ d. -/
lemma p2two_level (v w1 w2 : ℕ+) (d : ℕ) :
    S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F 2 (by omega : 0 < 2) (pair w1 w2) d =
      S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d +
      (∑ t : P2Idx v w2,
        ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d) +
      (∑ a : p1twoIdx v w1 w2,
        ((p1twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a) (p1twoC v w1 w2 a) d) := by
  classical
  let A : ℕ → RatFunc.CompletionAtInfty F := fun i => S F 1 (by omega : 0 < 1) (single v) i
  let B : ℕ → RatFunc.CompletionAtInfty F := fun j => S F 2 (by omega : 0 < 2) (pair w1 w2) j
  have h1 : (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, A ℓ * B m) =
      (∑ i ∈ Finset.range d, S F 1 (by omega : 0 < 1) (single v) i *
        (∑ j ∈ Finset.range i, S F 2 (by omega : 0 < 2) (pair w1 w2) j)) := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    exact (Finset.mul_sum (s := Finset.range ℓ) (a := A ℓ) (f := B)).symm
  have h2 : (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, A ℓ * B m) =
      (∑ m ∈ Finset.range d, S F 2 (by omega : 0 < 2) (pair w1 w2) m *
        (∑ ℓ ∈ Finset.range m, S F 1 (by omega : 0 < 1) (single v) ℓ)) := by
    apply Finset.sum_congr rfl
    intro m hm
    calc
      (∑ ℓ ∈ Finset.range m, A ℓ * B m)
          = (∑ ℓ ∈ Finset.range m, A ℓ) * B m := by
            exact (Finset.sum_mul (s := Finset.range m) (f := A) (a := B m)).symm
      _ = B m * (∑ ℓ ∈ Finset.range m, A ℓ) := by
            rw [mul_comm]
      _ = S F 2 (by omega : 0 < 2) (pair w1 w2) m *
            (∑ ℓ ∈ Finset.range m, S F 1 (by omega : 0 < 1) (single v) ℓ) := by
            rfl
  calc
    S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F 2 (by omega : 0 < 2) (pair w1 w2) d
        = (∑ i ∈ Finset.range d, A i) * (∑ j ∈ Finset.range d, B j) := by
          rw [S_lt_eq_sum_levels F 1 (by omega : 0 < 1) (single v) d]
          rw [S_lt_eq_sum_levels F 2 (by omega : 0 < 2) (pair w1 w2) d]
    _ = (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, A ℓ * B m) +
        (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, A ℓ * B m) +
        (∑ ℓ ∈ Finset.range d, A ℓ * B ℓ) := by
          exact Commons.Data.Finset.sum_range_mul_split (R := RatFunc.CompletionAtInfty F) d A B
    _ = (∑ i ∈ Finset.range d, S F 1 (by omega : 0 < 1) (single v) i *
          (∑ j ∈ Finset.range i, S F 2 (by omega : 0 < 2) (pair w1 w2) j)) +
        (∑ m ∈ Finset.range d, S F 2 (by omega : 0 < 2) (pair w1 w2) m *
          (∑ ℓ ∈ Finset.range m, S F 1 (by omega : 0 < 1) (single v) ℓ)) +
        (∑ ℓ ∈ Finset.range d, A ℓ * B ℓ) := by
          rw [h1, h2]
    _ = S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d +
        (∑ t : P2Idx v w2,
          ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
          S_lt F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d) +
        (∑ a : p1twoIdx v w1 w2,
          ((p1twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
          S_lt F (p1twoDep v w1 w2 a) (p1twoDep_pos v w1 w2 a) (p1twoC v w1 w2 a) d) := by
          rw [g1eq F v w1 w2 d]
          rw [g2eq F v w1 w2 d]
          rw [g3eq F v w1 w2 d]

/-- Generic cons bound: if the tail has weight `W` and all prefixes ≤ `W`, the head
`h` fits before the target `(u)+(t1,t2)` when `h ≤ u+t1` and `h+W = u+t1+t2`. -/
lemma LePad_cons_generic (h u t1 t2 : ℕ+) {L : ℕ} (c : Fin L → ℕ+) (W : ℕ)
    (hwt : weight L c = W) (hpre : ∀ m, psum c m ≤ W)
    (hm1 : (h : ℕ) ≤ (u : ℕ) + (t1 : ℕ))
    (hW : (h : ℕ) + W = (u : ℕ) + (t1 : ℕ) + (t2 : ℕ)) :
    LePad (consVec h c) (single u) (pair t1 t2) := by
  constructor
  · rw [weight_consVec, hwt, weight_single, weight_pair]
    omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single u) (pair t1 t2)) 0
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        by_cases hn : n = 0
        · subst n
          have ht : psumSeq (tupPadSum (single u) (pair t1 t2)) 1 = (u : ℕ) + (t1 : ℕ) :=
            psumSeq_single_pair_one u t1 t2
          rw [ht]
          have hc0 : psum c 0 = 0 := by rw [psum_zero]
          rw [hc0]
          exact hm1
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          have hge2 : 2 ≤ n + 1 := by omega
          have ht : psumSeq (tupPadSum (single u) (pair t1 t2)) (n + 1) =
              (u : ℕ) + (t1 : ℕ) + (t2 : ℕ) := psumSeq_single_pair_ge u t1 t2 hge2
          rw [ht]
          have hb : psum c n ≤ W := hpre n
          omega

/-- Finite index of the depth-(1,2) `S_<d` expansion: the pure merge ⊕ the (v,w2)
stuffle ⊕ the Part-1 (1,2) outputs. -/
abbrev p2twoIdx (v w1 w2 : ℕ+) := PUnit ⊕ P2Idx v w2 ⊕ p1twoIdx v w1 w2

noncomputable def p2twoDep (v w1 w2 : ℕ+) : p2twoIdx v w1 w2 → ℕ := fun a => match a with
  | Sum.inl _ => 3
  | Sum.inr (Sum.inl t) => p2Dep v w2 t + 1
  | Sum.inr (Sum.inr x) => p1twoDep v w1 w2 x

lemma p2twoDep_pos (v w1 w2 : ℕ+) (a : p2twoIdx v w1 w2) : 0 < p2twoDep v w1 w2 a := by
  cases a with
  | inl u => simp [p2twoDep]
  | inr p => cases p with
    | inl t => simp [p2twoDep, p2Dep_pos]
    | inr x => simp [p2twoDep, p1twoDep_pos]

lemma p2twoDep_le (v w1 w2 : ℕ+) (a : p2twoIdx v w1 w2) : p2twoDep v w1 w2 a ≤ 3 := by
  cases a with
  | inl u => simp [p2twoDep]
  | inr p => cases p with
    | inl t =>
      have ht := p2Dep_le_two v w2 t
      simp [p2twoDep]
      omega
    | inr x => exact p1twoDep_le v w1 w2 x

noncomputable def p2twoF (v w1 w2 : ℕ+) : p2twoIdx v w1 w2 → ℤ := fun a => match a with
  | Sum.inl _ => (1 : ℤ)
  | Sum.inr (Sum.inl t) => p2F F v w2 t
  | Sum.inr (Sum.inr x) => p1twoF F v w1 w2 x

noncomputable def p2twoC (v w1 w2 : ℕ+) :
    ∀ a : p2twoIdx v w1 w2, Fin (p2twoDep v w1 w2 a) → ℕ+ := fun a => match a with
  | Sum.inl _ => consVec v (pair w1 w2)
  | Sum.inr (Sum.inl t) => consVec w1 (p2C v w2 t)
  | Sum.inr (Sum.inr x) => p1twoC v w1 w2 x

/-- Bound of the pure-merge output of the (1,2) `S_<d` product. -/
lemma p2two_lePad_pure (v w1 w2 : ℕ+) :
    LePad (p2twoC v w1 w2 (Sum.inl PUnit.unit)) (single v) (pair w1 w2) := by
  simpa [p2twoC, p2twoDep] using
    (LePad_cons_generic v v w1 w2 (pair w1 w2) ((w1 : ℕ) + (w2 : ℕ))
      (weight_pair w1 w2)
      (by intro m; exact (psum_le_weight (pair w1 w2) m).trans (le_of_eq (weight_pair w1 w2)))
      (by omega)
      (by omega))

/-- Bound of the stuffle outputs of the (1,2) `S_<d` product. -/
lemma p2two_lePad_stuffle (v w1 w2 : ℕ+) (t : P2Idx v w2) :
    LePad (p2twoC v w1 w2 (Sum.inr (Sum.inl t))) (single v) (pair w1 w2) := by
  simpa [p2twoC, p2twoDep] using
    (LePad_cons_generic w1 v w1 w2 (p2C v w2 t) ((v : ℕ) + (w2 : ℕ))
      (p2C_weight v w2 t)
      (p2C_prefix_le v w2 t)
      (by omega)
      (by omega))

/-- Bound of the Part-1 outputs of the (1,2) `S_<d` product. -/
lemma p2two_lePad_p1 (v w1 w2 : ℕ+) (x : p1twoIdx v w1 w2) :
    LePad (p2twoC v w1 w2 (Sum.inr (Sum.inr x))) (single v) (pair w1 w2) := by
  cases x with
  | inl u => simpa [p2twoC, p2twoDep] using p1two_lePad_pure v w1 w2
  | inr p => simpa [p2twoC, p2twoDep] using p1two_lePad_delta v w1 w2 p.1 p.2

/-- The depth-(1,2) `S_<d` carrier sum equals the level RHS (2.4), at every level. -/
lemma p2two_rhs_eq (v w1 w2 : ℕ+) (d : ℕ) :
    (∑ a : p2twoIdx v w1 w2,
      ((p2twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F (p2twoDep v w1 w2 a) (p2twoDep_pos v w1 w2 a) (p2twoC v w1 w2 a) d) =
    S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d +
      (∑ t : P2Idx v w2,
        ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d) +
      (∑ x : p1twoIdx v w1 w2,
        ((p1twoF F v w1 w2 x : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F (p1twoDep v w1 w2 x) (p1twoDep_pos v w1 w2 x) (p1twoC v w1 w2 x) d) := by
  classical
  let T : p2twoIdx v w1 w2 → RatFunc.CompletionAtInfty F := fun a =>
    ((p2twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
    S_lt F (p2twoDep v w1 w2 a) (p2twoDep_pos v w1 w2 a) (p2twoC v w1 w2 a) d
  have hsplit : (∑ a : p2twoIdx v w1 w2, T a) =
      T (Sum.inl PUnit.unit) +
        ∑ p : P2Idx v w2 ⊕ p1twoIdx v w1 w2, T (Sum.inr p) := by
    have hsum := Fintype.sum_sum_type (f := T)
    rw [hsum]
    simp
  have hsplit2 : (∑ p : P2Idx v w2 ⊕ p1twoIdx v w1 w2, T (Sum.inr p)) =
      (∑ t : P2Idx v w2, T (Sum.inr (Sum.inl t))) +
      ∑ x : p1twoIdx v w1 w2, T (Sum.inr (Sum.inr x)) := by
    have hsum := Fintype.sum_sum_type
      (f := fun p : P2Idx v w2 ⊕ p1twoIdx v w1 w2 => T (Sum.inr p))
    rw [hsum]
  calc
    (∑ a : p2twoIdx v w1 w2, T a)
        = T (Sum.inl PUnit.unit) +
            ((∑ t : P2Idx v w2, T (Sum.inr (Sum.inl t))) +
             ∑ x : p1twoIdx v w1 w2, T (Sum.inr (Sum.inr x))) := by
          rw [hsplit, hsplit2]
    _ = S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d +
            (∑ t : P2Idx v w2,
              ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d) +
          ∑ x : p1twoIdx v w1 w2,
            ((p1twoF F v w1 w2 x : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (p1twoDep v w1 w2 x) (p1twoDep_pos v w1 w2 x) (p1twoC v w1 w2 x) d := by
          have hp : T (Sum.inl PUnit.unit) =
              S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d := by
            simp [T, p2twoF, p2twoDep, p2twoC]
          rw [hp]
          rw [show (∑ t : P2Idx v w2, T (Sum.inr (Sum.inl t))) =
              ∑ t : P2Idx v w2,
                ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
                S_lt F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d by
                apply Finset.sum_congr rfl
                intro t ht
                simp [T, p2twoF, p2twoDep, p2twoC]]
          rw [show (∑ x : p1twoIdx v w1 w2, T (Sum.inr (Sum.inr x))) =
              ∑ x : p1twoIdx v w1 w2,
                ((p1twoF F v w1 w2 x : ℤ) : RatFunc.CompletionAtInfty F) *
                S_lt F (p1twoDep v w1 w2 x) (p1twoDep_pos v w1 w2 x) (p1twoC v w1 w2 x) d by
                apply Finset.sum_congr rfl
                intro x hx
                simp [T, p2twoF, p2twoDep, p2twoC]]
          ac_rfl
    _ = S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d +
          (∑ t : P2Idx v w2,
            ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d) +
          (∑ x : p1twoIdx v w1 w2,
            ((p1twoF F v w1 w2 x : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (p1twoDep v w1 w2 x) (p1twoDep_pos v w1 w2 x) (p1twoC v w1 w2 x) d) := by
          ac_rfl

/-- ★ Part 2 cons case at depth (1,2): `S_<d(v)·S_<d(w1,w2)` in the P2W carrier. -/
theorem p2two (v w1 w2 : ℕ+) :
    P2W F 1 2 (by omega : 0 < 1) (by omega : 0 < 2) (single v) (pair w1 w2) := by
  refine ⟨p2twoIdx v w1 w2, ?_, p2twoDep v w1 w2, p2twoDep_pos v w1 w2, p2twoF F v w1 w2,
    p2twoC v w1 w2, ?hid, ?hle, ?hbd⟩
  · infer_instance
  · intro d
    calc
      S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F 2 (by omega : 0 < 2) (pair w1 w2) d
          = S_lt F 3 (by omega : 0 < 3) (consVec v (pair w1 w2)) d +
            (∑ t : P2Idx v w2,
              ((p2F F v w2 t : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (p2Dep v w2 t + 1) (by omega) (consVec w1 (p2C v w2 t)) d) +
            (∑ x : p1twoIdx v w1 w2,
              ((p1twoF F v w1 w2 x : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (p1twoDep v w1 w2 x) (p1twoDep_pos v w1 w2 x) (p1twoC v w1 w2 x) d) :=
            p2two_level F v w1 w2 d
      _ = (∑ a : p2twoIdx v w1 w2, ((p2twoF F v w1 w2 a : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (p2twoDep v w1 w2 a) (p2twoDep_pos v w1 w2 a) (p2twoC v w1 w2 a) d) := by
            exact (p2two_rhs_eq F v w1 w2 d).symm
  · intro a
    cases a with
    | inl u => exact p2two_lePad_pure v w1 w2
    | inr p => cases p with
      | inl t => exact p2two_lePad_stuffle v w1 w2 t
      | inr x => exact p2two_lePad_p1 v w1 w2 x
  · intro a
    exact p2twoDep_le v w1 w2 a

/-- Part 2 at depth (1,2) for an arbitrary depth-two tuple. -/
theorem p2one_two : P2one F 2 (by omega : 0 < 2) := by
  intro v W
  rw [fin2_eq_pair W]
  exact p2two F v (W ⟨0, by omega⟩) (W ⟨1, by omega⟩)

end ZagierHoffmanPositiveChar
