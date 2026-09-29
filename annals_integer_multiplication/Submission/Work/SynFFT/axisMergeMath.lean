import Mathlib
import Submission.Work.SynFFT.axisKit

/-!
# Pure list facts about the blockwise merge (`mLevel`/`iter`/`mAll`)

`iter k` is `k` merge levels (`mLevel`) of the pairwise-concatenation tree of `axisKit`, and
`mAll Gs = iter Gs.length Gs` is the merge phase run to completion.  This file collects the pure
list layer of the correctness of the transpose word:

* `iter` is the identity on a list of at most one group (`iter_self_of_length_le_one`), and it is
  "eventually constant": once the level count reaches the length, `iter k` is `mAll`
  (`iter_eq_mAll`), and `mAll` is stable under one further level (`mAll_mLevel`);
* on the image of `cols` (a list of rows / of groups of rows) a merge level is the elementwise
  concatenation of adjacent groups (`mLevel_map_cols`), so `mAll (ps.map cols) = [cols ps.flatten]`
  (`mAll_map_cols`, i.e. associativity of `zipCat`); the exploded-row special case
  (`mAll_map_exploded`) is the leaf of the transpose recursion.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## `mLevel` is the identity on lists of at most one group -/

theorem mLevel_self_of_length_le_one (Gs : List (List (List Val))) (h : Gs.length ≤ 1) :
    mLevel Gs = Gs := by
  match Gs with
  | [] => rfl
  | [_] => rfl

theorem iter_self_of_length_le_one (k : ℕ) (Gs : List (List (List Val)))
    (h : Gs.length ≤ 1) : iter k Gs = Gs := by
  have key : ∀ k : ℕ, iter k Gs = Gs := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iter_succ, mLevel_self_of_length_le_one Gs h]; exact ih
  exact key k

/-- Iterating `iter` is iterating the corresponding levels. -/
theorem iter_add (a b : ℕ) (Gs : List (List (List Val))) :
    iter (a + b) Gs = iter a (iter b Gs) := by
  induction b generalizing Gs with
  | zero => simp
  | succ b ih => rw [Nat.add_succ, iter_succ, ih, iter_succ]

/-! ## The length decreases by one per level (once it is `≥ 2`) -/

theorem mLevel_length_lt (Gs : List (List (List Val))) (h : 2 ≤ Gs.length) :
    (mLevel Gs).length < Gs.length := by
  rw [mLevel_length]
  omega

/-- `k` levels suffice to bring a list of `k` groups down to at most one group. -/
theorem iter_length_le_one_of_le : ∀ (k : ℕ) (Gs : List (List (List Val))),
    Gs.length ≤ k → (iter k Gs).length ≤ 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Gs h
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rw [iter_self_of_length_le_one k Gs (by omega)]
      omega
    · cases k with
      | zero => omega
      | succ k' =>
        have hml : (mLevel Gs).length ≤ k' := by
          have hlen := mLevel_length Gs
          omega
        rw [iter_succ]
        exact ih k' (by omega) (mLevel Gs) hml

theorem mAll_length_le_one (Gs : List (List (List Val))) : (mAll Gs).length ≤ 1 :=
  iter_length_le_one_of_le Gs.length Gs le_rfl

/-! ## `iter` reaches `mAll` and stays there -/

theorem iter_eq_mAll (k : ℕ) (Gs : List (List (List Val))) (h : Gs.length ≤ k) :
    iter k Gs = mAll Gs := by
  rw [← Nat.sub_add_cancel h, iter_add]
  exact iter_self_of_length_le_one _ _ (mAll_length_le_one Gs)

theorem mAll_mLevel (Gs : List (List (List Val))) (h : 2 ≤ Gs.length) :
    mAll Gs = mAll (mLevel Gs) := by
  have hlt := mLevel_length_lt Gs h
  have h1 : Gs.length = (Gs.length - 1) + 1 := by omega
  have key : iter Gs.length Gs = iter (Gs.length - 1) (mLevel Gs) := by
    conv_lhs => rw [h1]
    rw [iter_succ]
  show iter Gs.length Gs = mAll (mLevel Gs)
  rw [key]
  exact iter_eq_mAll _ _ (by omega)

theorem mAll_self_of_length_le_one (Gs : List (List (List Val))) (h : Gs.length ≤ 1) :
    mAll Gs = Gs :=
  iter_self_of_length_le_one Gs.length Gs h

/-! ## `pairUp` reaches a single piece -/

theorem pairUp_ne_nil (ps : List (List (List Val))) (h : ps ≠ []) : pairUp ps ≠ [] := by
  cases ps with
  | nil => exact absurd rfl h
  | cons p rest =>
    cases rest with
    | nil => simp [pairUp]
    | cons q rest' => simp [pairUp]

/-- `k` pairings collapse a nonempty list of at most `2^k` pieces to the single piece
`[ps.flatten]` (`pairUp` preserves the flattening). -/
theorem pairUp_iter_eq_singleton : ∀ (k : ℕ) (ps : List (List (List Val))),
    ps ≠ [] → ps.length ≤ 2 ^ k → (pairUp^[k]) ps = [ps.flatten] := by
  intro k
  induction k with
  | zero =>
    intro ps hne hlen
    obtain ⟨p, rfl⟩ : ∃ p, ps = [p] := by
      cases ps with
      | nil => exact absurd rfl hne
      | cons p rest => cases rest with
        | nil => exact ⟨p, rfl⟩
        | cons q rest' => simp at hlen
    simp
  | succ k ih =>
    intro ps hne hlen
    rw [Function.iterate_succ_apply]
    rw [ih (pairUp ps) (pairUp_ne_nil ps hne) (by rw [pairUp_length]; omega)]
    rw [pairUp_flatten]

/-! ## The merge phase on a list of `cols` -/

/-- One merge level is one pairing, on the image of `cols`. -/
theorem iter_map_cols : ∀ (k : ℕ) (ps : List (List (List Val))),
    ps ≠ [] → ps.length ≤ 2 ^ k → iter k (ps.map cols) = [cols ps.flatten] := by
  intro k
  induction k with
  | zero =>
    intro ps hne hlen
    obtain ⟨p, rfl⟩ : ∃ p, ps = [p] := by
      cases ps with
      | nil => exact absurd rfl hne
      | cons p rest => cases rest with
        | nil => exact ⟨p, rfl⟩
        | cons q rest' => simp at hlen
    simp
  | succ k ih =>
    intro ps hne hlen
    rw [iter_succ, mLevel_map_cols]
    rw [ih (pairUp ps) (pairUp_ne_nil ps hne) (by rw [pairUp_length]; omega),
      pairUp_flatten]

theorem mAll_map_cols (ps : List (List (List Val))) (hne : ps ≠ []) :
    mAll (ps.map cols) = [cols ps.flatten] := by
  show iter (ps.map cols).length (ps.map cols) = [cols ps.flatten]
  rw [List.length_map]
  exact iter_map_cols _ _ hne (le_of_lt Nat.lt_two_pow_self)

theorem flatten_map_singleton {α : Type*} (l : List α) : (l.map (fun x => [x])).flatten = l := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [ih]

theorem mAll_map_exploded (rows : List (List Val)) (hne : rows ≠ []) :
    mAll (rows.map exploded) = [cols rows] := by
  have hne' : rows.map (fun r => [r]) ≠ [] := by
    simpa [List.map_eq_nil_iff] using hne
  have h := mAll_map_cols (rows.map (fun r => [r])) hne'
  have h1 : (rows.map (fun r => [r])).map cols = rows.map exploded := by
    rw [List.map_map]
    exact List.map_congr_left (fun r _ => cols_singleton r)
  have h2 : (rows.map (fun r => [r])).flatten = rows := flatten_map_singleton rows
  rw [h1, h2] at h
  exact h

/-! ## The requested conjunction -/

theorem axisMergeMath :
    (∀ (k : ℕ) (Gs : List (List (List HvdH.Val))), Gs.length ≤ 1 → iter k Gs = Gs) ∧
    (∀ (k : ℕ) (Gs : List (List (List HvdH.Val))), Gs.length ≤ k → iter k Gs = mAll Gs) ∧
    (∀ (Gs : List (List (List HvdH.Val))), 2 ≤ Gs.length → mAll Gs = mAll (mLevel Gs)) ∧
    (∀ (Gs : List (List (List HvdH.Val))), Gs.length ≤ 1 → mAll Gs = Gs) ∧
    (∀ (k : ℕ) (ps : List (List (List HvdH.Val))), ps ≠ [] → ps.length ≤ 2 ^ k →
      iter k (ps.map cols) = [cols ps.flatten]) ∧
    (∀ (ps : List (List (List HvdH.Val))), ps ≠ [] → mAll (ps.map cols) = [cols ps.flatten]) ∧
    (∀ (rows : List (List HvdH.Val)), rows ≠ [] → mAll (rows.map exploded) = [cols rows]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k Gs h; exact iter_self_of_length_le_one k Gs h
  · intro k Gs h; exact iter_eq_mAll k Gs h
  · intro Gs h; exact mAll_mLevel Gs h
  · intro Gs h; exact mAll_self_of_length_le_one Gs h
  · intro k ps hne hlen; exact iter_map_cols k ps hne hlen
  · intro ps hne; exact mAll_map_cols ps hne
  · intro rows hne; exact mAll_map_exploded rows hne

end Work.SynFFT
