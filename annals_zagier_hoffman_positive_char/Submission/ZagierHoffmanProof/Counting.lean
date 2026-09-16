import Mathlib
import ChallengeDeps
import Submission.ZagierHoffmanProof.Basic

/-!
# Counting of Hoffman tuples (rank part of theorem A)

Formalization of the counting of Hoffman tuples of weight `w` (any depth, entries `≤ q`
except the last `< q`), proving that their number is the paper's `d(w)`.  The central
objects are `ShapeT F w w` (padded shapes), `hoffCount`, the recursion
`hoffCount_rec`, and the equality `hoffCount_eq_d` with `ChallengeDeps.d`.
This supports the rank bound `Module.rank K (𝒵 F w) ≤ d F w` once the span part
(`𝒵 F w = span K (𝒯 F w)`) is available.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Padded carrier of weight `w`: a depth marker `m : Fin w` (the shape has depth `m+1`,
i.e. entries at indices `0..m`) and a padded entry function `f : Fin w → Fin (q+1)` with
entries `0..q` (`q = |F|`).  Entries beyond the depth (`m < i`) are required to be `0`. -/
abbrev PaddedCarrier (w : ℕ) : Type := Fin w × (Fin w → Fin (Nat.card F + 1))

/-- Shape conditions at weight `v` on a padded carrier: total weight `v` (only the first
`m+1` entries contribute, the rest are zero), positive entries on `0..m`, zero beyond `m`,
and last entry (`i = m`) `< q`. -/
def PaddedCond (v : ℕ) {w : ℕ} (x : PaddedCarrier F w) : Prop :=
  (∑ i : Fin w, ((x.2 i : Fin (Nat.card F + 1)) : ℕ)) = v ∧
  (∀ i : Fin w, (i : ℕ) ≤ (x.1 : ℕ) → 1 ≤ ((x.2 i : Fin (Nat.card F + 1)) : ℕ)) ∧
  (∀ i : Fin w, (x.1 : ℕ) < (i : ℕ) → ((x.2 i : Fin (Nat.card F + 1)) : ℕ) = 0) ∧
  ((x.2 ⟨(x.1 : ℕ), x.1.isLt⟩ : Fin (Nat.card F + 1)) : ℕ) < Nat.card F

/-- Hoffman shapes of weight `v` padded to weight `w`. -/
noncomputable def ShapeT (w v : ℕ) : Type :=
  {x : PaddedCarrier F w // PaddedCond F v x}

/-- Total number of Hoffman shapes of weight `w`. -/
noncomputable def hoffCount (w : ℕ) : ℕ := Nat.card (ShapeT F w w)

noncomputable instance (w v : ℕ) : Fintype (ShapeT F w v) := by
  classical
  unfold ShapeT
  infer_instance

/-- The depth `m + 1` of a weight-`v` shape is at most `v`. -/
lemma ShapeT_depth_le {w v : ℕ} (x : ShapeT F w v) : (x.1.1 : ℕ) + 1 ≤ v := by
  classical
  have hx : PaddedCond F v x.1 := x.2
  let m : ℕ := (x.1.1 : ℕ)
  let p : Finset (Fin w) := (Finset.univ : Finset (Fin w)).filter (fun i => (i : ℕ) ≤ m)
  let f : Fin w → ℕ := fun i => ((x.1.2 i : Fin (Nat.card F + 1)) : ℕ)
  -- off-prefix entries are zero
  have hz : ∀ i : Fin w, i ∉ p → f i = 0 := by
    intro i hi
    dsimp [f]
    have : m < (i : ℕ) := by
      simp [p] at hi
      omega
    exact hx.2.2.1 i this
  -- the prefix has exactly m + 1 elements
  have hcard : p.card = m + 1 := by
    have hbij : p ≃ Fin (m + 1) := by
      refine {
        toFun := fun i => by
          rcases i with ⟨i, hi⟩
          refine ⟨(i : ℕ), ?_⟩
          have hle : (i : ℕ) ≤ m := by
            simpa [p] using hi
          omega
        invFun := fun j => by
          have hj : (j : ℕ) < m + 1 := j.isLt
          have hmw : m < w := x.1.1.isLt
          refine ⟨⟨(j : ℕ), by omega⟩, ?_⟩
          have hj' : (j : ℕ) ≤ m := by omega
          simpa [p] using hj'
        left_inv := by intro i; apply Subtype.ext; apply Fin.ext; rfl
        right_inv := by intro j; apply Fin.ext; rfl }
    simpa [Fintype.card_fin] using (Fintype.card_congr hbij)
  -- sum over univ = sum over prefix (rest are zero)
  have hsplit : (∑ i : Fin w, f i) = ∑ i ∈ p, f i := by
    have hsf := Finset.sum_filter (s := (Finset.univ : Finset (Fin w)))
      (p := fun i : Fin w => (i : ℕ) ≤ m) (f := f)
    have hs : (∑ i ∈ p, f i) = ∑ i : Fin w, f i := by
      calc
        (∑ i ∈ p, f i) = ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≤ m), f i := by rfl
        _ = ∑ i : Fin w, (if (i : ℕ) ≤ m then f i else 0) := by
              rw [hsf]
        _ = ∑ i : Fin w, f i := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hp : (i : ℕ) ≤ m
              · simp [hp]
              · have hnp : i ∉ p := by
                  simp [p, hp]
                have hz' := hz i hnp
                simp [hp, hz']
    exact hs.symm
  calc
    m + 1 = p.card := hcard.symm
    _ = ∑ i ∈ p, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ p, f i := by
          exact Finset.sum_le_sum (fun i hi => hx.2.1 i (by simp [p] at hi; omega))
    _ = ∑ i : Fin w, f i := hsplit.symm
    _ = v := hx.1

/-- Single-part shapes (carrier level): depth 1 (`m = 0`). -/
def SingleT (w v : ℕ) : Type :=
  {x : PaddedCarrier F w // PaddedCond F v x ∧ (x.1 : ℕ) = 0}

/-- Multi-part shapes (carrier level): depth at least 2 (`1 ≤ m`). -/
def MultiT (w v : ℕ) : Type :=
  {x : PaddedCarrier F w // PaddedCond F v x ∧ 1 ≤ (x.1 : ℕ)}

noncomputable instance (w v : ℕ) : Fintype (SingleT F w v) := by
  classical
  unfold SingleT
  infer_instance
noncomputable instance (w v : ℕ) : Fintype (MultiT F w v) := by
  classical
  unfold MultiT
  infer_instance

/-- Every shape is single or multi. -/
noncomputable def singleMultiEquiv (w v : ℕ) :
    ShapeT F w v ≃ SingleT F w v ⊕ MultiT F w v := by
  classical
  have e1 : {x : ShapeT F w v // (x.1.1 : ℕ) = 0} ≃ SingleT F w v :=
    Equiv.subtypeSubtypeEquivSubtypeInter (p := PaddedCond F v)
      (q := fun c : PaddedCarrier F w => (c.1 : ℕ) = 0)
  have e2 : {x : ShapeT F w v // ¬ (x.1.1 : ℕ) = 0} ≃ MultiT F w v := by
    exact (Equiv.subtypeEquivRight (fun x : ShapeT F w v => by
      constructor <;> intro h <;> omega)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (p := PaddedCond F v)
        (q := fun c : PaddedCarrier F w => 1 ≤ (c.1 : ℕ)))
  exact (Equiv.sumCompl (p := fun x : ShapeT F w v => (x.1.1 : ℕ) = 0)).symm.trans
    (Equiv.sumCongr e1 e2)

/-- `hoffCount(w) = |single| + |multi|`. -/
lemma hoffCount_eq_single_add_multi (w : ℕ) :
    hoffCount F w = Nat.card (SingleT F w w) + Nat.card (MultiT F w w) := by
  classical
  unfold hoffCount
  rw [Nat.card_congr (singleMultiEquiv F w w)]
  rw [Nat.card_sum]



/-- Sum over `Fin w` of an indicator at the zero index (`w ≥ 1`). -/
lemma sum_indicator_zero {w : ℕ} (hw : 1 ≤ w) {M : Type*} [AddCommMonoid M] (a : M) :
    (∑ i : Fin w, (if i = (⟨0, by omega⟩ : Fin w) then a else 0)) = a := by
  classical
  let z : Fin w := ⟨0, by omega⟩
  have h := Fintype.sum_eq_single (α := Fin w) (M := M)
    (f := fun i : Fin w => (if i = z then a else 0)) z (by
      intro b hb
      simp [hb])
  simpa using h

/-- A function on `Fin w` that is zero off the zero index has sum equal to its value there. -/
lemma sum_eq_zero_except_zero {w : ℕ} (hw : 1 ≤ w) (f : Fin w → ℕ)
    (hz : ∀ i : Fin w, i ≠ (⟨0, by omega⟩ : Fin w) → f i = 0) :
    (∑ i : Fin w, f i) = f (⟨0, by omega⟩ : Fin w) := by
  classical
  calc
    (∑ i : Fin w, f i) = ∑ i : Fin w, (if i = (⟨0, by omega⟩ : Fin w) then f (⟨0, by omega⟩ : Fin w) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h0 : i = (⟨0, by omega⟩ : Fin w)
          · simp [h0]
          · have hz' := hz i h0
            simp [h0, hz']
    _ = f (⟨0, by omega⟩ : Fin w) := sum_indicator_zero hw (f (⟨0, by omega⟩ : Fin w))

/-- The canonical single shape of weight `w` (valid when `w < q`): the tuple `(w)`. -/
noncomputable def canonicalSingle {w : ℕ} (hw : 1 ≤ w) (hwq : w < Nat.card F) :
    SingleT F w w := by
  classical
  let z : Fin w := ⟨0, by omega⟩
  let f : Fin w → Fin (Nat.card F + 1) := fun i =>
    if i = z then (⟨w, by omega⟩ : Fin (Nat.card F + 1)) else 0
  refine ⟨⟨z, f⟩, ?_, rfl⟩
  constructor
  · -- weight = w
    have hsum := sum_indicator_zero (M := ℕ) hw w
    calc
      (∑ i : Fin w, ((f i : Fin (Nat.card F + 1)) : ℕ))
          = (∑ i : Fin w, (if i = z then (w : ℕ) else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h0 : i = z
            · simp [f, h0]
            · simp [f, h0]
      _ = w := by simpa using hsum
  · constructor
    · intro i hi
      have h0 : (i : ℕ) = 0 := by
        dsimp [z] at hi
        omega
      have hi0 : i = z := by
        apply Fin.ext
        exact h0
      simp [f, hi0]
      exact hw
    · constructor
      · intro i hi
        have hne : i ≠ z := by
          intro h0
          have hv : (i : ℕ) = 0 := by simpa [z] using congrArg (fun t : Fin w => (t : ℕ)) h0
          dsimp [z] at hi
          omega
        simp [f, hne]
      · -- last entry (index 0) < q
        simp [f]
        exact hwq

/-- Every single shape of weight `w` is the canonical one. -/
lemma single_eq_canonical {w : ℕ} (hw : 1 ≤ w) (hwq : w < Nat.card F)
    (x : SingleT F w w) : x = canonicalSingle F hw hwq := by
  classical
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨hcond, hm0⟩
  apply Subtype.ext
  -- carrier equality: x.1 = (canonicalSingle ...).1 ; both are (m = 0, f) pairs
  have hx0 : x.1 = (⟨0, by omega⟩ : Fin w) := by
    apply Fin.ext
    exact hm0
  -- entry values of x: 0-th is w, others 0
  have hval0 : ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) = w := by
    have hs := sum_eq_zero_except_zero hw (fun i : Fin w => ((x.2 i : Fin (Nat.card F + 1)) : ℕ)) (by
      intro i hi
      have hiv : (i : ℕ) ≠ 0 := by
        intro h
        apply hi
        apply Fin.ext
        exact h
      have hm : (x.1 : ℕ) < (i : ℕ) := by
        have : (x.1 : ℕ) = 0 := hm0
        omega
      exact hcond.2.2.1 i hm)
    exact hs.symm.trans hcond.1
  have hz : ∀ i : Fin w, i ≠ (⟨0, by omega⟩ : Fin w) → ((x.2 i : Fin (Nat.card F + 1)) : ℕ) = 0 := by
    intro i hi
    have hiv : (i : ℕ) ≠ 0 := by
      intro h
      apply hi
      apply Fin.ext
      exact h
    have hm : (x.1 : ℕ) < (i : ℕ) := by
      have : (x.1 : ℕ) = 0 := hm0
      omega
    exact hcond.2.2.1 i hm
  -- carrier: first components equal (both 0), then functions agree at every index
  apply Prod.ext
  · apply Fin.ext
    simp [canonicalSingle, hm0]
  · funext i
    apply Fin.ext
    by_cases h0 : i = (⟨0, by omega⟩ : Fin w)
    · -- index 0: both values are w
      have hx_i : ((x.2 i : Fin (Nat.card F + 1)) : ℕ) = w := by
        rw [h0]
        exact hval0
      calc
        ((x.2 i : Fin (Nat.card F + 1)) : ℕ) = w := hx_i
        _ = (((canonicalSingle F hw hwq).1.2 i : Fin (Nat.card F + 1)) : ℕ) := by
              rw [h0]
              simp [canonicalSingle]
    · -- off-zero: both values are 0
      have hx_i : ((x.2 i : Fin (Nat.card F + 1)) : ℕ) = 0 := hz i h0
      calc
        ((x.2 i : Fin (Nat.card F + 1)) : ℕ) = 0 := hx_i
        _ = (((canonicalSingle F hw hwq).1.2 i : Fin (Nat.card F + 1)) : ℕ) := by
              simp [canonicalSingle, h0]

/-- Cardinality of the single part at weight `w`: `1` iff `w < q`, else `0`. -/
lemma singleT_card {w : ℕ} (hw : 1 ≤ w) :
    Nat.card (SingleT F w w) = if w < Nat.card F then 1 else 0 := by
  classical
  by_cases hwq : w < Nat.card F
  · rw [if_pos hwq]
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨canonicalSingle F hw hwq, fun y => single_eq_canonical F hw hwq y⟩
  · rw [if_neg hwq]
    have hnone : IsEmpty (SingleT F w w) := by
      refine ⟨fun x => ?_⟩
      rcases x with ⟨x, hx⟩
      rcases hx with ⟨hcond, hm0⟩
      -- the single entry must be `< q` (last condition) but equals the weight `w ≥ q`
      have hval : ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) = w := by
        have hs := sum_eq_zero_except_zero hw (fun i : Fin w => ((x.2 i : Fin (Nat.card F + 1)) : ℕ)) (by
          intro i hi
          have hiv : (i : ℕ) ≠ 0 := by
            intro h
            apply hi
            apply Fin.ext
            exact h
          have hm : (x.1 : ℕ) < (i : ℕ) := by
            have : (x.1 : ℕ) = 0 := hm0
            omega
          exact hcond.2.2.1 i hm)
        exact hs.symm.trans hcond.1
      have hlast : ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) < Nat.card F := by
        have hl := hcond.2.2.2
        have hidx : ⟨(x.1 : ℕ), x.1.isLt⟩ = (⟨0, by omega⟩ : Fin w) := by
          apply Fin.ext
          exact hm0
        rw [hidx] at hl
        exact hl
      omega
    haveI : IsEmpty (SingleT F w w) := hnone
    simp



/-- Sum over `Fin w` splits at the head when all entries beyond `m` vanish:
`Σ f = f 0 + (sum of the body entries at indices 1..m)`. -/
lemma sum_split_head {w m : ℕ} (hm1 : 1 ≤ m) (hmw : m ≤ w - 1) (f : Fin w → ℕ)
    (hz : ∀ i : Fin w, m < (i : ℕ) → f i = 0) :
    (∑ i : Fin w, f i) = f (⟨0, by omega⟩ : Fin w) +
      ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ m), f i := by
  classical
  let p : Finset (Fin w) := (Finset.univ : Finset (Fin w)).filter (fun i => (i : ℕ) ≤ m)
  let b : Finset (Fin w) := (Finset.univ : Finset (Fin w)).filter (fun i => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ m)
  have hsplit : (∑ i : Fin w, f i) = ∑ i ∈ p, f i := by
    have hsf := Finset.sum_filter (s := (Finset.univ : Finset (Fin w)))
      (p := fun i : Fin w => (i : ℕ) ≤ m) (f := f)
    have hs : (∑ i ∈ p, f i) = ∑ i : Fin w, f i := by
      calc
        (∑ i ∈ p, f i) = ∑ i : Fin w, (if (i : ℕ) ≤ m then f i else 0) := by
              simpa [p] using hsf
        _ = ∑ i : Fin w, f i := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hp : (i : ℕ) ≤ m
              · simp [hp]
              · have hm : m < (i : ℕ) := by omega
                have hz' := hz i hm
                simp [hp, hz']
    exact hs.symm
  have hsfz := Finset.sum_filter_add_sum_filter_not (s := p)
    (p := fun i : Fin w => (i : ℕ) = 0) (f := f)
  have hzmem : (∑ i ∈ p.filter (fun i : Fin w => (i : ℕ) = 0), f i) = f (⟨0, by omega⟩ : Fin w) := by
    have hsing : p.filter (fun i : Fin w => (i : ℕ) = 0) = {⟨0, by omega⟩} := by
      ext i
      simp [p]
      constructor
      · intro hi
        apply Fin.ext
        exact hi.2
      · intro hi
        rw [hi]
        simp [p]
    rw [hsing]
    simp
  have hb : p.filter (fun i : Fin w => ¬ (i : ℕ) = 0) = b := by
    ext i
    simp [p, b]
    omega
  calc
    (∑ i : Fin w, f i) = ∑ i ∈ p, f i := hsplit
    _ = (∑ i ∈ p.filter (fun i : Fin w => (i : ℕ) = 0), f i) +
        (∑ i ∈ p.filter (fun i : Fin w => ¬ (i : ℕ) = 0), f i) := by
          rw [← hsfz]
    _ = f (⟨0, by omega⟩ : Fin w) + ∑ i ∈ b, f i := by
          rw [hzmem, hb]


/-- Sum over `Fin w` splits at the head: `Σ f = f 0 + (sum over the non-zero indices)`. -/
lemma split_at_zero {w : ℕ} (hw : 1 ≤ w) (f : Fin w → ℕ) :
    (∑ i : Fin w, f i) = f (⟨0, by omega⟩ : Fin w) +
      ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0), f i := by
  classical
  have hzmem : (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) = 0), f i) =
      f (⟨0, by omega⟩ : Fin w) := by
    have hsing : (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) = 0) =
        {⟨0, by omega⟩} := by
      ext i
      simp
      constructor
      · intro hi
        apply Fin.ext
        exact hi
      · intro hi
        rw [hi]
    rw [hsing]
    simp
  have hsfz := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin w)))
    (p := fun i : Fin w => (i : ℕ) = 0) (f := f)
  calc
    (∑ i : Fin w, f i)
        = (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) = 0), f i) +
          (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => ¬ (i : ℕ) = 0), f i) := by
          rw [← hsfz]
    _ = f (⟨0, by omega⟩ : Fin w) +
          ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0), f i := by
          rw [hzmem]

/-- The tail function: shifts `f` down by one slot, dropping the head (index 0). -/
noncomputable def tailFn {w : ℕ} {R : Type*} [Zero R] (f : Fin w → R) : Fin w → R :=
  fun j => if h : (j : ℕ) + 1 < w then f ⟨(j : ℕ) + 1, h⟩ else 0

/-- Sum of the tail equals the sum of `f` over the non-zero indices. -/
lemma tailFn_sum {w : ℕ} (hw : 1 ≤ w) (f : Fin w → ℕ) :
    (∑ j : Fin w, tailFn f j) =
      ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0), f i := by
  classical
  let D : Finset (Fin w) := (Finset.univ : Finset (Fin w)).filter (fun j : Fin w => (j : ℕ) + 1 < w)
  let N : Finset (Fin w) := (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0)
  have hcover : D ∪ {⟨w - 1, by omega⟩} = (Finset.univ : Finset (Fin w)) := by
    ext j
    constructor
    · intro hj
      simp
    · intro hj
      by_cases h : (j : ℕ) + 1 < w
      · simp [D, h]
      · have hw1 : (j : ℕ) = w - 1 := by
          have hjw : (j : ℕ) < w := j.isLt
          omega
        have hjlast : j = (⟨w - 1, by omega⟩ : Fin w) := by
          apply Fin.ext
          exact hw1
        simp [D, hjlast]
  have hzero : tailFn f (⟨w - 1, by omega⟩ : Fin w) = 0 := by
    simp [tailFn]
    intro h
    omega
  have hl : (∑ j : Fin w, tailFn f j) = ∑ j ∈ D, tailFn f j := by
    calc
      (∑ j : Fin w, tailFn f j) = ∑ j ∈ D ∪ {⟨w - 1, by omega⟩}, tailFn f j := by
            rw [← hcover]
      _ = (∑ j ∈ D, tailFn f j) + tailFn f (⟨w - 1, by omega⟩ : Fin w) := by
            rw [Finset.sum_union]
            · rfl
            · rw [Finset.disjoint_singleton_right]
              have h : (⟨w - 1, by omega⟩ : Fin w) ∉ D := by
                simp [D]
                omega
              exact h
      _ = ∑ j ∈ D, tailFn f j := by rw [hzero, add_zero]
  have hreindex : (∑ j ∈ D, tailFn f j) = ∑ i ∈ N, f i := by
    refine Finset.sum_bij (fun j hj => ⟨(j : ℕ) + 1, by simpa [D] using hj⟩) ?_ ?_ ?_ ?_
    · intro j hj
      simp [N]
    · intro a₁ ha₁ a₂ ha₂ h
      apply Fin.ext
      have hval : (a₁ : ℕ) + 1 = (a₂ : ℕ) + 1 := congrArg (fun t : Fin w => (t : ℕ)) h
      omega
    · intro i hi
      have hil : (i : ℕ) < w := i.isLt
      have hin : (i : ℕ) ≠ 0 := by simpa [N] using hi
      refine ⟨⟨(i : ℕ) - 1, by omega⟩, ?_, ?_⟩
      · have hmem : (i : ℕ) - 1 + 1 < w := by omega
        simp [D]
        exact hmem
      · apply Fin.ext
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hin))
    · intro j hj
      have hdj : (j : ℕ) + 1 < w := by simpa [D] using hj
      simp [tailFn, hdj]
  calc
    (∑ j : Fin w, tailFn f j) = ∑ j ∈ D, tailFn f j := hl
    _ = ∑ i ∈ N, f i := hreindex
    _ = ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0), f i := by rfl


/-- Head value of a multi shape is positive: `1 ≤ a`. -/
lemma multi_head_pos {w : ℕ} {x : PaddedCarrier F w} (hm : 1 ≤ (x.1 : ℕ)) (hw : 1 ≤ w)
    (hcond : PaddedCond F w x) :
    1 ≤ ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) := by
  -- positivity at the head index 0 (0 ≤ m since the shape is multi)
  exact hcond.2.1 (⟨0, by omega⟩ : Fin w) (by simpa using (Nat.zero_le (x.1 : ℕ)))

/-- Head value of a multi shape is at most `w - 1`: the tail holds at least one positive
entry, so the weight `w` exceeds the head value. -/
lemma multi_head_le {w : ℕ} {x : PaddedCarrier F w} (hm : 1 ≤ (x.1 : ℕ)) (hw : 1 ≤ w)
    (hcond : PaddedCond F w x) :
    ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) ≤ w - 1 := by
  classical
  let a : ℕ := ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)
  let f : Fin w → ℕ := fun i => ((x.2 i : Fin (Nat.card F + 1)) : ℕ)
  have hmw : (x.1 : ℕ) ≤ w - 1 := by
    have h := x.1.isLt
    omega
  -- sum_split_head with m := (x.1 : ℕ): w = a + (body sum)
  have hsplit := sum_split_head (w := w) (m := (x.1 : ℕ)) hm hmw f (by
    intro i hi
    exact hcond.2.2.1 i hi)
  -- the weight of the whole shape is w
  have hwsum : (∑ i : Fin w, f i) = w := by
    simpa [f] using hcond.1
  have hwbody : w = a + ∑ i ∈ (Finset.univ : Finset (Fin w)).filter
      (fun i : Fin w => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (x.1 : ℕ)), f i := by
    calc
      w = ∑ i : Fin w, f i := hwsum.symm
      _ = f (⟨0, by omega⟩ : Fin w) + ∑ i ∈ (Finset.univ : Finset (Fin w)).filter
            (fun i : Fin w => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (x.1 : ℕ)), f i := by
            simpa [a] using hsplit
      _ = a + ∑ i ∈ (Finset.univ : Finset (Fin w)).filter
            (fun i : Fin w => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (x.1 : ℕ)), f i := by rfl
  -- the body sum is at least 1 (its first entry f 1 is positive)
  have hbody : 1 ≤ ∑ i ∈ (Finset.univ : Finset (Fin w)).filter
      (fun i : Fin w => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (x.1 : ℕ)), f i := by
    have h1mem : (⟨1, by omega⟩ : Fin w) ∈ (Finset.univ : Finset (Fin w)).filter
        (fun i : Fin w => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (x.1 : ℕ)) := by
      simp
      exact hm
    have hf1 : 1 ≤ f (⟨1, by omega⟩ : Fin w) := by
      dsimp [f]
      exact hcond.2.1 (⟨1, by omega⟩ : Fin w) (by omega)
    have hle := Finset.single_le_sum (f := f) (fun j hj => Nat.zero_le (f j)) h1mem
    -- hle : f ⟨1⟩ ≤ ∑ over the filter, f ; combined with hf1
    omega
  omega


/-- Weight identity of the tail at the ℕ level: after removing the head, the sum of the
remaining entries (as ℕ values, via `tailFn`) is `w − a` where `a` is the head value. -/
lemma tail_weight {w : ℕ} {x : PaddedCarrier F w} (hm : 1 ≤ (x.1 : ℕ)) (hw : 1 ≤ w)
    (hcond : PaddedCond F w x) :
    (∑ j : Fin w, tailFn (fun i : Fin w => ((x.2 i : Fin (Nat.card F + 1)) : ℕ)) j) =
      w - ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) := by
  classical
  let a : ℕ := ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)
  let fn : Fin w → ℕ := fun i => ((x.2 i : Fin (Nat.card F + 1)) : ℕ)
  have htail := tailFn_sum (w := w) hw fn
  have hsplit := split_at_zero (w := w) hw fn
  have hwsum : (∑ i : Fin w, fn i) = w := by
    simpa [fn] using hcond.1
  have htotal : w = a + ∑ i ∈ (Finset.univ : Finset (Fin w)).filter
      (fun i : Fin w => (i : ℕ) ≠ 0), fn i := by
    calc
      w = ∑ i : Fin w, fn i := hwsum.symm
      _ = fn (⟨0, by omega⟩ : Fin w) + ∑ i ∈ (Finset.univ : Finset (Fin w)).filter
            (fun i : Fin w => (i : ℕ) ≠ 0), fn i := hsplit
      _ = a + ∑ i ∈ (Finset.univ : Finset (Fin w)).filter
            (fun i : Fin w => (i : ℕ) ≠ 0), fn i := by simpa [a, fn]
  calc
    (∑ j : Fin w, tailFn fn j) = ∑ i ∈ (Finset.univ : Finset (Fin w)).filter
        (fun i : Fin w => (i : ℕ) ≠ 0), fn i := htail
    _ = w - a := by omega


/-- Pointwise: the `ℕ`-value of the `Fin(q+1)`-valued tail equals the ℕ-valued tail. -/
lemma tailFn_val {w : ℕ} (f : Fin w → Fin (Nat.card F + 1)) (j : Fin w) :
    ((tailFn f j : Fin (Nat.card F + 1)) : ℕ) =
      tailFn (fun i : Fin w => ((f i : Fin (Nat.card F + 1)) : ℕ)) j := by
  classical
  by_cases hjd : (j : ℕ) + 1 < w
  · simp [tailFn, hjd]
  · simp [tailFn, hjd]


/-- The tail of a multi shape is a valid shape of weight `w − a` (a = head value):
depth-marker `m − 1`, entry function `tailFn x.2`. -/
lemma multi_tail_cond {w : ℕ} {x : PaddedCarrier F w} (hm : 1 ≤ (x.1 : ℕ)) (hw : 1 ≤ w)
    (hcond : PaddedCond F w x) :
    PaddedCond F (w - ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ))
      ⟨(⟨(x.1 : ℕ) - 1, by omega⟩ : Fin w), tailFn x.2⟩ := by
  classical
  let m : ℕ := (x.1 : ℕ)
  let a : ℕ := ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)
  let g : Fin w → Fin (Nat.card F + 1) := tailFn x.2
  let fn : Fin w → ℕ := fun i => ((x.2 i : Fin (Nat.card F + 1)) : ℕ)
  have hmw : m < w := x.1.isLt
  constructor
  · -- weight of the tail = w - a
    calc
      (∑ j : Fin w, ((g j : Fin (Nat.card F + 1)) : ℕ)) = ∑ j : Fin w, tailFn fn j := by
            apply Finset.sum_congr rfl
            intro j hj
            have hv := tailFn_val F x.2 j
            simpa [g, fn] using hv
      _ = w - a := by
            have hw' := tail_weight F (x := x) hm hw hcond
            simpa [fn, a] using hw'
  · constructor
    · -- positivity: j ≤ m-1 → 1 ≤ g j
      intro j hj
      have hjm' : (j : ℕ) ≤ m - 1 := by simpa [m] using hj
      have hj1 : (j : ℕ) + 1 ≤ m := by omega
      have hjd : (j : ℕ) + 1 < w := by omega
      have hpos : 1 ≤ ((x.2 ⟨(j : ℕ) + 1, hjd⟩ : Fin (Nat.card F + 1)) : ℕ) :=
        hcond.2.1 (⟨(j : ℕ) + 1, hjd⟩ : Fin w) (by omega)
      have hval : ((g j : Fin (Nat.card F + 1)) : ℕ) =
          ((x.2 ⟨(j : ℕ) + 1, hjd⟩ : Fin (Nat.card F + 1)) : ℕ) := by
        dsimp [g]
        simp [tailFn, hjd]
      rw [hval]
      exact hpos
    · constructor
      · -- zero beyond depth: m - 1 < j → g j = 0
        intro j hj
        have hjm0 : m - 1 < (j : ℕ) := by simpa [m] using hj
        have hjm : m ≤ (j : ℕ) := by omega
        by_cases hjd : (j : ℕ) + 1 < w
        · have hval : ((g j : Fin (Nat.card F + 1)) : ℕ) =
              ((x.2 ⟨(j : ℕ) + 1, hjd⟩ : Fin (Nat.card F + 1)) : ℕ) := by
              dsimp [g]
              simp [tailFn, hjd]
          rw [hval]
          have hmj : (x.1 : ℕ) < (j : ℕ) + 1 := by omega
          exact hcond.2.2.1 (⟨(j : ℕ) + 1, hjd⟩ : Fin w) (by simpa using hmj)
        · have hval : ((g j : Fin (Nat.card F + 1)) : ℕ) = 0 := by
              dsimp [g]
              simp [tailFn, hjd]
          exact hval
      · -- last entry (new index m-1) < q: its value is x.2 at original index m
        have hjd : (m - 1 : ℕ) + 1 < w := by omega
        have hval : ((g (⟨m - 1, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) =
            ((x.2 ⟨(m - 1) + 1, hjd⟩ : Fin (Nat.card F + 1)) : ℕ) := by
          dsimp [g]
          simp [tailFn, hjd]
        rw [hval]
        have hsame : x.2 ⟨(m - 1) + 1, hjd⟩ = x.2 ⟨m, hmw⟩ := by
          have hidx : (⟨(m - 1) + 1, hjd⟩ : Fin w) = ⟨m, hmw⟩ := by
            apply Fin.ext
            change (m - 1) + 1 = m
            have hm1 : 1 ≤ m := by simpa [m] using hm
            omega
          exact congrArg x.2 hidx
        rw [hsame]
        exact hcond.2.2.2


/-- The head value index `a − 1` of a multi shape fits into `Fin (min q (w−1))`. -/
lemma multi_head_index {w : ℕ} {x : PaddedCarrier F w} (hm : 1 ≤ (x.1 : ℕ)) (hw : 1 ≤ w)
    (hcond : PaddedCond F w x) :
    ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) - 1 <
      min (Nat.card F) (w - 1) := by
  let a : ℕ := ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)
  have hpos : 1 ≤ a := by simpa [a] using multi_head_pos F (x := x) hm hw hcond
  have hale : a ≤ w - 1 := by simpa [a] using multi_head_le F (x := x) hm hw hcond
  have haleq : a ≤ Nat.card F := by
    have hu : ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) < Nat.card F + 1 :=
      (x.2 (⟨0, by omega⟩ : Fin w)).isLt
    dsimp [a]
    omega
  omega


/-- Forward map of the multi-part decomposition: a multi shape `x` maps to the head index
`k = a−1` and the tail shape (a = head value). -/
noncomputable def multiFwd {w : ℕ} (hw : 1 ≤ w) (x : MultiT F w w) :
    (Σ k : Fin (min (Nat.card F) (w - 1)), ShapeT F w (w - (k : ℕ) - 1)) := by
  classical
  let x0 : PaddedCarrier F w := x.1
  let hcond : PaddedCond F w x0 := by simpa [x0] using x.2.1
  let hm : 1 ≤ (x0.1 : ℕ) := by simpa [x0] using x.2.2
  let a : ℕ := ((x0.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)
  let k : Fin (min (Nat.card F) (w - 1)) := ⟨a - 1, multi_head_index F (x := x0) hm hw hcond⟩
  refine ⟨k, ?_⟩
  have hk : w - (k : ℕ) - 1 = w - a := by
    dsimp [k, a]
    have hpos : 1 ≤ a := by simpa [a] using multi_head_pos F (x := x0) hm hw hcond
    omega
  refine ⟨⟨(⟨(x0.1 : ℕ) - 1, by omega⟩ : Fin w), tailFn x0.2⟩, ?_⟩
  rw [hk]
  exact multi_tail_cond F (x := x0) hm hw hcond


/-- Entry shift: prepends a head value, moving `g` up by one slot. -/
noncomputable def prependFn {w : ℕ} (hd : Fin (Nat.card F + 1))
    (g : Fin w → Fin (Nat.card F + 1)) : Fin w → Fin (Nat.card F + 1) :=
  fun i => if h : (i : ℕ) = 0 then hd
    else g ⟨(i : ℕ) - 1, by have hi := i.isLt; exact lt_of_le_of_lt (Nat.sub_le (i : ℕ) 1) hi⟩



/-- Sum of the prepended function (ℕ-values): the head plus the old sum, PROVIDED the last
slot of `g` vanishes (the prepend drops `g`'s index `w−1`). -/
lemma prepend_sum {w : ℕ} (hw : 1 ≤ w) (hd : ℕ) (g : Fin w → ℕ)
    (hz : g (⟨w - 1, by omega⟩ : Fin w) = 0) :
    (∑ i : Fin w, (if (i : ℕ) = 0 then hd else g ⟨(i : ℕ) - 1, by have hi := i.isLt; omega⟩)) =
      hd + ∑ j : Fin w, g j := by
  classical
  let fn : Fin w → ℕ := fun i => (if (i : ℕ) = 0 then hd else g ⟨(i : ℕ) - 1, by have hi := i.isLt; omega⟩)
  have hsplit := split_at_zero (w := w) hw fn
  have hd0 : fn (⟨0, by omega⟩ : Fin w) = hd := by simp [fn]
  have hshift : (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0), fn i) =
      ∑ j : Fin w, g j := by
    have hc : (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0), fn i) =
        ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0),
          g ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : (i : ℕ) ≠ 0 := by simpa using hi
      simp [fn, hin]
    let N' : Finset (Fin w) := (Finset.univ : Finset (Fin w)).filter (fun j : Fin w => (j : ℕ) < w - 1)
    have hre : (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0),
          g ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩) = ∑ i ∈ N', g i := by
      refine Finset.sum_bij (fun i hi => ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩) ?_ ?_ ?_ ?_
      · intro i hi
        have hin : (i : ℕ) ≠ 0 := by simpa using hi
        have hil := i.isLt
        simp [N']
        omega
      · intro a₁ ha₁ a₂ ha₂ h
        apply Fin.ext
        have hv : (a₁ : ℕ) - 1 = (a₂ : ℕ) - 1 := congrArg (fun t : Fin w => (t : ℕ)) h
        have hn1 : (a₁ : ℕ) ≠ 0 := by simpa using ha₁
        have hn2 : (a₂ : ℕ) ≠ 0 := by simpa using ha₂
        omega
      · intro j hj
        have hjl : (j : ℕ) < w - 1 := by simpa [N'] using hj
        refine ⟨⟨(j : ℕ) + 1, by omega⟩, ?_, ?_⟩
        · simp
        · apply Fin.ext
          change (j : ℕ) + 1 - 1 = (j : ℕ)
          omega
      · intro i hi
        rfl
    have hcover : N' ∪ {⟨w - 1, by omega⟩} = (Finset.univ : Finset (Fin w)) := by
      ext j
      constructor
      · intro hj
        simp
      · intro hj
        by_cases h : (j : ℕ) < w - 1
        · simp [N', h]
        · have hjl : (j : ℕ) = w - 1 := by
            have hjw : (j : ℕ) < w := j.isLt
            omega
          rw [Finset.mem_union]
          right
          rw [Finset.mem_singleton]
          apply Fin.ext
          exact hjl
    have hN' : (∑ i ∈ N', g i) = ∑ j : Fin w, g j := by
      calc
        (∑ i ∈ N', g i) = (∑ i ∈ N', g i) + g (⟨w - 1, by omega⟩ : Fin w) := by rw [hz, add_zero]
        _ = ∑ j ∈ N' ∪ {⟨w - 1, by omega⟩}, g j := by
              rw [Finset.sum_union]
              · rfl
              · rw [Finset.disjoint_singleton_right]
                simp [N']
        _ = ∑ j : Fin w, g j := by rw [hcover]
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0), fn i)
          = ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0),
              g ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ := hc
      _ = ∑ i ∈ N', g i := hre
      _ = ∑ j : Fin w, g j := hN'
  calc
    (∑ i : Fin w, (if (i : ℕ) = 0 then hd else g ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩))
        = ∑ i : Fin w, fn i := by rfl
    _ = fn (⟨0, by omega⟩ : Fin w) + ∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i : Fin w => (i : ℕ) ≠ 0), fn i := hsplit
    _ = hd + ∑ j : Fin w, g j := by rw [hd0, hshift]




/-- Inverse map: given a head index `k` and a tail shape of weight `w − k − 1`, prepend the
head value `(k : ℕ) + 1` to obtain a multi shape of weight `w`. -/
noncomputable def multiInv {w : ℕ} (hw : 1 ≤ w)
    (t : Σ k : Fin (min (Nat.card F) (w - 1)), ShapeT F w (w - (k : ℕ) - 1)) :
    MultiT F w w := by
  classical
  rcases t with ⟨k, y⟩
  rcases y with ⟨y, hcond⟩
  let my : ℕ := (y.1 : ℕ)
  let hd : Fin (Nat.card F + 1) := ⟨(k : ℕ) + 1, by
      have hk := k.isLt
      omega⟩
  have hdepth : (y.1 : ℕ) + 1 ≤ w - (k : ℕ) - 1 := by
    have h := ShapeT_depth_le F (⟨y, hcond⟩ : ShapeT F w (w - (k : ℕ) - 1))
    simpa using h
  have hmx : my + 1 < w := by
    dsimp [my]
    have h2 : w - (k : ℕ) - 1 ≤ w - 1 := by
      have hk0 : 0 ≤ (k : ℕ) := Nat.zero_le _
      omega
    have h3 : (y.1 : ℕ) + 1 ≤ w - 1 := le_trans hdepth h2
    omega
  let x : PaddedCarrier F w := ⟨⟨my + 1, hmx⟩, prependFn F hd y.2⟩
  let g : Fin w → ℕ := fun i => ((y.2 i : Fin (Nat.card F + 1)) : ℕ)
  have hweight : (∑ i : Fin w, ((x.2 i : Fin (Nat.card F + 1)) : ℕ)) = w := by
    let pf : Fin w → ℕ := fun i => (if (i : ℕ) = 0 then ((hd : Fin (Nat.card F + 1)) : ℕ)
      else g ⟨(i : ℕ) - 1, by have hi := i.isLt; omega⟩)
    have hpoint : ∀ i : Fin w, ((prependFn F hd y.2 i : Fin (Nat.card F + 1)) : ℕ) = pf i := by
      intro i
      by_cases h0 : (i : ℕ) = 0
      · simp [prependFn, pf, h0]
      · have hin : (i : ℕ) ≠ 0 := h0
        simp [prependFn, pf, hin, g]
    have hz : g (⟨w - 1, by omega⟩ : Fin w) = 0 := by
      dsimp [g]
      have hb : (y.1 : ℕ) < w - 1 := by
        have hk0 : 0 ≤ (k : ℕ) := Nat.zero_le _
        omega
      exact hcond.2.2.1 (⟨w - 1, by omega⟩ : Fin w) hb
    have hs := prepend_sum (w := w) hw ((hd : Fin (Nat.card F + 1)) : ℕ) g hz
    have hhd : (((hd : Fin (Nat.card F + 1)) : ℕ)) = (k : ℕ) + 1 := rfl
    have hy : (∑ i : Fin w, g i) = w - (k : ℕ) - 1 := by simpa [g] using hcond.1
    calc
      (∑ i : Fin w, ((x.2 i : Fin (Nat.card F + 1)) : ℕ)) = ∑ i : Fin w, pf i := by
            dsimp [x]
            apply Finset.sum_congr rfl
            intro i hi
            exact hpoint i
      _ = ((hd : Fin (Nat.card F + 1)) : ℕ) + ∑ i : Fin w, g i := hs
      _ = w := by
            have hkl := k.isLt
            rw [hhd, hy]
            omega
  refine ⟨⟨⟨my + 1, hmx⟩, prependFn F hd y.2⟩, ?_, ?_⟩
  · constructor
    · exact hweight
    · constructor
      · intro i hi
        change 1 ≤ (((prependFn F hd y.2 i : Fin (Nat.card F + 1)) : ℕ))
        by_cases h0 : (i : ℕ) = 0
        · have hval : (prependFn F hd y.2 i : Fin (Nat.card F + 1)) = hd := by
            simp [prependFn, h0]
          rw [hval]
          simp [hd]
        · have hin : (i : ℕ) ≠ 0 := h0
          have hval : (prependFn F hd y.2 i : Fin (Nat.card F + 1)) =
              y.2 ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ := by
            simp [prependFn, hin]
          rw [hval]
          have hle : ((⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ : Fin w) : ℕ) ≤ (y.1 : ℕ) := by
            change (i : ℕ) - 1 ≤ (y.1 : ℕ)
            dsimp [my] at hi
            omega
          have hpos := hcond.2.1 (⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ : Fin w) hle
          simpa [g] using hpos
      · constructor
        · intro i hi
          change (((prependFn F hd y.2 i : Fin (Nat.card F + 1)) : ℕ)) = 0
          have hgt : my + 1 < (i : ℕ) := by
            simpa [my] using hi
          have hin : (i : ℕ) ≠ 0 := by omega
          have hval : (prependFn F hd y.2 i : Fin (Nat.card F + 1)) =
              y.2 ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ := by
            simp [prependFn, hin]
          rw [hval]
          have hlt : (y.1 : ℕ) < ((⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ : Fin w) : ℕ) := by
            change (y.1 : ℕ) < (i : ℕ) - 1
            dsimp [my] at hi
            omega
          have hz' := hcond.2.2.1 (⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ : Fin w) hlt
          exact hz'
        · change (((prependFn F hd y.2 (⟨my + 1, hmx⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)) <
              Nat.card F
          have hval : (prependFn F hd y.2 (⟨my + 1, hmx⟩ : Fin w) : Fin (Nat.card F + 1)) =
              y.2 ⟨my, by have h := (⟨my + 1, hmx⟩ : Fin w).isLt; omega⟩ := by
            have hin : (my + 1 : ℕ) ≠ 0 := by omega
            have hidx : ((⟨my + 1, hmx⟩ : Fin w) : ℕ) - 1 = my := by
              change my + 1 - 1 = my
              omega
            simp [prependFn, hin, hidx]
          rw [hval]
          have hlast := hcond.2.2.2
          simpa [my] using hlast
  · dsimp [my]
    omega


/-- Shifting back: for a non-zero index `i`, the tail at `i−1` recovers `f i`. -/
lemma tailFn_value_shift {w : ℕ} {R : Type*} [Zero R] (f : Fin w → R) (i : Fin w)
    (hi : (i : ℕ) ≠ 0) :
    tailFn f ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩ = f i := by
  classical
  let j : Fin w := ⟨(i : ℕ) - 1, by have hil := i.isLt; omega⟩
  have hji : (j : ℕ) + 1 = (i : ℕ) := by
    dsimp [j]
    change (i : ℕ) - 1 + 1 = (i : ℕ)
    have hi1 : 1 ≤ (i : ℕ) := by omega
    omega
  have hlt : (j : ℕ) + 1 < w := by
    rw [hji]
    exact i.isLt
  calc
    tailFn f j = f ⟨(j : ℕ) + 1, hlt⟩ := by
          simp [tailFn, hlt]
    _ = f i := by
          congr 1
          apply Fin.ext
          exact hji


/-- The prepended head value of `multiInv (multiFwd x)` recovers the head entry of `x`. -/
lemma multiInv_head {w : ℕ} {x : PaddedCarrier F w} (hm : 1 ≤ (x.1 : ℕ)) (hw : 1 ≤ w)
    (hcond : PaddedCond F w x) :
    let a : ℕ := ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)
    let k : Fin (min (Nat.card F) (w - 1)) := ⟨a - 1, multi_head_index F (x := x) hm hw hcond⟩
    (⟨(k : ℕ) + 1, by
        have hk := k.isLt
        omega⟩ : Fin (Nat.card F + 1)) = x.2 (⟨0, by omega⟩ : Fin w) := by
  classical
  let a : ℕ := ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)
  let k : Fin (min (Nat.card F) (w - 1)) := ⟨a - 1, multi_head_index F (x := x) hm hw hcond⟩
  apply Fin.ext
  have hpos : 1 ≤ a := by simpa [a] using multi_head_pos F (x := x) hm hw hcond
  have hk1 : (k : ℕ) + 1 = a := by
    dsimp [k]
    change a - 1 + 1 = a
    omega
  calc
    (((⟨(k : ℕ) + 1, by
        have hk := k.isLt
        omega⟩ : Fin (Nat.card F + 1)) : ℕ)) = (k : ℕ) + 1 := rfl
    _ = a := hk1
    _ = ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) := by rfl

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma multi_left {w : ℕ} (hw : 1 ≤ w) (x : MultiT F w w) :
    multiInv F hw (multiFwd F hw x) = x := by
  classical
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨hcond, hm⟩
  apply Subtype.ext
  dsimp [multiFwd, multiInv]
  apply Prod.ext
  · apply Fin.ext
    change (↑x.1 : ℕ) - 1 + 1 = (↑x.1 : ℕ)
    omega
  · funext i
    by_cases h0 : (i : ℕ) = 0
    · have hin0 : i = (⟨0, by omega⟩ : Fin w) := by
        apply Fin.ext
        change (i : ℕ) = 0
        exact h0
      apply Fin.ext
      rw [hin0]
      simp [prependFn]
      change ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) - 1 + 1 =
        ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ)
      have hpos : 1 ≤ ((x.2 (⟨0, by omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) := by
        simpa using multi_head_pos F (x := x) hm hw hcond
      omega
    · have hin : (i : ℕ) ≠ 0 := h0
      simp [prependFn, hin]
      exact tailFn_value_shift (R := Fin (Nat.card F + 1)) x.2 i hin

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma multi_right {w : ℕ} (hw : 1 ≤ w)
    (t : Σ k : Fin (min (Nat.card F) (w - 1)), ShapeT F w (w - (k : ℕ) - 1)) :
    multiFwd F hw (multiInv F hw t) = t := by
  classical
  rcases t with ⟨k, y⟩
  rcases k with ⟨kval, hklt⟩
  rcases y with ⟨y, hcond⟩
  dsimp [multiFwd, multiInv]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    by_cases hj : (j : ℕ) + 1 < w
    · simp [tailFn, hj]
      have hin : (j : ℕ) + 1 ≠ 0 := by omega
      simp [prependFn, hin]
    · simp [tailFn, hj]
      have hzero : y.2 j = (0 : Fin (Nat.card F + 1)) := by
        have hjl : (j : ℕ) + 1 = w := by
          have hjw : (j : ℕ) < w := j.isLt
          omega
        have hdepth : (y.1 : ℕ) + 1 ≤ w - kval - 1 := by
          have h := ShapeT_depth_le F (⟨y, hcond⟩ : ShapeT F w (w - kval - 1))
          simpa using h
        have hlt : (y.1 : ℕ) < (j : ℕ) := by omega
        apply Fin.ext
        have hz := hcond.2.2.1 j hlt
        simpa using hz
      rw [hzero]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `MultiT F w w` is in bijection with pairs `(k, tail)` where `k` is the head value minus
one and the tail is a shape of weight `w − k − 1`. -/
noncomputable def multiEquiv {w : ℕ} (hw : 1 ≤ w) :
    MultiT F w w ≃ (Σ k : Fin (min (Nat.card F) (w - 1)), ShapeT F w (w - (k : ℕ) - 1)) where
  toFun := fun x => multiFwd F hw x
  invFun := fun t => multiInv F hw t
  left_inv := by
    intro x
    exact multi_left F hw x
  right_inv := by
    intro t
    exact multi_right F hw t

/-- The number of multi shapes of weight `w` is the sum over `k` of the number of tails. -/
lemma multiT_card {w : ℕ} (hw : 1 ≤ w) :
    Nat.card (MultiT F w w) =
      ∑ k : Fin (min (Nat.card F) (w - 1)), Nat.card (ShapeT F w (w - (k : ℕ) - 1)) := by
  classical
  rw [← Nat.card_sigma]
  exact Nat.card_congr (multiEquiv F hw)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Values of a padded shape of weight `v` vanish at indices `i` with `v ≤ i`. -/
lemma ShapeT_zero_ge {w v : ℕ} (x : ShapeT F w v) {i : Fin w} (hi : v ≤ (i : ℕ)) :
    ((x.1.2 i : Fin (Nat.card F + 1)) : ℕ) = 0 := by
  have hd := ShapeT_depth_le F x
  have hb : (x.1.1 : ℕ) < (i : ℕ) := by
    omega
  exact x.2.2.2.1 i hb

/-- Sum over `Fin w` of a function vanishing at indices `≥ v` equals the sum over `Fin v`. -/
lemma sum_fin_cut {w v : ℕ} (h : v ≤ w) (g : Fin w → ℕ)
    (hz : ∀ i : Fin w, v ≤ (i : ℕ) → g i = 0) :
    (∑ i : Fin w, g i) = ∑ j : Fin v, g ⟨(j : ℕ), by have hj := j.isLt; omega⟩ := by
  classical
  let P : Fin w → Prop := fun i => (i : ℕ) < v
  have hz' : (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i => ¬ P i), g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiP : ¬ P i := by simpa using hi
    have hge : v ≤ (i : ℕ) := by
      dsimp [P] at hiP
      omega
    exact hz i hge
  have hb : (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i => P i), g i) =
      ∑ j : Fin v, g ⟨(j : ℕ), by have hj := j.isLt; omega⟩ := by
    refine Finset.sum_bij (fun i hi => ⟨(i : ℕ), by
        have hiP : P i := by simpa using hi
        dsimp [P] at hiP
        exact hiP⟩) ?_ ?_ ?_ ?_
    · intro i hi
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      apply Fin.ext
      exact congrArg (fun t : Fin v => (t : ℕ)) h
    · intro j hj
      refine ⟨⟨(j : ℕ), by have hj' := j.isLt; exact lt_of_lt_of_le hj' h⟩, ?_, ?_⟩
      · have hP : P (⟨(j : ℕ), by have hj' := j.isLt; exact lt_of_lt_of_le hj' h⟩ : Fin w) := by
          dsimp [P]
          exact j.isLt
        simpa using hP
      · apply Fin.ext
        rfl
    · intro i hi
      rfl
  calc
    (∑ i : Fin w, g i) = (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i => P i), g i) +
        (∑ i ∈ (Finset.univ : Finset (Fin w)).filter (fun i => ¬ P i), g i) := by
          have hsp := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin w))) (p := P) (f := g)
          simpa [add_comm, add_left_comm, add_assoc] using hsp.symm
    _ = ∑ j : Fin v, g ⟨(j : ℕ), by have hj := j.isLt; omega⟩ := by
          rw [hz', add_zero]
          exact hb

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Truncation of a shape of weight `v` padded to length `w` (for `v ≤ w`) down to length `v`. -/
noncomputable def truncShape {w v : ℕ} (h : v ≤ w) (x : ShapeT F w v) : ShapeT F v v := by
  classical
  let m : Fin v := ⟨(x.1.1 : ℕ), by have hd := ShapeT_depth_le F x; omega⟩
  let g : Fin v → Fin (Nat.card F + 1) := fun i => x.1.2 ⟨(i : ℕ), by have hi := i.isLt; omega⟩
  refine ⟨⟨m, g⟩, ?_⟩
  constructor
  · change (∑ i : Fin v, ((x.1.2 (⟨(i : ℕ), by have hi := i.isLt; omega⟩ : Fin w)
        : Fin (Nat.card F + 1)) : ℕ)) = v
    have hcut := sum_fin_cut h (fun i : Fin w => ((x.1.2 i : Fin (Nat.card F + 1)) : ℕ))
      (fun i hi => ShapeT_zero_ge F x (i := i) hi)
    rw [← hcut]
    exact x.2.1
  · constructor
    · intro i hi
      change 1 ≤ ((x.1.2 (⟨(i : ℕ), by have hi' := i.isLt; omega⟩ : Fin w)
          : Fin (Nat.card F + 1)) : ℕ)
      have hpos := x.2.2.1 (⟨(i : ℕ), by have hi' := i.isLt; omega⟩ : Fin w) hi
      exact hpos
    · constructor
      · intro i hi
        change ((x.1.2 (⟨(i : ℕ), by have hi' := i.isLt; omega⟩ : Fin w)
            : Fin (Nat.card F + 1)) : ℕ) = 0
        have hz := x.2.2.2.1 (⟨(i : ℕ), by have hi' := i.isLt; omega⟩ : Fin w) hi
        exact hz
      · change ((x.1.2 (⟨(x.1.1 : ℕ), by
            have hd := ShapeT_depth_le F x
            omega⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) < Nat.card F
        have hlast := x.2.2.2.2
        simpa using hlast

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Padding of a shape of weight `v` (length `v`) to length `w ≥ v` by zeros. -/
noncomputable def extendShape {w v : ℕ} (h : v ≤ w) (x : ShapeT F v v) : ShapeT F w v := by
  classical
  let m : Fin w := ⟨(x.1.1 : ℕ), by
    have hm := (x.1.1 : Fin v).isLt
    exact lt_of_lt_of_le hm h⟩
  let g : Fin w → Fin (Nat.card F + 1) := fun i =>
    if hiv : (i : ℕ) < v then x.1.2 ⟨(i : ℕ), hiv⟩ else (0 : Fin (Nat.card F + 1))
  refine ⟨⟨m, g⟩, ?_⟩
  constructor
  · change (∑ i : Fin w, ((g i : Fin (Nat.card F + 1)) : ℕ)) = v
    have hz : ∀ i : Fin w, v ≤ (i : ℕ) → ((g i : Fin (Nat.card F + 1)) : ℕ) = 0 := by
      intro i hi
      dsimp [g]
      have hge : ¬ (i : ℕ) < v := by omega
      simp [hge]
    have hcut := sum_fin_cut h (fun i : Fin w => ((g i : Fin (Nat.card F + 1)) : ℕ)) hz
    calc
      (∑ i : Fin w, ((g i : Fin (Nat.card F + 1)) : ℕ))
          = ∑ j : Fin v, ((g (⟨(j : ℕ), by have hj := j.isLt; omega⟩ : Fin w)
              : Fin (Nat.card F + 1)) : ℕ) := hcut
      _ = ∑ j : Fin v, ((x.1.2 j : Fin (Nat.card F + 1)) : ℕ) := by
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [g]
            have hjv : (j : ℕ) < v := j.isLt
            simp [hjv]
      _ = v := x.2.1
  · constructor
    · intro i hi
      change 1 ≤ ((g i : Fin (Nat.card F + 1)) : ℕ)
      dsimp [g]
      have hiv : (i : ℕ) < v := by
        have hmv : (x.1.1 : ℕ) < v := (x.1.1 : Fin v).isLt
        change (i : ℕ) ≤ (x.1.1 : ℕ) at hi
        omega
      have hpos := x.2.2.1 ⟨(i : ℕ), hiv⟩ (by change (i : ℕ) ≤ (x.1.1 : ℕ); omega)
      have hval : (if hiv : (i : ℕ) < v then x.1.2 ⟨(i : ℕ), hiv⟩ else (0 : Fin (Nat.card F + 1)))
          = x.1.2 ⟨(i : ℕ), hiv⟩ := by
        simp [hiv]
      rw [hval]
      exact hpos
    · constructor
      · intro i hi
        change ((g i : Fin (Nat.card F + 1)) : ℕ) = 0
        dsimp [g]
        by_cases hiv : (i : ℕ) < v
        · have hz := x.2.2.2.1 ⟨(i : ℕ), hiv⟩ (by change (x.1.1 : ℕ) < (i : ℕ); omega)
          have hval : (if hiv : (i : ℕ) < v then x.1.2 ⟨(i : ℕ), hiv⟩ else (0 : Fin (Nat.card F + 1)))
              = x.1.2 ⟨(i : ℕ), hiv⟩ := by
            simp [hiv]
          rw [hval]
          exact hz
        · have hge : ¬ (i : ℕ) < v := hiv
          simp [hge]
      · change ((g (⟨(m : ℕ), m.isLt⟩ : Fin w) : Fin (Nat.card F + 1)) : ℕ) < Nat.card F
        dsimp [g]
        have hmv : (m : ℕ) < v := by
          dsimp [m]
          exact (x.1.1 : Fin v).isLt
        simp [hmv]
        have hlast := x.2.2.2.2
        simpa using hlast

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Padding then truncating a shape recovers it. -/
lemma extend_trunc {w v : ℕ} (h : v ≤ w) (x : ShapeT F w v) :
    extendShape F h (truncShape F h x) = x := by
  classical
  rcases x with ⟨x, hcond⟩
  apply Subtype.ext
  dsimp [extendShape, truncShape]
  apply Prod.ext
  · apply Fin.ext
    rfl
  · funext i
    by_cases hiv : (i : ℕ) < v
    · simp [hiv]
    · have hz := ShapeT_zero_ge F (⟨x, hcond⟩ : ShapeT F w v) (i := i) (by omega)
      simp [hiv]
      apply Fin.ext
      simpa using hz.symm

/-- Truncating then padding a shape recovers it. -/
lemma trunc_extend {w v : ℕ} (h : v ≤ w) (x : ShapeT F v v) :
    truncShape F h (extendShape F h x) = x := by
  classical
  rcases x with ⟨x, hcond⟩
  apply Subtype.ext
  dsimp [extendShape, truncShape]
  apply Prod.ext
  · apply Fin.ext
    rfl
  · funext i
    have hiv : (i : ℕ) < v := i.isLt
    simp [hiv]

/-- Shapes of weight `v` are in bijection with their padding to any length `w ≥ v`. -/
noncomputable def shapePadEquiv {w v : ℕ} (h : v ≤ w) :
    ShapeT F w v ≃ ShapeT F v v where
  toFun := fun x => truncShape F h x
  invFun := fun x => extendShape F h x
  left_inv := by
    intro x
    exact extend_trunc F h x
  right_inv := by
    intro x
    exact trunc_extend F h x

/-- The number of weight-`v` shapes does not depend on the padding length `w ≥ v`. -/
lemma ShapeT_card_pad {w v : ℕ} (h : v ≤ w) :
    Nat.card (ShapeT F w v) = Nat.card (ShapeT F v v) := by
  classical
  exact Nat.card_congr (shapePadEquiv F h)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Recursion for the number of Hoffman shapes of weight `w`: a single shape plus
multi shapes (split at the head entry `k + 1`). -/
lemma hoffCount_rec {w : ℕ} (hw : 1 ≤ w) :
    hoffCount F w = (if w < Nat.card F then 1 else 0) +
      ∑ k : Fin (min (Nat.card F) (w - 1)), hoffCount F (w - (k : ℕ) - 1) := by
  classical
  rw [hoffCount_eq_single_add_multi F w]
  rw [singleT_card F hw]
  have hm := multiT_card F hw
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  unfold hoffCount
  exact ShapeT_card_pad F (Nat.sub_le (w) ((k : ℕ) + 1))

end ZagierHoffmanPositiveChar


namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `hoffCount` recursion, expressed as a sum over `Finset.range`. -/
lemma hoffCount_rec_range {w : ℕ} (hw : 1 ≤ w) :
    hoffCount F w = (if w < Nat.card F then 1 else 0) +
      ∑ i ∈ Finset.range (min (Nat.card F) (w - 1)), hoffCount F (w - i - 1) := by
  classical
  rw [hoffCount_rec F hw]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => hoffCount F (w - i - 1)) (min (Nat.card F) (w - 1))]

/-- `Σ_{i < n} 2^i = 2^n − 1`. -/
lemma pow_two_sum_range (n : ℕ) : (∑ i ∈ Finset.range n, (2 : ℕ) ^ i) = 2 ^ n - 1 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      have hA : 1 ≤ 2 ^ n := by
        exact Nat.succ_le_of_lt (pow_pos (by norm_num) n)
      rw [pow_succ]
      omega

/-- `Σ_{i < n} 2^{n−1−i} = 2^n − 1`. -/
lemma pow_two_sum_reflect_range (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℕ) ^ (n - 1 - i)) = 2 ^ n - 1 := by
  classical
  rw [Finset.sum_range_reflect (fun j : ℕ => (2 : ℕ) ^ j) n]
  exact pow_two_sum_range n

/-- The finite field has at least two elements. -/
lemma nat_card_ge_two : 2 ≤ Nat.card F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- Closed form of `d` below `q`. -/
lemma d_eq_pow_two {m : ℕ} (hm : 1 ≤ m) (hmq : m < Nat.card F) :
    d F m = 2 ^ (m - 1) := by
  classical
  unfold d
  have hne0 : m ≠ 0 := by omega
  have hle : m ≤ Nat.card F - 1 := by omega
  rw [if_neg hne0]
  rw [if_pos hle]

/-- Closed form of `d` at `q`. -/
lemma d_eq_pow_two_sub_one : d F (Nat.card F) = 2 ^ (Nat.card F - 1) - 1 := by
  classical
  unfold d
  have hq2 := nat_card_ge_two F
  have hne0 : Nat.card F ≠ 0 := by omega
  have hgt : ¬ Nat.card F ≤ Nat.card F - 1 := by omega
  rw [if_neg hne0]
  rw [if_neg hgt]
  have heq : Nat.card F = Nat.card F := rfl
  rw [if_pos heq]

/-- Number of Hoffman shapes of weight `w` equals the paper's `d(w)` (for `w ≥ 1`). -/
lemma hoffCount_eq_d : ∀ w : ℕ, 1 ≤ w → hoffCount F w = d F w := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
      intro hw
      by_cases hwq : w < Nat.card F
      · -- 1 ≤ w < q
        rw [hoffCount_rec_range F hw]
        rw [if_pos hwq]
        rw [Nat.min_eq_right (by omega : w - 1 ≤ Nat.card F)]
        have hsum : (∑ i ∈ Finset.range (w - 1), hoffCount F (w - i - 1)) = 2 ^ (w - 1) - 1 := by
          have hstep : ∀ i ∈ Finset.range (w - 1), hoffCount F (w - i - 1) = (2 : ℕ) ^ ((w - 1) - 1 - i) := by
            intro i hi
            have him : i < w - 1 := by simpa using hi
            have hterm : 1 ≤ w - i - 1 := by omega
            have hwlt : w - i - 1 < w := by omega
            rw [ih (w - i - 1) hwlt hterm]
            have hd := d_eq_pow_two F hterm (by omega : w - i - 1 < Nat.card F)
            rw [hd]
            congr 1
            omega
          rw [Finset.sum_congr rfl hstep]
          rw [pow_two_sum_reflect_range (w - 1)]
        rw [hsum]
        rw [d_eq_pow_two F hw hwq]
        have hp : 1 ≤ 2 ^ (w - 1) := by
          exact Nat.succ_le_of_lt (pow_pos (by norm_num) (w - 1))
        omega
      · -- w ≥ q
        by_cases hweq : w = Nat.card F
        · -- w = q
          subst w
          rw [hoffCount_rec_range F hw]
          rw [Nat.min_eq_right (by omega : Nat.card F - 1 ≤ Nat.card F)]
          have hif : (if Nat.card F < Nat.card F then 1 else 0) = 0 := by simp
          rw [hif]
          have hsum : (∑ i ∈ Finset.range (Nat.card F - 1), hoffCount F (Nat.card F - i - 1)) =
              2 ^ (Nat.card F - 1) - 1 := by
            have hstep : ∀ i ∈ Finset.range (Nat.card F - 1),
                hoffCount F (Nat.card F - i - 1) = (2 : ℕ) ^ ((Nat.card F - 1) - 1 - i) := by
              intro i hi
              have him : i < Nat.card F - 1 := by simpa using hi
              have hterm : 1 ≤ Nat.card F - i - 1 := by omega
              have hwlt : Nat.card F - i - 1 < Nat.card F := by omega
              rw [ih (Nat.card F - i - 1) hwlt hterm]
              have hd := d_eq_pow_two F hterm (by omega : Nat.card F - i - 1 < Nat.card F)
              rw [hd]
              congr 1
              omega
            rw [Finset.sum_congr rfl hstep]
            rw [pow_two_sum_reflect_range (Nat.card F - 1)]
          rw [hsum]
          rw [d_eq_pow_two_sub_one F]
          omega
        · -- w > q
          have hwg : Nat.card F < w := by omega
          rw [hoffCount_rec_range F hw]
          rw [Nat.min_eq_left (by omega : Nat.card F ≤ w - 1)]
          have hif : (if w < Nat.card F then 1 else 0) = 0 := by simp [hwq]
          rw [hif]
          have hsum : (∑ i ∈ Finset.range (Nat.card F), hoffCount F (w - i - 1)) =
              ∑ i ∈ Finset.range (Nat.card F), d F (w - i - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            have him : i < Nat.card F := by simpa using hi
            have hterm : 1 ≤ w - i - 1 := by omega
            have hwlt : w - i - 1 < w := by omega
            exact ih (w - i - 1) hwlt hterm
          rw [hsum]
          rw [zero_add]
          conv =>
            rhs
            unfold d
          have hne0 : w ≠ 0 := by omega
          have hle : ¬ w ≤ Nat.card F - 1 := by omega
          have hne : w ≠ Nat.card F := by omega
          rw [if_neg hne0]
          rw [if_neg hle]
          rw [if_neg hne]
          apply Finset.sum_congr rfl
          intro i hi
          congr 1

end ZagierHoffmanPositiveChar


namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Pad the entries of a Hoffman tuple (values `≤ q`, last `< q`) to a function over `Fin w`. -/
noncomputable def tupleEntry {w r : ℕ} (hr1 : 1 ≤ r) (s : Fin r → ℕ+)
    (hfirst : ∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ Nat.card F)
    (hlast : (s ⟨r - 1, by omega⟩ : ℕ) < Nat.card F) :
    Fin w → Fin (Nat.card F + 1) :=
  fun i => if hiv : (i : ℕ) < r then
      ⟨(s ⟨(i : ℕ), hiv⟩ : ℕ), by
        by_cases hi : (i : ℕ) < r - 1
        · have hb := hfirst ⟨(i : ℕ), hiv⟩ hi
          omega
        · have hiq : (i : ℕ) = r - 1 := by
            have hil := i.isLt
            omega
          have hb : (s ⟨(i : ℕ), hiv⟩ : ℕ) < Nat.card F := by
            simpa [hiq] using hlast
          omega⟩
    else (0 : Fin (Nat.card F + 1))

/-- Value of `tupleEntry` below `r`. -/
lemma tupleEntry_val_lt {w r : ℕ} (hr1 : 1 ≤ r) (s : Fin r → ℕ+)
    (hfirst : ∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ Nat.card F)
    (hlast : (s ⟨r - 1, by omega⟩ : ℕ) < Nat.card F) {i : Fin w} (hiv : (i : ℕ) < r) :
    ((tupleEntry F hr1 s hfirst hlast i : Fin (Nat.card F + 1)) : ℕ) = (s ⟨(i : ℕ), hiv⟩ : ℕ) := by
  simp [tupleEntry, hiv]

/-- Value of `tupleEntry` at indices `≥ r` vanishes. -/
lemma tupleEntry_val_ge {w r : ℕ} (hr1 : 1 ≤ r) (s : Fin r → ℕ+)
    (hfirst : ∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ Nat.card F)
    (hlast : (s ⟨r - 1, by omega⟩ : ℕ) < Nat.card F) {i : Fin w} (hge : r ≤ (i : ℕ)) :
    ((tupleEntry F hr1 s hfirst hlast i : Fin (Nat.card F + 1)) : ℕ) = 0 := by
  have h : ¬ (i : ℕ) < r := by omega
  simp [tupleEntry, h]

/-- A weight-`w` Hoffman tuple `(r,s)` (`r ≥ 1`, entries `≤ q` except the last `< q`)
converted to the padded shape of `ShapeT F w w`. -/
noncomputable def tupleShape (w : ℕ) (hw : 1 ≤ w) (r : ℕ) (hr1 : 1 ≤ r) (hrw : r ≤ w)
    (s : Fin r → ℕ+) (hsum : (∑ i : Fin r, ((s i : ℕ+)) : ℕ) = w)
    (hfirst : ∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ Nat.card F)
    (hlast : (s ⟨r - 1, by omega⟩ : ℕ) < Nat.card F) : ShapeT F w w := by
  classical
  let m : Fin w := ⟨r - 1, by omega⟩
  let g : Fin w → Fin (Nat.card F + 1) := tupleEntry F hr1 s hfirst hlast
  refine ⟨⟨m, g⟩, ?_⟩
  constructor
  · change (∑ i : Fin w, ((g i : Fin (Nat.card F + 1)) : ℕ)) = w
    have hz : ∀ i : Fin w, r ≤ (i : ℕ) → ((g i : Fin (Nat.card F + 1)) : ℕ) = 0 := by
      intro i hi
      exact tupleEntry_val_ge F hr1 s hfirst hlast hi
    have hcut := sum_fin_cut hrw (fun i : Fin w => ((g i : Fin (Nat.card F + 1)) : ℕ)) hz
    calc
      (∑ i : Fin w, ((g i : Fin (Nat.card F + 1)) : ℕ))
          = ∑ j : Fin r, ((g ⟨(j : ℕ), by have hj := j.isLt; omega⟩ : Fin (Nat.card F + 1)) : ℕ) := hcut
      _ = (∑ j : Fin r, (s j : ℕ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact tupleEntry_val_lt F hr1 s hfirst hlast j.isLt
      _ = w := hsum
  · constructor
    · intro i hi
      change 1 ≤ ((g i : Fin (Nat.card F + 1)) : ℕ)
      have hiv : (i : ℕ) < r := by
        dsimp [m] at hi
        omega
      have hv := tupleEntry_val_lt F hr1 s hfirst hlast hiv
      rw [hv]
      exact Nat.succ_le_of_lt (s ⟨(i : ℕ), hiv⟩).pos
    · constructor
      · intro i hi
        change ((g i : Fin (Nat.card F + 1)) : ℕ) = 0
        have hge : r ≤ (i : ℕ) := by
          dsimp [m] at hi
          omega
        exact tupleEntry_val_ge F hr1 s hfirst hlast hge
      · change ((g ⟨(m : ℕ), m.isLt⟩ : Fin (Nat.card F + 1)) : ℕ) < Nat.card F
        have hmv : (m : ℕ) < r := by
          dsimp [m]
          omega
        have hv := tupleEntry_val_lt F hr1 s hfirst hlast hmv
        rw [hv]
        simpa using hlast

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The depth of the shape of a tuple is `r`. -/
lemma tupleShape_depth {w : ℕ} (hw : 1 ≤ w) {r : ℕ} (hr1 : 1 ≤ r) (hrw : r ≤ w)
    (s : Fin r → ℕ+) (hsum : (∑ i : Fin r, ((s i : ℕ+)) : ℕ) = w)
    (hfirst : ∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ Nat.card F)
    (hlast : (s ⟨r - 1, by omega⟩ : ℕ) < Nat.card F) :
    (((tupleShape F w hw r hr1 hrw s hsum hfirst hlast).1.1 : Fin w) : ℕ) + 1 = r := by
  dsimp [tupleShape]
  change (r - 1) + 1 = r
  omega

/-- The entries of the shape of a tuple recover the tuple entries (below depth `r`). -/
lemma tupleShape_entry {w : ℕ} (hw : 1 ≤ w) {r : ℕ} (hr1 : 1 ≤ r) (hrw : r ≤ w)
    (s : Fin r → ℕ+) (hsum : (∑ i : Fin r, ((s i : ℕ+)) : ℕ) = w)
    (hfirst : ∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ Nat.card F)
    (hlast : (s ⟨r - 1, by omega⟩ : ℕ) < Nat.card F) {i : Fin w} (hi : (i : ℕ) < r) :
    (((tupleShape F w hw r hr1 hrw s hsum hfirst hlast).1.2 i : Fin (Nat.card F + 1)) : ℕ) =
      (s ⟨(i : ℕ), hi⟩ : ℕ) := by
  dsimp [tupleShape]
  exact tupleEntry_val_lt F hr1 s hfirst hlast hi

/-- Two equal shapes of Hoffman tuples come from the same tuple data. -/
lemma tupleShape_inj {w : ℕ} (hw : 1 ≤ w) {r₁ r₂ : ℕ} (hr1₁ : 1 ≤ r₁) (hrw₁ : r₁ ≤ w)
    (s₁ : Fin r₁ → ℕ+) (hsum₁ : (∑ i : Fin r₁, ((s₁ i : ℕ+)) : ℕ) = w)
    (hfirst₁ : ∀ i : Fin r₁, (i : ℕ) < r₁ - 1 → (s₁ i : ℕ) ≤ Nat.card F)
    (hlast₁ : (s₁ ⟨r₁ - 1, by omega⟩ : ℕ) < Nat.card F)
    (hr1₂ : 1 ≤ r₂) (hrw₂ : r₂ ≤ w)
    (s₂ : Fin r₂ → ℕ+) (hsum₂ : (∑ i : Fin r₂, ((s₂ i : ℕ+)) : ℕ) = w)
    (hfirst₂ : ∀ i : Fin r₂, (i : ℕ) < r₂ - 1 → (s₂ i : ℕ) ≤ Nat.card F)
    (hlast₂ : (s₂ ⟨r₂ - 1, by omega⟩ : ℕ) < Nat.card F)
    (hx : tupleShape F w hw r₁ hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁ =
      tupleShape F w hw r₂ hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂) :
    ∃ h : r₁ = r₂,
      ∀ i : Fin r₁, s₁ i = s₂ ⟨(i : ℕ), by simpa [h] using i.isLt⟩ := by
  classical
  have hd₁ := tupleShape_depth F hw hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁
  have hd₂ := tupleShape_depth F hw hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂
  have hfst : ((((tupleShape F w hw r₁ hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁).1.1 : Fin w)) : ℕ) =
      ((((tupleShape F w hw r₂ hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂).1.1 : Fin w)) : ℕ) := by
    exact congrArg (fun z : ShapeT F w w => ((z.1.1 : Fin w) : ℕ)) hx
  have hr : r₁ = r₂ := by omega
  have hfun : (tupleShape F w hw r₁ hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁).1.2 =
      (tupleShape F w hw r₂ hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂).1.2 := by
    exact congrArg (fun z : ShapeT F w w => z.1.2) hx
  refine ⟨hr, ?_⟩
  intro i
  have hil : (i : ℕ) < w := by omega
  let ι : Fin w := ⟨(i : ℕ), hil⟩
  have hi₁ : (ι : ℕ) < r₁ := by
    dsimp [ι]
    exact i.isLt
  have he₁ := tupleShape_entry F hw hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁ (i := ι) hi₁
  have hi₂ : (ι : ℕ) < r₂ := by
    dsimp [ι]
    omega
  have he₂ := tupleShape_entry F hw hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂ (i := ι) hi₂
  have hidex₁ : (⟨((ι : Fin w) : ℕ), hi₁⟩ : Fin r₁) = i := by
    apply Fin.ext
    dsimp [ι]
  have hidex₂ : (⟨((ι : Fin w) : ℕ), hi₂⟩ : Fin r₂) = ⟨(i : ℕ), by simpa [hr] using i.isLt⟩ := by
    apply Fin.ext
    dsimp [ι]
  have hval₁ : ((((tupleShape F w hw r₁ hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁).1.2 ι :
        Fin (Nat.card F + 1))) : ℕ) = (s₁ i : ℕ) := by
    calc
      ((((tupleShape F w hw r₁ hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁).1.2 ι :
          Fin (Nat.card F + 1))) : ℕ) = (s₁ ⟨((ι : Fin w) : ℕ), hi₁⟩ : ℕ) := he₁
      _ = (s₁ i : ℕ) := by
            exact congrArg (fun t : Fin r₁ => (s₁ t : ℕ)) hidex₁
  have hval₂ : ((((tupleShape F w hw r₂ hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂).1.2 ι :
        Fin (Nat.card F + 1))) : ℕ) =
      (s₂ ⟨(i : ℕ), by simpa [hr] using i.isLt⟩ : ℕ) := by
    calc
      ((((tupleShape F w hw r₂ hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂).1.2 ι :
          Fin (Nat.card F + 1))) : ℕ) = (s₂ ⟨((ι : Fin w) : ℕ), hi₂⟩ : ℕ) := he₂
      _ = (s₂ ⟨(i : ℕ), by simpa [hr] using i.isLt⟩ : ℕ) := by
            exact congrArg (fun t : Fin r₂ => (s₂ t : ℕ)) hidex₂
  have hvi : ((((tupleShape F w hw r₁ hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁).1.2 ι :
        Fin (Nat.card F + 1))) : ℕ) =
      ((((tupleShape F w hw r₂ hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂).1.2 ι :
        Fin (Nat.card F + 1))) : ℕ) := by
    exact congrArg (fun e : Fin (Nat.card F + 1) => (e : ℕ)) (congrFun hfun ι)
  apply Subtype.ext
  calc
    (s₁ i : ℕ) = ((((tupleShape F w hw r₁ hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁).1.2 ι :
        Fin (Nat.card F + 1))) : ℕ) := hval₁.symm
    _ = ((((tupleShape F w hw r₂ hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂).1.2 ι :
        Fin (Nat.card F + 1))) : ℕ) := hvi
    _ = (s₂ ⟨(i : ℕ), by simpa [hr] using i.isLt⟩ : ℕ) := hval₂

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Membership in `𝒯_aux`: a `ζ_A` of a weight-`w` Hoffman tuple of depth `r`. -/
lemma mem_Taux (w : ℕ) (r : ℕ+) (v : RatFunc.CompletionAtInfty F) :
    v ∈ 𝒯_aux F w r ↔ ∃ s : Fin (r : ℕ) → ℕ+,
      (∑ i : Fin (r : ℕ), ((s i : ℕ+)) : ℕ) = w ∧
      (∀ i : Fin (r : ℕ), (i : ℕ) < (r : ℕ) - 1 → (s i : ℕ) ≤ Nat.card F) ∧
      (s ⟨(r : ℕ) - 1, by have hr := (r : ℕ+).pos; omega⟩ : ℕ) < Nat.card F ∧
      ζ_A F s = v := by
  classical
  simp [𝒯_aux, 𝔖_w]
  constructor
  · rintro ⟨s, hs, hζ⟩
    rcases hs with ⟨hsum, hb⟩
    refine ⟨s, hsum, ?_⟩
    rcases hb with ⟨hfirst, hlast⟩
    refine ⟨hfirst, hlast, hζ⟩
  · rintro ⟨s, hsum, hfirst, hlast, hζ⟩
    refine ⟨s, ?_, hζ⟩
    exact ⟨hsum, hfirst, hlast⟩

/-- Membership in `𝒯`: a `ζ_A` of a weight-`w` Hoffman tuple of some depth `r ≥ 1`. -/
lemma mem_T (w : ℕ) (v : RatFunc.CompletionAtInfty F) :
    v ∈ 𝒯 F w ↔ ∃ r : ℕ+, v ∈ 𝒯_aux F w r := by
  simp [𝒯]

/-- The shape attached to a value `v ∈ 𝒯 F w` (shape of a canonical preimage tuple). -/
noncomputable def valueToShape (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w}) : ShapeT F w w := by
  classical
  rcases v with ⟨v, hv⟩
  have hmemT : ∃ r : ℕ+, v ∈ 𝒯_aux F w r := (mem_T F w v).mp hv
  let r : ℕ+ := Classical.choose hmemT
  have hr : v ∈ 𝒯_aux F w r := Classical.choose_spec hmemT
  have hmemAux : ∃ s : Fin (r : ℕ) → ℕ+,
      (∑ i : Fin (r : ℕ), ((s i : ℕ+)) : ℕ) = w ∧
      (∀ i : Fin (r : ℕ), (i : ℕ) < (r : ℕ) - 1 → (s i : ℕ) ≤ Nat.card F) ∧
      (s ⟨(r : ℕ) - 1, by have hr' := (r : ℕ+).pos; omega⟩ : ℕ) < Nat.card F ∧
      ζ_A F s = v := (mem_Taux F w r v).mp hr
  let s : Fin (r : ℕ) → ℕ+ := Classical.choose hmemAux
  have hs := Classical.choose_spec hmemAux
  have hsum : (∑ i : Fin (r : ℕ), ((s i : ℕ+)) : ℕ) = w := hs.1
  have hfirst : ∀ i : Fin (r : ℕ), (i : ℕ) < (r : ℕ) - 1 → (s i : ℕ) ≤ Nat.card F := hs.2.1
  have hlast : (s ⟨(r : ℕ) - 1, by have hr' := (r : ℕ+).pos; omega⟩ : ℕ) < Nat.card F := hs.2.2.1
  have hζ : ζ_A F s = v := hs.2.2.2
  have hr1 : 1 ≤ (r : ℕ) := by
    exact Nat.succ_le_of_lt (r : ℕ+).pos
  have hrw : (r : ℕ) ≤ w := by
    have hc := card_le_sum_pnat (r : ℕ) s
    rw [hsum] at hc
    exact hc
  exact tupleShape F w hw (r : ℕ) hr1 hrw s hsum hfirst hlast

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `ζ_A` depends only on the tuple, not on the ambient reindexing of the depth. -/
lemma ζ_A_eq_of_reindex {r₁ r₂ : ℕ} (h : r₁ = r₂) (s₁ : Fin r₁ → ℕ+) (s₂ : Fin r₂ → ℕ+)
    (hp : ∀ i : Fin r₁, s₁ i = s₂ ⟨(i : ℕ), by simpa [h] using i.isLt⟩) :
    ζ_A F s₁ = ζ_A F s₂ := by
  classical
  subst r₂
  apply congrArg (ζ_A F)
  funext i
  simpa using hp i

/-- Equal shapes of Hoffman tuples force equal preimage tuples and hence equal values. -/
lemma valueToShape_inj (w : ℕ) (hw : 1 ≤ w) :
    Function.Injective (valueToShape F w hw) := by
  classical
  intro v₁ v₂ h
  rcases v₁ with ⟨v₁, hv₁⟩
  rcases v₂ with ⟨v₂, hv₂⟩
  have hm₁ : ∃ r : ℕ+, v₁ ∈ 𝒯_aux F w r := (mem_T F w v₁).mp hv₁
  let r₁ : ℕ+ := Classical.choose hm₁
  have hr₁' : v₁ ∈ 𝒯_aux F w r₁ := Classical.choose_spec hm₁
  have hma₁ : ∃ s : Fin (r₁ : ℕ) → ℕ+,
      (∑ i : Fin (r₁ : ℕ), ((s i : ℕ+)) : ℕ) = w ∧
      (∀ i : Fin (r₁ : ℕ), (i : ℕ) < (r₁ : ℕ) - 1 → (s i : ℕ) ≤ Nat.card F) ∧
      (s ⟨(r₁ : ℕ) - 1, by have hr' := (r₁ : ℕ+).pos; omega⟩ : ℕ) < Nat.card F ∧
      ζ_A F s = v₁ := (mem_Taux F w r₁ v₁).mp hr₁'
  let s₁ : Fin (r₁ : ℕ) → ℕ+ := Classical.choose hma₁
  have hs₁ := Classical.choose_spec hma₁
  have hsum₁ : (∑ i : Fin (r₁ : ℕ), ((s₁ i : ℕ+)) : ℕ) = w := hs₁.1
  have hfirst₁ : ∀ i : Fin (r₁ : ℕ), (i : ℕ) < (r₁ : ℕ) - 1 → (s₁ i : ℕ) ≤ Nat.card F := hs₁.2.1
  have hlast₁ : (s₁ ⟨(r₁ : ℕ) - 1, by have hr' := (r₁ : ℕ+).pos; omega⟩ : ℕ) < Nat.card F := hs₁.2.2.1
  have hζ₁ : ζ_A F s₁ = v₁ := hs₁.2.2.2
  have hm₂ : ∃ r : ℕ+, v₂ ∈ 𝒯_aux F w r := (mem_T F w v₂).mp hv₂
  let r₂ : ℕ+ := Classical.choose hm₂
  have hr₂' : v₂ ∈ 𝒯_aux F w r₂ := Classical.choose_spec hm₂
  have hma₂ : ∃ s : Fin (r₂ : ℕ) → ℕ+,
      (∑ i : Fin (r₂ : ℕ), ((s i : ℕ+)) : ℕ) = w ∧
      (∀ i : Fin (r₂ : ℕ), (i : ℕ) < (r₂ : ℕ) - 1 → (s i : ℕ) ≤ Nat.card F) ∧
      (s ⟨(r₂ : ℕ) - 1, by have hr' := (r₂ : ℕ+).pos; omega⟩ : ℕ) < Nat.card F ∧
      ζ_A F s = v₂ := (mem_Taux F w r₂ v₂).mp hr₂'
  let s₂ : Fin (r₂ : ℕ) → ℕ+ := Classical.choose hma₂
  have hs₂ := Classical.choose_spec hma₂
  have hsum₂ : (∑ i : Fin (r₂ : ℕ), ((s₂ i : ℕ+)) : ℕ) = w := hs₂.1
  have hfirst₂ : ∀ i : Fin (r₂ : ℕ), (i : ℕ) < (r₂ : ℕ) - 1 → (s₂ i : ℕ) ≤ Nat.card F := hs₂.2.1
  have hlast₂ : (s₂ ⟨(r₂ : ℕ) - 1, by have hr' := (r₂ : ℕ+).pos; omega⟩ : ℕ) < Nat.card F := hs₂.2.2.1
  have hζ₂ : ζ_A F s₂ = v₂ := hs₂.2.2.2
  have hr1₁ : 1 ≤ (r₁ : ℕ) := by
    exact Nat.succ_le_of_lt (r₁ : ℕ+).pos
  have hr1₂ : 1 ≤ (r₂ : ℕ) := by
    exact Nat.succ_le_of_lt (r₂ : ℕ+).pos
  have hrw₁ : (r₁ : ℕ) ≤ w := by
    have hc := card_le_sum_pnat (r₁ : ℕ) s₁
    rw [hsum₁] at hc
    exact hc
  have hrw₂ : (r₂ : ℕ) ≤ w := by
    have hc := card_le_sum_pnat (r₂ : ℕ) s₂
    rw [hsum₂] at hc
    exact hc
  have ht₁ : valueToShape F w hw ⟨v₁, hv₁⟩ =
      tupleShape F w hw (r₁ : ℕ) hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁ := by
    rfl
  have ht₂ : valueToShape F w hw ⟨v₂, hv₂⟩ =
      tupleShape F w hw (r₂ : ℕ) hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂ := by
    rfl
  rw [ht₁, ht₂] at h
  have hts := tupleShape_inj F hw hr1₁ hrw₁ s₁ hsum₁ hfirst₁ hlast₁
      hr1₂ hrw₂ s₂ hsum₂ hfirst₂ hlast₂ h
  rcases hts with ⟨hₙ, hpt⟩
  apply Subtype.ext
  calc
    v₁ = ζ_A F s₁ := hζ₁.symm
    _ = ζ_A F s₂ := ζ_A_eq_of_reindex F hₙ s₁ s₂ hpt
    _ = v₂ := hζ₂

/-- The set of Hoffman MZVs of weight `w` has at most as many elements as Hoffman shapes. -/
lemma 𝒯_ncard_le (w : ℕ) (hw : 1 ≤ w) : Set.ncard (𝒯 F w) ≤ hoffCount F w := by
  classical
  let α := {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w}
  have hco : Set.ncard (𝒯 F w) = (Set.univ : Set α).ncard := by
    exact (Set.ncard_coe (𝒯 F w)).symm
  have hun : (Set.univ : Set α).ncard = Nat.card α := by
    exact Set.ncard_univ α
  have hnat : Nat.card α ≤ Nat.card (ShapeT F w w) := by
    exact Nat.card_le_card_of_injective (valueToShape F w hw) (valueToShape_inj F w hw)
  calc
    Set.ncard (𝒯 F w) = (Set.univ : Set α).ncard := hco
    _ = Nat.card α := hun
    _ ≤ Nat.card (ShapeT F w w) := hnat
    _ = hoffCount F w := by
      rfl

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Rank bound of theorem A, given the spanning statement `𝒵 F w = span K (𝒯 F w)`. -/
lemma rank_part {w : ℕ} (hw : 1 ≤ w)
    (hspan : 𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w)) :
    Module.rank (RatFunc F) (𝒵 F w) ≤ (d F w : Cardinal) := by
  classical
  have hfin : Set.Finite (𝒯 F w) := by
    have hFin : Finite {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w} := by
      exact Finite.of_injective (valueToShape F w hw) (valueToShape_inj F w hw)
    letI := hFin
    exact Set.toFinite (𝒯 F w)
  have h1 := rank_span_le (R := RatFunc F) (M := RatFunc.CompletionAtInfty F) (𝒯 F w)
  have hcard : (Set.ncard (𝒯 F w) : Cardinal) = Cardinal.mk {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w} := by
    exact Set.cast_ncard (s := 𝒯 F w) hfin
  have hle1 : Set.ncard (𝒯 F w) ≤ d F w := by
    exact le_trans (𝒯_ncard_le F w hw) (le_of_eq (hoffCount_eq_d F w hw))
  calc
    Module.rank (RatFunc F) (𝒵 F w) = Module.rank (RatFunc F) (Submodule.span (RatFunc F) (𝒯 F w)) := by
          rw [hspan]
    _ ≤ Cardinal.mk {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w} := h1
    _ = (Set.ncard (𝒯 F w) : Cardinal) := hcard.symm
    _ ≤ (d F w : Cardinal) := by
          exact_mod_cast hle1

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Assembly of theorem A: the spanning statement `𝒵 F w = span K (𝒯 F w)` implies the
full conclusion of theorem A (the rank bound uses the counting module). -/
theorem theorem_A_of_span (w : ℕ+) (hspan : 𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w)) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) ∧
    Module.rank (RatFunc F) (𝒵 F w) ≤ d F w := by
  constructor
  · exact hspan
  · exact rank_part F (Nat.succ_le_of_lt w.pos) hspan

end ZagierHoffmanPositiveChar
