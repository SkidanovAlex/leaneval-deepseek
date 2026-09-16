/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.CountT0More
import Submission.ZagierHoffmanProof.StepL203
import Submission.Commons.Combinatorics.Composition.bounded_card_rec
import Submission.Commons.Combinatorics.Composition.bounded_card_two

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

/-!
# `𝒯0`-elements are bounded compositions

A weight-`w` tuple all of whose entries are `< q` is exactly a composition of `w` whose parts are
all `< q` (read the padded entries of the shape as a list).  Hence

  ★★ `shapeT0EquivComp : ShapeT0 F w w ≃ {c : Composition w // ∀ b ∈ c.blocks, b < q}`

and, with the shared commons `Commons.Combinatorics.Composition.bounded_card_rec` /
`bounded_card_two`,

  ★★★ `hoffCount0_eq_bcomp (1 ≤ w) : hoffCount0 F w = Σ_{i < min (q−1) w} hoffCount0 F (w−(i+1))`
  ★★★ `hoffCount0_eq_fib_of_card_three (q = 3) : hoffCount0 F w = Nat.fib (w+1)`.

The map is: shape ↦ its entries (as a list) ↦ a composition; conversely a bounded composition's
blocks are turned into a tuple and padded with `Counting.tupleShape`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The entries of a `𝒯0`-shape, as a list (the depth marker determines the length). -/
noncomputable def shapeT0List {w : ℕ} (x : ShapeT0 F w w) : List ℕ :=
  List.ofFn fun i : Fin ((x.1.1.1 : ℕ) + 1) =>
    ((x.1.1.2 ⟨(i : ℕ), by have h1 := i.isLt; have h2 := x.1.1.1.isLt; omega⟩ :
      Fin (Nat.card F + 1)) : ℕ)

/-- The entries of a `𝒯0`-shape are positive. -/
lemma shapeT0List_pos {w : ℕ} (x : ShapeT0 F w w) : ∀ b ∈ shapeT0List F x, 0 < b := by
  intro b hb
  rw [shapeT0List, List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  have h := x.1.2.2.1 ⟨(i : ℕ), by have h1 := i.isLt; have h2 := x.1.1.1.isLt; omega⟩
    (by show (i : ℕ) ≤ (x.1.1.1 : ℕ); have := i.isLt; omega)
  omega

/-- The entries of a `𝒯0`-shape sum to the weight. -/
lemma shapeT0List_sum {w : ℕ} (hw : 1 ≤ w) (x : ShapeT0 F w w) :
    (shapeT0List F x).sum = w := by
  rw [shapeT0List, List.sum_ofFn]
  have hcut := sum_fin_cut (v := (x.1.1.1 : ℕ) + 1) (w := w)
    (by have := x.1.1.1.isLt; omega)
    (fun i : Fin w => ((x.1.1.2 i : Fin (Nat.card F + 1)) : ℕ))
    (fun i hi => x.1.2.2.2.1 i (by omega))
  rw [← hcut]
  exact x.1.2.1

/-- The entries of a `𝒯0`-shape are `< q`. -/
lemma shapeT0List_lt {w : ℕ} (x : ShapeT0 F w w) :
    ∀ b ∈ shapeT0List F x, b < Nat.card F := by
  intro b hb
  rw [shapeT0List, List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  exact x.2 ⟨(i : ℕ), by have h1 := i.isLt; have h2 := x.1.1.1.isLt; omega⟩

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The entry of a `𝒯0`-shape at an index `i < w` is the entry of its tuple. -/
lemma shapeT0List_get {w : ℕ} (x : ShapeT0 F w w) (n : ℕ)
    (hn : n < (shapeT0List F x).length) :
    (shapeT0List F x).get ⟨n, hn⟩ =
      ((x.1.1.2 ⟨n, by rw [shapeT0List, List.length_ofFn] at hn; omega⟩ :
        Fin (Nat.card F + 1)) : ℕ) := by
  unfold shapeT0List
  rw [List.get_ofFn]
  rfl

/-- **The `𝒯0`-shape attached to a composition whose parts are all `< q`.** -/
noncomputable def shapeOfComp {w : ℕ} (hw : 1 ≤ w)
    (c : {c : Composition w // ∀ b ∈ c.blocks, b < Nat.card F}) : ShapeT0 F w w := by
  classical
  have hpos : ∀ i ∈ c.1.blocks, 0 < i := fun i hi => c.1.blocks_pos hi
  have hsum : c.1.blocks.sum = w := c.1.blocks_sum
  have hbound : ∀ i ∈ c.1.blocks, i < Nat.card F := c.2
  have hlen1 : 1 ≤ c.1.blocks.length := by
    rcases Nat.eq_zero_or_pos c.1.blocks.length with h0 | h
    · have hl : c.1.blocks = [] := List.length_eq_zero_iff.mp h0
      rw [hl] at hsum
      simp at hsum
      omega
    · exact h
  have hlenw : c.1.blocks.length ≤ w := by
    have h := List.length_le_sum_of_one_le c.1.blocks
      (fun i hi => Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (hpos i hi)))
    rw [hsum] at h
    exact h
  let s : Fin c.1.blocks.length → ℕ+ := fun i => ⟨c.1.blocks.get i, hpos _ (List.get_mem _ i)⟩
  have hs : (∑ i : Fin c.1.blocks.length, (s i : ℕ)) = w := by
    have h1 : (∑ i : Fin c.1.blocks.length, (c.1.blocks.get i)) = c.1.blocks.sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    calc (∑ i : Fin c.1.blocks.length, (s i : ℕ))
        = ∑ i : Fin c.1.blocks.length, (c.1.blocks.get i) :=
          Finset.sum_congr rfl (fun i _ => rfl)
      _ = c.1.blocks.sum := h1
      _ = w := hsum
  have hfirst : ∀ i : Fin c.1.blocks.length, (i : ℕ) < c.1.blocks.length - 1 →
      (s i : ℕ) ≤ Nat.card F := by
    intro i _
    exact le_of_lt (hbound _ (List.get_mem _ i))
  have hlast : (s ⟨c.1.blocks.length - 1, by omega⟩ : ℕ) < Nat.card F :=
    hbound _ (List.get_mem _ _)
  refine ⟨tupleShape F w hw c.1.blocks.length hlen1 hlenw s hs hfirst hlast, ?_⟩
  intro i
  dsimp only [tupleShape]
  by_cases hi : (i : ℕ) < c.1.blocks.length
  · rw [tupleEntry_val_lt F hlen1 s hfirst hlast hi]
    exact hbound _ (List.get_mem _ ⟨(i : ℕ), hi⟩)
  · rw [tupleEntry_val_ge F hlen1 s hfirst hlast (by omega)]
    have := nat_card_ge_two F
    omega

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The depth marker of `shapeOfComp`. -/
lemma shapeOfComp_marker {w : ℕ} (hw : 1 ≤ w)
    (c : {c : Composition w // ∀ b ∈ c.blocks, b < Nat.card F}) :
    ((shapeOfComp F hw c).1.1.1 : ℕ) = c.1.blocks.length - 1 := by
  unfold shapeOfComp
  dsimp only [tupleShape]

/-- The entries of `shapeOfComp` below the depth are the blocks of the composition. -/
lemma shapeOfComp_entry {w : ℕ} (hw : 1 ≤ w)
    (c : {c : Composition w // ∀ b ∈ c.blocks, b < Nat.card F})
    {i : Fin w} (hi : (i : ℕ) < c.1.blocks.length) :
    (((shapeOfComp F hw c).1.1.2 i : Fin (Nat.card F + 1)) : ℕ) =
      c.1.blocks.get ⟨(i : ℕ), hi⟩ := by
  unfold shapeOfComp
  dsimp only [tupleShape]
  simp only [tupleEntry, dif_pos hi]
  rfl

/-- The entries of `shapeOfComp` beyond the depth vanish. -/
lemma shapeOfComp_entry_ge {w : ℕ} (hw : 1 ≤ w)
    (c : {c : Composition w // ∀ b ∈ c.blocks, b < Nat.card F})
    {i : Fin w} (hi : c.1.blocks.length ≤ (i : ℕ)) :
    (((shapeOfComp F hw c).1.1.2 i : Fin (Nat.card F + 1)) : ℕ) = 0 := by
  unfold shapeOfComp
  dsimp only [tupleShape]
  simp only [tupleEntry, dif_neg (Nat.not_lt.mpr hi)]
  rfl

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A composition of `w ≥ 1` has at least one block. -/
lemma composition_blocks_length_pos {w : ℕ} (hw : 1 ≤ w) (c : Composition w) :
    1 ≤ c.blocks.length := by
  rcases Nat.eq_zero_or_pos c.blocks.length with h0 | h
  · have hl : c.blocks = [] := List.length_eq_zero_iff.mp h0
    have hs := c.blocks_sum
    rw [hl] at hs
    simp at hs
    omega
  · exact h

/-- The composition attached to a `𝒯0`-shape. -/
noncomputable def shapeT0Comp {w : ℕ} (hw : 1 ≤ w) (x : ShapeT0 F w w) :
    {c : Composition w // ∀ b ∈ c.blocks, b < Nat.card F} :=
  ⟨⟨shapeT0List F x, by intro i hi; exact shapeT0List_pos F x i hi, shapeT0List_sum F hw x⟩,
    shapeT0List_lt F x⟩

lemma shapeT0Comp_blocks {w : ℕ} (hw : 1 ≤ w) (x : ShapeT0 F w w) :
    (shapeT0Comp F hw x).1.blocks = shapeT0List F x := rfl

/-- ★★ **`𝒯0`-shapes are exactly the compositions of `w` whose parts are all `< q`.** -/
noncomputable def shapeT0EquivComp {w : ℕ} (hw : 1 ≤ w) :
    ShapeT0 F w w ≃ {c : Composition w // ∀ b ∈ c.blocks, b < Nat.card F} where
  toFun := shapeT0Comp F hw
  invFun := shapeOfComp F hw
  left_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    refine Prod.ext ?_ ?_
    · refine Fin.ext ?_
      rw [shapeOfComp_marker F hw (shapeT0Comp F hw x), shapeT0Comp_blocks F hw x, shapeT0List,
        List.length_ofFn]
      omega
    · funext i
      refine Fin.ext ?_
      by_cases hi : (i : ℕ) < (shapeT0List F x).length
      · rw [shapeOfComp_entry F hw (shapeT0Comp F hw x) hi]
        change (shapeT0List F x).get ⟨(i : ℕ), hi⟩ = ((x.1.1.2 i : Fin (Nat.card F + 1)) : ℕ)
        rw [shapeT0List_get F x (i : ℕ) hi]
      · have hge : (shapeT0List F x).length ≤ (i : ℕ) := Nat.le_of_not_lt hi
        rw [shapeOfComp_entry_ge F hw (shapeT0Comp F hw x)
          (by rwa [shapeT0Comp_blocks F hw x])]
        have hzero := x.1.2.2.2.1 i (by rw [shapeT0List, List.length_ofFn] at hge; omega)
        rw [hzero]
  right_inv c := by
    refine Subtype.ext (Composition.ext ?_)
    rw [shapeT0Comp_blocks F hw (shapeOfComp F hw c), shapeT0List]
    refine List.ext_get ?_ ?_
    · rw [List.length_ofFn, shapeOfComp_marker F hw c]
      exact Nat.sub_add_cancel (composition_blocks_length_pos hw c.1)
    · intro n h1 h2
      have hlen1 := composition_blocks_length_pos hw c.1
      have hlenw : c.1.blocks.length ≤ w := by
        have h := List.length_le_sum_of_one_le c.1.blocks
          (fun i hi => Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (c.1.blocks_pos hi)))
        rw [c.1.blocks_sum] at h
        exact h
      have hidx : n < w := by
        rw [List.length_ofFn, shapeOfComp_marker F hw c] at h1
        omega
      rw [List.get_ofFn]
      exact shapeOfComp_entry F hw c (i := ⟨n, hidx⟩) h2

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ **The `𝒯0`-count is the number of bounded compositions**: `|𝒯0_w|` counts the compositions
of `w` whose parts are all `< q`. -/
theorem hoffCount0_eq_bcomp {w : ℕ} (hw : 1 ≤ w) :
    hoffCount0 F w = Nat.card {c : Composition w // ∀ b ∈ c.blocks, b < Nat.card F} :=
  Nat.card_congr (shapeT0EquivComp F hw)

/-- The two forms of the "bounded parts" condition agree for `q ≥ 1`: `b < q ↔ b ≤ q − 1`. -/
noncomputable def bcompEquiv {w q : ℕ} (hq : 0 < q) :
    {c : Composition w // ∀ b ∈ c.blocks, b < q}
      ≃ {c : Composition w // ∀ b ∈ c.blocks, b ≤ q - 1} := by
  refine Equiv.subtypeEquivRight (fun c => ?_)
  constructor
  · intro h b hb
    exact (Nat.lt_iff_le_pred hq).mp (h b hb)
  · intro h b hb
    exact (Nat.lt_iff_le_pred hq).mpr (h b hb)

/-- ★★★ **For `q = 3`, the number of `𝒯0`-elements of weight `w` is the Fibonacci number
`Fib (w+1)`**: `𝒯0`-tuples are compositions of `w` into parts `1` or `2`. -/
theorem hoffCount0_eq_fib_of_card_three {w : ℕ} (hw : 1 ≤ w) (hq : Nat.card F = 3) :
    hoffCount0 F w = Nat.fib (w + 1) := by
  rw [hoffCount0_eq_bcomp F hw,
    Nat.card_congr (bcompEquiv (w := w) (q := Nat.card F) (by omega)), hq]
  norm_num
  rw [← Nat.card_eq_fintype_card]
  exact Commons.Combinatorics.Composition.bounded_card_two w

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ **The recursion for the `𝒯0`-count** in the range `w > q − 1`:
`|𝒯0_w| = Σ_{i < q−1} |𝒯0_{w−i−1}|`.  (In this range every `w − i − 1` is `≥ 1`, so no
correction term for the empty composition is needed.) -/
theorem hoffCount0_rec {w : ℕ} (hw : 1 ≤ w) (hwq : Nat.card F - 1 < w) :
    hoffCount0 F w = ∑ i ∈ Finset.range (Nat.card F - 1), hoffCount0 F (w - (i + 1)) := by
  have hqpos : 0 < Nat.card F := by have := nat_card_ge_two F; omega
  have hq1 : 0 < Nat.card F - 1 := by have := nat_card_ge_two F; omega
  have hmin : (Nat.card F - 1).min w = Nat.card F - 1 := Nat.min_eq_left (by omega)
  rw [hoffCount0_eq_bcomp F hw,
    Nat.card_congr (bcompEquiv (w := w) (q := Nat.card F) hqpos),
    Commons.Combinatorics.Composition.bounded_card_rec (Nat.card F - 1) w hq1 hw, hmin]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < Nat.card F - 1 := Finset.mem_range.mp hi
  have h2 : i + 2 ≤ w := by omega
  have hpos : 1 ≤ w - (i + 1) := by omega
  exact (Nat.card_congr (bcompEquiv (w := w - (i + 1)) (q := Nat.card F) hqpos)).symm.trans
    (hoffCount0_eq_bcomp F hpos).symm

/-- ★★ **The Fibonacci recurrence for `q = 3`**: `|𝒯0_w| = |𝒯0_{w−1}| + |𝒯0_{w−2}|`. -/
theorem hoffCount0_rec_three {w : ℕ} (hw : 3 ≤ w) (hq : Nat.card F = 3) :
    hoffCount0 F w = hoffCount0 F (w - 1) + hoffCount0 F (w - 2) := by
  have h := hoffCount0_rec F (by omega) (by omega : Nat.card F - 1 < w)
  rw [h, hq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

/-- Over `F₃`: `|𝒯0_w|` is Fibonacci, e.g. `|𝒯0_5| = Fib 6 = 8`. -/
example : hoffCount0 (ZMod 3) 5 = 8 := by
  have h := hoffCount0_eq_fib_of_card_three (ZMod 3) (w := 5) (by norm_num)
    (by rw [Nat.card_eq_fintype_card, ZMod.card])
  rw [h]
  norm_num

/-- Over `F₃`: the Fibonacci recurrence at `w = 6`. -/
example : hoffCount0 (ZMod 3) 6 = hoffCount0 (ZMod 3) 5 + hoffCount0 (ZMod 3) 4 := by
  have h := hoffCount0_rec_three (ZMod 3) (w := 6) (by norm_num)
    (by rw [Nat.card_eq_fintype_card, ZMod.card])
  simpa using h

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ **For `q = 2`**, `𝒯0_w = {ζ_A(1,…,1)}` is a singleton, so `|𝒯0_w| = hoffCount0 F w = 1`. -/
theorem hoffCount0_card_two (h2 : Nat.card F = 2) {w : ℕ} (hw : 1 ≤ w) :
    hoffCount0 F w = 1 := by
  rw [← ncard_T0_eq_hoffCount0 F w hw, T0_card_two_eq F h2 w hw, Set.ncard_singleton]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ **For `w < q`, `|𝒯0_w| = 2^{w-1}`** (all compositions of `w` have parts `< q`). -/
theorem hoffCount0_eq_two_pow {w : ℕ} (hw1 : 1 ≤ w) (hwq : w < Nat.card F) :
    hoffCount0 F w = 2 ^ (w - 1) := by
  rw [hoffCount0_eq_d_of_le F hw1 (by omega), d_eq_pow_two F hw1 hwq]

end ZagierHoffmanPositiveChar
