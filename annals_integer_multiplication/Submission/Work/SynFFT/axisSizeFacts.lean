import Mathlib
import Submission.Work.SynFFT.axisKit

/-!
# Encoding-size facts for the axis-transpose merge words

`Work.SynFFT.axisSizeFacts`: the merge layer of `HasAxisTranspose` (`axisKit`) builds values by
`ofList`-ing rows (`grpVal`) and groups (`stateVal`); the cost of the merge words is governed by
`HvdH.vsz` of those values (`axisMerge`, `axisLeaf`).  Here we record

* the exact sizes of those values (`axsz_grpVal_size`, `axsz_stateVal_size`),
* the sub-additivity of `zipCat` at the level of encodings (`axsz_grpVal_zipCat_le`),
* the fact that neither `mLevel` nor `iter` ever increases the total encoded size, so that the
  cost bound of the merge phase is monotone in the number of levels performed.

The proof is entirely elementary: `vsz (ofList xs) = Σ_{x∈xs} vsz x + xs.length + 1` (one `cons`
glyph per element, one for the terminal `nil`), and concatenating two encodings shares exactly one
glyph -- the terminal `nil` of the first -- which is where the slack in the `zipCat` inequality
comes from.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## Immediates -/

@[simp] theorem axsz_ofList_nil : ofList ([] : List Val) = Val.nil := rfl

@[simp] theorem axsz_ofList_cons (a : Val) (t : List Val) :
    ofList (a :: t) = Val.cons a (ofList t) := rfl

/-- A `cons` cell contributes one glyph plus the two sub-encodings. -/
@[simp] theorem axsz_vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]

@[simp] theorem axsz_vsz_nil : vsz (Val.nil : Val) = 1 := rfl

/-! ## Exact sizes of `ofList`-encoded lists -/

/-- `vsz (ofList xs) = Σ_{x ∈ xs} vsz x + xs.length + 1`: one glyph per `cons` cell, one for the
terminal `nil`, plus the encodings of the elements. -/
theorem axsz_vsz_ofList : ∀ xs : List Val, vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1
  | [] => by simp
  | a :: t => by
      rw [axsz_ofList_cons, axsz_vsz_cons, axsz_vsz_ofList t]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- Concatenating two encodings shares exactly one glyph (the terminal `nil` of the first). -/
theorem axsz_vsz_ofList_append (xs ys : List Val) :
    vsz (ofList (xs ++ ys)) + 1 = vsz (ofList xs) + vsz (ofList ys) := by
  rw [axsz_vsz_ofList, axsz_vsz_ofList, axsz_vsz_ofList]
  simp only [List.map_append, List.sum_append, List.length_append]
  omega

/-- Splitting a constant out of a sum over a list: `Σ (f a + c) = Σ f a + c * |l|`. -/
theorem axsz_sum_map_add_const {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun a => f a + c)).sum = (l.map f).sum + c * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih, List.map_cons, List.sum_cons]
      ring

/-- `ofList` of a `map`: every element contributes its encoding plus its `cons` cell. -/
theorem axsz_ofList_map_size {α : Type*} (l : List α) (f : α → Val) :
    vsz (ofList (l.map f)) = (l.map (fun a => vsz (f a) + 1)).sum + 1 := by
  induction l with
  | nil => simp [ofList]
  | cons a t ih =>
      rw [List.map_cons, axsz_ofList_cons, axsz_vsz_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Exact size of a group (a list of rows, each row `ofList`-encoded): the rows, one `cons` glyph
per row, and one for the terminal `nil` of the enclosing list. -/
theorem axsz_grpVal_size (G : List (List Val)) :
    vsz (grpVal G) = (G.map (fun r => vsz (ofList r) + 1)).sum + 1 :=
  axsz_ofList_map_size G ofList

/-- Exact size of a state (a list of groups). -/
theorem axsz_stateVal_size (Gs : List (List (List Val))) :
    vsz (stateVal Gs) = (Gs.map (fun G => vsz (grpVal G) + 1)).sum + 1 :=
  axsz_ofList_map_size Gs grpVal

/-! ## Sub-additivity of `zipCat` -/

theorem axsz_zipCat_length_le (G₁ G₂ : List (List Val)) :
    (zipCat G₁ G₂).length ≤ G₁.length + G₂.length := by
  induction G₁ generalizing G₂ with
  | nil => simp only [zipCat]; simp
  | cons r₁ t₁ ih =>
      cases G₂ with
      | nil => simp only [zipCat_nil_right]; simp
      | cons r₂ t₂ =>
          rw [show zipCat (r₁ :: t₁) (r₂ :: t₂) = (r₁ ++ r₂) :: zipCat t₁ t₂ from rfl]
          have := ih t₂
          simp only [List.length_cons]
          omega

theorem axsz_sum_zipCat_le (G₁ G₂ : List (List Val)) :
    ((zipCat G₁ G₂).map (fun r => vsz (ofList r))).sum ≤
      (G₁.map (fun r => vsz (ofList r))).sum + (G₂.map (fun r => vsz (ofList r))).sum := by
  induction G₁ generalizing G₂ with
  | nil => simp only [zipCat]; simp
  | cons r₁ t₁ ih =>
      cases G₂ with
      | nil => simp only [zipCat_nil_right]; simp
      | cons r₂ t₂ =>
          have hrow : vsz (ofList (r₁ ++ r₂)) ≤ vsz (ofList r₁) + vsz (ofList r₂) := by
            have := axsz_vsz_ofList_append r₁ r₂
            omega
          have hih := ih t₂
          rw [show zipCat (r₁ :: t₁) (r₂ :: t₂) = (r₁ ++ r₂) :: zipCat t₁ t₂ from rfl]
          simp only [List.map_cons, List.sum_cons]
          omega

/-- The same, for the sums `Σ_{r} (vsz r + 1)` that occur in `vsz (grpVal ·)`. -/
theorem axsz_sum1_zipCat_le (G₁ G₂ : List (List Val)) :
    ((zipCat G₁ G₂).map (fun r => vsz (ofList r) + 1)).sum ≤
      (G₁.map (fun r => vsz (ofList r) + 1)).sum +
        (G₂.map (fun r => vsz (ofList r) + 1)).sum := by
  have e₁ : ((zipCat G₁ G₂).map (fun r => vsz (ofList r) + 1)).sum
      = ((zipCat G₁ G₂).map (fun r => vsz (ofList r))).sum + (zipCat G₁ G₂).length := by
    rw [axsz_sum_map_add_const, Nat.one_mul]
  have e₂ : (G₁.map (fun r => vsz (ofList r) + 1)).sum
      = (G₁.map (fun r => vsz (ofList r))).sum + G₁.length := by
    rw [axsz_sum_map_add_const, Nat.one_mul]
  have e₃ : (G₂.map (fun r => vsz (ofList r) + 1)).sum
      = (G₂.map (fun r => vsz (ofList r))).sum + G₂.length := by
    rw [axsz_sum_map_add_const, Nat.one_mul]
  have h₁ := axsz_sum_zipCat_le G₁ G₂
  have h₂ := axsz_zipCat_length_le G₁ G₂
  omega

/-- `zipCat` never increases the encoded size of a group. -/
theorem axsz_grpVal_zipCat_le (G₁ G₂ : List (List Val)) :
    vsz (grpVal (zipCat G₁ G₂)) ≤ vsz (grpVal G₁) + vsz (grpVal G₂) := by
  rw [axsz_grpVal_size, axsz_grpVal_size, axsz_grpVal_size]
  have := axsz_sum1_zipCat_le G₁ G₂
  omega

/-! ## `mLevel` and `iter` never increase the total encoded size -/

/-- One merge level never increases the total encoded size of a state. -/
theorem axsz_mLevel_sum_le : ∀ Gs : List (List (List Val)),
    ((mLevel Gs).map (fun G => vsz (grpVal G) + 1)).sum ≤
      (Gs.map (fun G => vsz (grpVal G) + 1)).sum
  | [] => le_refl 0
  | [G] => le_refl _
  | G₁ :: G₂ :: rest => by
      have ih := axsz_mLevel_sum_le rest
      have hzip := axsz_grpVal_zipCat_le G₁ G₂
      rw [mLevel_cons_cons]
      simp only [List.map_cons, List.sum_cons]
      omega

theorem axsz_mLevel_stateVal_le (Gs : List (List (List Val))) :
    vsz (stateVal (mLevel Gs)) ≤ vsz (stateVal Gs) := by
  rw [axsz_stateVal_size, axsz_stateVal_size]
  exact Nat.add_le_add_right (axsz_mLevel_sum_le Gs) 1

theorem axsz_iter_stateVal_le : ∀ (k : ℕ) (Gs : List (List (List Val))),
    vsz (stateVal (iter k Gs)) ≤ vsz (stateVal Gs)
  | 0, Gs => le_refl _
  | Nat.succ k, Gs => by
      rw [iter_succ]
      exact le_trans (axsz_iter_stateVal_le k (mLevel Gs)) (axsz_mLevel_stateVal_le Gs)

theorem axsz_length_le_stateVal (Gs : List (List (List Val))) :
    Gs.length + 1 ≤ vsz (stateVal Gs) := by
  rw [axsz_stateVal_size]
  have h : Gs.length ≤ (Gs.map (fun G => vsz (grpVal G) + 1)).sum := by
    induction Gs with
    | nil => simp
    | cons G rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  omega

/-! ## A bit-counting fact -/

theorem axsz_pow_le_size {j n : ℕ} (h : 2 ^ j ≤ n) : j ≤ n.size := by
  have h1 : 2 ^ j < 2 ^ n.size := lt_of_le_of_lt h (Nat.lt_size_self n)
  exact le_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1)

-- encoding-size facts for the merge words: grpVal/stateVal/zipCat are defined in axisKit
theorem axisSizeFacts :
    (∀ (G : List (List HvdH.Val)), HvdH.vsz (Work.SynFFT.grpVal G) = (G.map (fun r => HvdH.vsz (HvdH.ofList r) + 1)).sum + 1) ∧
    (∀ (Gs : List (List (List HvdH.Val))),
      HvdH.vsz (Work.SynFFT.stateVal Gs) = (Gs.map (fun G => HvdH.vsz (Work.SynFFT.grpVal G) + 1)).sum + 1) ∧
    (∀ (G₁ G₂ : List (List HvdH.Val)), HvdH.vsz (Work.SynFFT.grpVal (Work.SynFFT.zipCat G₁ G₂)) ≤
      HvdH.vsz (Work.SynFFT.grpVal G₁) + HvdH.vsz (Work.SynFFT.grpVal G₂)) ∧
    (∀ (Gs : List (List (List HvdH.Val))), HvdH.vsz (Work.SynFFT.stateVal (Work.SynFFT.mLevel Gs)) ≤
      HvdH.vsz (Work.SynFFT.stateVal Gs)) ∧
    (∀ (k : ℕ) (Gs : List (List (List HvdH.Val))), HvdH.vsz (Work.SynFFT.stateVal (Work.SynFFT.iter k Gs)) ≤
      HvdH.vsz (Work.SynFFT.stateVal Gs)) ∧
    (∀ (Gs : List (List (List HvdH.Val))), Gs.length + 1 ≤ HvdH.vsz (Work.SynFFT.stateVal Gs)) ∧
    (∀ (j n : ℕ), 1 ≤ n → 2 ^ j ≤ n → j ≤ n.size) := by
  refine ⟨axsz_grpVal_size, axsz_stateVal_size, axsz_grpVal_zipCat_le, axsz_mLevel_stateVal_le,
    axsz_iter_stateVal_le, axsz_length_le_stateVal, fun j n _ h => axsz_pow_le_size h⟩

end Work.SynFFT
