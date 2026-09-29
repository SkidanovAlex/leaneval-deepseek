import Mathlib
import Submission.Work.ConvR.basic

/-!
# ConvR/`scaleArr`: elementary facts about the encodings of array shapes

Shared vocabulary for `Work.ConvR.scaleArr` (the pointwise application of `FxLib.scale` to a
rectangular array `M × r` of fixed-point complex numbers).

The value of an array is `rarrVal As = ofList (As.map cvecVal)`: a `cons`-chain whose elements are
the rows `cvecVal u = ofList (u.map cfxVal)`, and the results of the maps below are rebuilt with the
same constructors, so all the structural facts are definitional.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## The array / row / coefficient encodings -/

@[simp] theorem cvecVal_nil : cvecVal ([] : List (ℤ × ℤ)) = Val.nil := rfl

@[simp] theorem cvecVal_cons (z : ℤ × ℤ) (u : List (ℤ × ℤ)) :
    cvecVal (z :: u) = Val.cons (cfxVal z) (cvecVal u) := rfl

@[simp] theorem rarrVal_nil : rarrVal ([] : List (List (ℤ × ℤ))) = Val.nil := rfl

@[simp] theorem rarrVal_cons (w : List (ℤ × ℤ)) (ws : List (List (ℤ × ℤ))) :
    rarrVal (w :: ws) = Val.cons (cvecVal w) (rarrVal ws) := rfl

/-- A row is `nil` exactly when it is empty. -/
theorem cvecVal_eq_nil_iff {u : List (ℤ × ℤ)} : cvecVal u = Val.nil ↔ u = [] := by
  cases u with
  | nil => simp
  | cons z u => simp

theorem cvecVal_ne_nil {u : List (ℤ × ℤ)} (h : u ≠ []) : cvecVal u ≠ Val.nil :=
  fun hc => h ((cvecVal_eq_nil_iff).mp hc)

/-- A single fixed-point coefficient is never `nil`. -/
theorem cfxVal_ne_nil (z : ℤ × ℤ) : cfxVal z ≠ Val.nil := by
  simp [cfxVal]

@[simp] theorem enc_nil_eq : (Val.nil).enc = [Glyph.nil] := rfl

@[simp] theorem enc_cons_eq (a b : Val) : (Val.cons a b).enc = Glyph.cons :: (a.enc ++ b.enc) := rfl

/-- The first glyph of an integer value. -/
theorem enc_int_head (z : ℤ) :
    (Val.int z).enc.headD Glyph.eos = if z < 0 then Glyph.neg else Glyph.pos := by
  by_cases h : z < 0 <;> simp [Val.enc, h]

/-- The encoding of a nonempty row starts with `cons`. -/
theorem cvecVal_enc_head_cons {u : List (ℤ × ℤ)} (h : u ≠ []) :
    (cvecVal u).enc.headD Glyph.eos = Glyph.cons := by
  cases u with
  | nil => exact absurd rfl h
  | cons z u => simp [enc_cons_eq]

/-- The encoding of an empty row starts with `nil`. -/
theorem cvecVal_enc_head_nil : (cvecVal ([] : List (ℤ × ℤ))).enc.headD Glyph.eos = Glyph.nil := by
  simp

/-- Given the disc condition, a `nil` row of the array forces `r = 0`. -/
theorem eq_nil_of_inDiscArr_row_nil {p M r : ℕ} {As : List (List (ℤ × ℤ))}
    (h : InDiscArr p M r As) {u : List (ℤ × ℤ)} (hu : u ∈ As) (h0 : u = []) : r = 0 := by
  have hlen : u.length = r := (h.2 u hu).1
  rw [h0] at hlen
  simp at hlen
  omega

/-- All rows of `As` are empty as soon as one is (the rows of `InDiscArr` all have length `r`). -/
theorem all_rows_nil_of_row_nil {p M r : ℕ} {As : List (List (ℤ × ℤ))}
    (h : InDiscArr p M r As) {u : List (ℤ × ℤ)} (hu : u ∈ As) (h0 : u = []) :
    ∀ w ∈ As, w = [] := by
  have hr : r = 0 := eq_nil_of_inDiscArr_row_nil h hu h0
  intro w hw
  have hlen : w.length = r := (h.2 w hw).1
  rw [hr] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

end Work.ConvR
