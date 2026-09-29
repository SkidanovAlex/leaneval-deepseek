import Mathlib
import Submission.Work.IntLib.parseEmitDefs

/-!
# The bit accumulators of the `parse` scan

`Work.IntLib.pushAcc f pre` is the content of a stack that has received `f g` for every glyph `g` of
the scanned list `pre` (most recent glyph first).  The raw input of the challenge is encoded by
`IntegerMultiplication.encodeProd encodeNat encodeNat`, i.e. by `List.zipWithAll Prod.mk`, and each
input symbol `p : InSym = Option Bool × Option Bool` becomes the glyph `inpGlyph p`.

This file shows that scanning the *reversed* raw input list with the dispatch `inX` (resp. `inY`)
recovers exactly the bits of the first (resp. second) component, in reverse order -- `none`
components contributing no glyph at all.

The proof is a case analysis on the three defining equations of `List.zipWithAll`
(`List.zipWithAll.eq_1/eq_2/eq_3`): the `[], l₂` case is pure padding (nothing is contributed to
`inX`), the `l₁, []` case is pure padding for `inY`, and the `a :: as, b :: bs` case peels off one
genuine pair.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-! ## Concatenation of accumulated pushes -/

/-- Pushing along a concatenation is the concatenation of the pushes. -/
theorem pushAcc_append_zipAll (f : Glyph → List Glyph) (a b : List Glyph) :
    pushAcc f (a ++ b) = pushAcc f a ++ pushAcc f b := by
  induction a with
  | nil => rfl
  | cons g gs ih => simp [ih, List.append_assoc]

/-! ## The padding cases -/

/-- If the input glyphs come from symbols whose first component is `none`, the `x` accumulator stays
empty. -/
theorem pushAcc_inX_pad_right (l₂ : List Bool) :
    pushAcc inX ((l₂.map (fun b => Glyph.inp (none : Option Bool) (some b))).reverse) = [] := by
  induction l₂ with
  | nil => rfl
  | cons b bs ih =>
      rw [List.map_cons, List.reverse_cons, pushAcc_append_zipAll]
      simp [ih]

/-- If the input glyphs come from symbols whose second component is `none`, the `y` accumulator
stays empty. -/
theorem pushAcc_inY_pad_left (l₁ : List Bool) :
    pushAcc inY ((l₁.map (fun a => Glyph.inp (some a) (none : Option Bool))).reverse) = [] := by
  induction l₁ with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons, List.reverse_cons, pushAcc_append_zipAll]
      simp [ih]

/-- The `x` accumulator of symbols with second component `none` collects the first component, in
reverse order. -/
theorem pushAcc_inX_pad_left (l₁ : List Bool) :
    pushAcc inX ((l₁.map (fun a => Glyph.inp (some a) (none : Option Bool))).reverse) =
      (l₁.map Glyph.bit).reverse := by
  induction l₁ with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons, List.reverse_cons, pushAcc_append_zipAll, ih]
      simp

/-- The `y` accumulator of symbols with first component `none` collects the second component, in
reverse order. -/
theorem pushAcc_inY_pad_right (l₂ : List Bool) :
    pushAcc inY ((l₂.map (fun b => Glyph.inp (none : Option Bool) (some b))).reverse) =
      (l₂.map Glyph.bit).reverse := by
  induction l₂ with
  | nil => rfl
  | cons b bs ih =>
      rw [List.map_cons, List.reverse_cons, pushAcc_append_zipAll, ih]
      simp

/-! ## The two main statements -/

/-- Scanning the reversed raw input of `zipWithAll Prod.mk l₁ l₂` with `inX` collects the bits of
`l₁`, in reverse order. -/
theorem pushAcc_inX_zipWithAll_eq (l₁ l₂ : List Bool) :
    pushAcc inX ((List.zipWithAll Prod.mk l₁ l₂).map HvdH.inpGlyph).reverse =
      (l₁.map HvdH.Glyph.bit).reverse := by
  induction l₂ generalizing l₁ with
  | nil =>
      cases l₁ with
      | nil => simp
      | cons a as =>
          rw [List.zipWithAll.eq_2, List.map_map]
          exact pushAcc_inX_pad_left (a :: as)
  | cons b bs ih =>
      cases l₁ with
      | nil =>
          rw [List.zipWithAll.eq_1, List.map_map]
          exact pushAcc_inX_pad_right (b :: bs)
      | cons a as =>
          rw [List.zipWithAll.eq_3, List.map_cons, List.reverse_cons, pushAcc_append_zipAll, ih as]
          simp [HvdH.inpGlyph]

/-- Scanning the reversed raw input of `zipWithAll Prod.mk l₁ l₂` with `inY` collects the bits of
`l₂`, in reverse order. -/
theorem pushAcc_inY_zipWithAll_eq (l₁ l₂ : List Bool) :
    pushAcc inY ((List.zipWithAll Prod.mk l₁ l₂).map HvdH.inpGlyph).reverse =
      (l₂.map HvdH.Glyph.bit).reverse := by
  induction l₂ generalizing l₁ with
  | nil =>
      cases l₁ with
      | nil => simp
      | cons a as =>
          rw [List.zipWithAll.eq_2, List.map_map]
          exact pushAcc_inY_pad_left (a :: as)
  | cons b bs ih =>
      cases l₁ with
      | nil =>
          rw [List.zipWithAll.eq_1, List.map_map]
          exact pushAcc_inY_pad_right (b :: bs)
      | cons a as =>
          rw [List.zipWithAll.eq_3, List.map_cons, List.reverse_cons, pushAcc_append_zipAll, ih as]
          simp [HvdH.inpGlyph]

theorem pushAccBitsZipWithAll :
    (∀ l₁ l₂ : List Bool, Work.IntLib.pushAcc Work.IntLib.inX ((List.zipWithAll Prod.mk l₁ l₂).map HvdH.inpGlyph).reverse = (l₁.map HvdH.Glyph.bit).reverse) ∧
    (∀ l₁ l₂ : List Bool, Work.IntLib.pushAcc Work.IntLib.inY ((List.zipWithAll Prod.mk l₁ l₂).map HvdH.inpGlyph).reverse = (l₂.map HvdH.Glyph.bit).reverse) :=
  ⟨pushAcc_inX_zipWithAll_eq, pushAcc_inY_zipWithAll_eq⟩

end Work.IntLib
