import Mathlib
import Submission.Work.WilkiesH.Defs

/-!
# Nonemptiness of cells

Every cylindrical cell of `WilkiesDesign.IsCell` is nonempty.  This is a
straight induction on the cell construction:

* the base cell `Set.univ ⊆ ℝ⁰` is inhabited by the empty tuple;
* a `graph` cell over a nonempty base contains `Fin.snoc x (f x)` for any
  `x` in the base;
* a `band` cell over a nonempty base contains `Fin.snoc x y` where `y` is a
  real number strictly between the two extended boundary values `a x < b x`
  (such a real exists by `EReal.lt_iff_exists_real_btwn`).
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.Cell

/-- A real number strictly between two comparable extended reals.  This is the
form in which the density of `ℝ` inside `EReal` is used for `band` cells. -/
lemma exists_real_btwn_EReal {a b : EReal} (h : a < b) :
    ∃ y : ℝ, a < (y : EReal) ∧ (y : EReal) < b :=
  EReal.lt_iff_exists_real_btwn.mp h

theorem isCell_nonempty {n : ℕ} {C : Set (Fin n → ℝ)} (h : WilkiesDesign.IsCell n C) : C.Nonempty := by
  induction h with
  | zero => exact ⟨fun i => i.elim0, trivial⟩
  | graph hC f hf ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨Fin.snoc x (f x), by
        refine ⟨?_, ?_⟩
        · simpa [Fin.init_snoc] using hx
        · simp [Fin.init_snoc, Fin.snoc_last]⟩
  | band hC a b ha hb hab ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hy1, hy2⟩ := exists_real_btwn_EReal (hab x hx)
      exact ⟨Fin.snoc x y, by
        refine ⟨?_, ?_, ?_⟩
        · simpa [Fin.init_snoc] using hx
        · simpa [Fin.init_snoc, Fin.snoc_last] using hy1
        · simpa [Fin.init_snoc, Fin.snoc_last] using hy2⟩

end Work.WilkiesH.Cell
