/-
# `Work.FIArea7.Pub213` — vocabulary for the direct route to *FI* (21.10)

This is an independent development of *FI* Proposition 21.3, *FI* (21.10), along the paper's own
route (pp. 1026–1027), i.e. without the mean-square input `MeanSquareBound`, and without
`Submission.Work.FIArea7.qBilinDefs` (whose `Work.FIArea7.mem_gBox_iff` collides with the
declaration of the same name in `prop232Defs.lean`; see `Pub213/NOTES.md`).

The objects `IsC` (the "arrangement" monoid of *FI* p. 1027: units, `1+i` and the odd naturals)
and `IsPP` (primary and primitive) are those of `Work.FIArea7.Prop213Aux.Defs`.
-/
import Mathlib
import Submission.Work.FIArea7.Prop213Aux.Defs
import Submission.Work.FIArea7.FIsymbols

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Work.FIArea7

open Finset
open scoped BigOperators

namespace Pub213

/-- All `c ∈ C` with `‖c‖² ≤ X`: a sub-`Finset` of the box of radius `⌈√X⌉`. -/
def CBox (X : ℝ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (⌈Real.sqrt X⌉₊ : ℤ)).filter (fun c => Prop213Aux.IsC c)

lemma mem_CBox {X : ℝ} {c : GaussianInt} :
    c ∈ CBox X ↔ c ∈ Work.FIPlan.gBox (⌈Real.sqrt X⌉₊ : ℤ) ∧ Prop213Aux.IsC c :=
  Finset.mem_filter

/-! ## The `6`-fold convolution -/

/-- The `k`-tuples of elements of the box `gBox R`. -/
def boxTup (k : ℕ) (R : ℤ) : Finset (Fin k → GaussianInt) :=
  Fintype.piFinset (fun _ : Fin k => Work.FIPlan.gBox R)

/-- The product of the entries of a tuple. -/
def tupProd {k : ℕ} (t : Fin k → GaussianInt) : GaussianInt := ∏ i, t i

/-- The `6`-fold Dirichlet convolution of `β` over the box `gBox R`. -/
def conv6 (R : ℤ) (β : GaussianInt → ℂ) (u : GaussianInt) : ℂ :=
  ∑ t ∈ boxTup 6 R, if tupProd t = u then ∏ i, β (t i) else 0

/-- `‖(n : ℂ)‖ ≤ 1` when `|n| ≤ 1`. -/
lemma norm_intCast_le_one_of_abs_le_one {n : ℤ} (h : |n| ≤ 1) :
    ‖(((n : ℤ)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast h

/-- A box containing every `k`-fold product of elements of `gBox R`
(the modulus of an element of `gBox R` is at most `√2·|R|`). -/
def boxPow (R : ℤ) (k : ℕ) : ℤ := (⌈Real.sqrt 2 * |(R : ℝ)|⌉₊ : ℤ) ^ k

end Pub213

end Work.FIArea7

end
