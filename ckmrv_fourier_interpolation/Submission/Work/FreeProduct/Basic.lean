import Mathlib
import Submission.Work.Modular.GroupAlgebra
import Submission.Work.Modular.presentedGroup_equiv_PSL

/-!
# Reduced words in the free product `ℤ/2 ∗ ℤ/3`

This file sets up the combinatorics of reduced words in `FP = ℤ/2 ∗ ℤ/3` (the free product
realized as `Monoid.CoprodI Cyc`, which is isomorphic to the abstract group `Γ` of
`Work.Modular.GroupAlgebra` via `Work.Modular.PresGroup.gammaEquivFP`).

The dictionary used throughout:

* `x` is the generator of the `ℤ/2` factor, `y` that of the `ℤ/3` factor,
* `T = x * y` is the infinite order element of CKMRV (their `T = S (ST)`),
* every element of `FP` has a unique reduced word `Word.equiv g : W`; the *length* of `g` is the
  number of letters of that word.

The main content is a length calculus:

* `wlen_smul_le` : prepending a letter increases the length by at most one;
* `toList_mul_of_ne` : if the last letter of a prefix and the first letter of a reduced word lie
  in different factors, the reduced word of the product is the concatenation.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- The reduced words of `FP = ℤ/2 ∗ ℤ/3`. -/
abbrev W : Type := Monoid.CoprodI.Word Cyc

/-- The letters of the free product. -/
abbrev Letter : Type := Sigma Cyc

/-- The generator of the `ℤ/2` factor. -/
def x : FP := gC2

/-- The generator of the `ℤ/3` factor. -/
def y : FP := gC3

/-- The element `y ^ 2`. -/
def y2 : FP := y ^ 2

theorem x_sq : x * x = 1 := gC2_mul_self

theorem y_cube : y ^ 3 = 1 := gC3_cube

theorem y_mul_y2 : y * y2 = 1 := by
  have h : y * y2 = y ^ 3 := by rw [y2]; group
  exact h.trans gC3_cube

theorem y2_mul_y : y2 * y = 1 := by
  have h : y2 * y = y ^ 3 := by rw [y2]; group
  exact h.trans gC3_cube

theorem y_mul_y : y * y = y2 := by rw [y2, pow_two]

/-- `T = x * y`, the infinite order element of CKMRV (`T = S (ST)`). -/
def T : FP := x * y

theorem T_eq : T = x * y := rfl

/-- The relevant letters, as elements of `Sigma Cyc`. -/
def Lx : Letter := ⟨false, (Multiplicative.ofAdd 1 : C2)⟩
def Ly : Letter := ⟨true, (Multiplicative.ofAdd 1 : C3)⟩
def Ly2 : Letter := ⟨true, (Multiplicative.ofAdd 2 : C3)⟩

@[simp] theorem Lx_fst : Lx.1 = false := rfl
@[simp] theorem Ly_fst : Ly.1 = true := rfl

theorem of_Lx : Monoid.CoprodI.of Lx.2 = x := rfl
theorem of_Ly : Monoid.CoprodI.of Ly.2 = y := rfl

theorem of_Ly2 : Monoid.CoprodI.of Ly2.2 = y2 := by
  have h : (Multiplicative.ofAdd 2 : C3) = (Multiplicative.ofAdd 1) * (Multiplicative.ofAdd 1) :=
    by decide
  rw [Ly2, y2, y, gC3, h, sq, map_mul]

/-- The product of a list of letters, inside `FP`. -/
def toProd (l : List Letter) : FP := (l.map fun a => Monoid.CoprodI.of a.2).prod

@[simp] theorem toProd_nil : toProd [] = 1 := rfl

theorem toProd_cons (a : Letter) (l : List Letter) :
    toProd (a :: l) = Monoid.CoprodI.of a.2 * toProd l := by
  simp [toProd, List.prod_cons]

theorem prod_injective : Function.Injective (Monoid.CoprodI.Word.prod (M := Cyc)) :=
  Monoid.CoprodI.Word.equiv.symm.injective

theorem prod_equiv (g : FP) : (Monoid.CoprodI.Word.equiv g).prod = g :=
  Monoid.CoprodI.Word.equiv.symm_apply_apply g

theorem equiv_prod (w : W) : Monoid.CoprodI.Word.equiv w.prod = w :=
  Monoid.CoprodI.Word.equiv.apply_symm_apply w

theorem eq_of_prod_eq {w w' : W} (h : w.prod = w'.prod) : w = w' := prod_injective h

/-- **The word of a product.** -/
theorem equiv_mul (g z : FP) :
    Monoid.CoprodI.Word.equiv (g * z) = g • Monoid.CoprodI.Word.equiv z := by
  apply eq_of_prod_eq
  rw [prod_equiv, Monoid.CoprodI.Word.prod_smul, prod_equiv]

/-- The length of a reduced word. -/
def wlen (w : W) : ℕ := w.toList.length

/-- The length of a group element: the number of letters of its reduced word. -/
def elen (g : FP) : ℕ := wlen (Monoid.CoprodI.Word.equiv g)

theorem elen_prod (w : W) : elen w.prod = wlen w := by
  simp [elen, equiv_prod]

theorem equiv_one : Monoid.CoprodI.Word.equiv (1 : FP) = Monoid.CoprodI.Word.empty := by
  rw [← Monoid.CoprodI.Word.prod_empty (M := Cyc)]
  exact equiv_prod Monoid.CoprodI.Word.empty

theorem elen_eq_zero_iff {g : FP} : elen g = 0 ↔ g = 1 := by
  constructor
  · intro h
    have h0 : (Monoid.CoprodI.Word.equiv g).toList.length = 0 := by
      simp only [elen, wlen] at h; exact h
    have h' : (Monoid.CoprodI.Word.equiv g).toList = [] := List.length_eq_zero_iff.mp h0
    have hw : Monoid.CoprodI.Word.equiv g = Monoid.CoprodI.Word.empty :=
      Monoid.CoprodI.Word.ext h'
    rw [← prod_equiv g, hw, Monoid.CoprodI.Word.prod_empty]
  · rintro rfl
    rw [elen, equiv_one]
    rfl

theorem elen_one : elen (1 : FP) = 0 := elen_eq_zero_iff.mpr rfl

theorem wlen_eq_zero_iff {w : W} : wlen w = 0 ↔ w = Monoid.CoprodI.Word.empty := by
  constructor
  · intro h
    have h0 : w.toList.length = 0 := by simpa [wlen] using h
    exact Monoid.CoprodI.Word.ext (List.length_eq_zero_iff.mp h0)
  · rintro rfl
    rfl

theorem wlen_pos {w : W} (h : w ≠ Monoid.CoprodI.Word.empty) : 0 < wlen w := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  exact h (wlen_eq_zero_iff.mp h0)

end

end Work.FreeProduct
