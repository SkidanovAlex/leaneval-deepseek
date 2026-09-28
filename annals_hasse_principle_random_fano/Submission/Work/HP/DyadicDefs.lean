import Mathlib

/-!
# Definitions for the dyadic-sum combinatorial estimate (`Work.HP.dyadic_sum_ge3`)

This file isolates the combinatorial objects used in `dyadic_sum_ge3.lean` so that
child lemmas can import a sorry-free module.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

open Finset

/-- The weight attached to the `j`-th coordinate in the exponent. -/
def cval (N r : ℕ) (j : Fin r) : ℕ :=
  if (j : ℕ) < 2 then N - 2 else N + r - 1 - 2 * (j : ℕ)

/-- The number of coordinates `≥ i`, i.e. `r - i`. -/
def wval (r : ℕ) (i : Fin r) : ℕ := r - (i : ℕ)

/-- `N - max(i,2)`. -/
def alpha (N : ℕ) {r : ℕ} (i : Fin r) : ℕ := N - max (i : ℕ) 2

/-- The suffix sum `∑_{j ≥ i} cval j`, in closed form. -/
def Sval (N r : ℕ) (i : Fin r) : ℕ := wval r i * alpha N i

/-- The exponent of the term indexed by `k`. -/
def bigE (N r : ℕ) (k : Fin r → ℕ) : ℕ := ∑ j, k j * cval N r j

/-- The exponent of the term indexed by the difference vector `n`. -/
def bigE' (N r : ℕ) (n : Fin r → ℕ) : ℕ := ∑ i, n i * Sval N r i

/-- The box of functions with all coordinates `≤ M`. -/
def piBox (r M : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun _ : Fin r => Finset.range (M + 1))

/-- Monotone functions in the box with total sum `≤ M`. -/
def Kset (r M : ℕ) : Finset (Fin r → ℕ) :=
  (piBox r M).filter (fun k => Monotone k ∧ (∑ j, k j) ≤ M)

/-- Difference vectors in the box whose weighted sum is `≤ M`. -/
def Nset (N r M : ℕ) : Finset (Fin r → ℕ) :=
  (piBox r M).filter (fun n => (∑ i, n i * wval r i) ≤ M)

/-- Prefix sums of a difference vector. -/
def toK (r : ℕ) (n : Fin r → ℕ) : Fin r → ℕ :=
  fun i => ∑ j ∈ Finset.univ.filter (fun j : Fin r => j ≤ i), n j

/-- Successive differences of a vector. -/
def toN (r : ℕ) (k : Fin r → ℕ) : Fin r → ℕ :=
  fun i => k i - (if (i : ℕ) = 0 then 0 else k ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩)

end Work.HP
