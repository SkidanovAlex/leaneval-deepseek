import Mathlib
import Submission.Work.HP.DyadicDefs

/-!
# Combinatorial set-up for the dyadic sum bound (`Work.HP.dyadic.sum_bound`)

This file isolates the objects used by `Work.HP.dyadic.sum_bound` and by the
child lemmas it delegates, so that those children can import a sorry-free module.

The sum in question is over the box
`Nset N r M = {n : Fin r → ℕ | ∀ i, n i ≤ M, ∑ i, n i * (r - i) ≤ M}`,
and the exponent is `bigE' N r n = ∑ i, n i * (wval r i * alpha N i)` with
`wval r i = r - i` and `alpha N i = N - max i 2`.

The key structural fact is that `wval r i * alpha N i = (N-2) * wval r i - dval r i`
where the *deficit* `dval r i = (i-2)(r-i)` vanishes exactly on the first three
coordinates `i = 0,1,2`.  Splitting the coordinates into the first three (the
"head", with vanishing deficit) and the remaining ones (the "tail", whose deficits
are all `≥ 1`) is what produces the factor `(M+1)^2` in the estimate.
-/

set_option autoImplicit false

namespace Work.HP.dyadic

open Finset

noncomputable section

/-- The deficit weight `(i-2)(r-i)` of the coordinate `i`; it vanishes exactly for `i ≤ 2`. -/
def dval (r : ℕ) (i : Fin r) : ℕ := ((i : ℕ) - 2) * (r - (i : ℕ))

/-- `∑ i, n i * (r - i)` : the quantity constrained to be `≤ M`. -/
def sval (r : ℕ) (n : Fin r → ℕ) : ℕ := ∑ i, n i * wval r i

/-- `∑ i, n i * dval r i` : the total deficit of `n`. -/
def Pval (r : ℕ) (n : Fin r → ℕ) : ℕ := ∑ i, n i * dval r i

/-- The coordinate `i < 3` of `Fin r`, for `r ≥ 3`. -/
def headIdx (r : ℕ) (hr : 3 ≤ r) (i : Fin 3) : Fin r := ⟨(i : ℕ), by omega⟩

/-- The coordinate `i + 3` of `Fin r`, for `r ≥ 3`. -/
def tailIdx (r : ℕ) (hr : 3 ≤ r) (j : Fin (r - 3)) : Fin r := ⟨(j : ℕ) + 3, by omega⟩

/-- Restriction of a family to its first three coordinates. -/
def headPart (r : ℕ) (hr : 3 ≤ r) (n : Fin r → ℕ) : Fin 3 → ℕ := fun i => n (headIdx r hr i)

/-- Restriction of a family to the coordinates `≥ 3`. -/
def tailPart (r : ℕ) (hr : 3 ≤ r) (n : Fin r → ℕ) : Fin (r - 3) → ℕ := fun j => n (tailIdx r hr j)

/-- Assemble a family from its first three coordinates and the remaining ones. -/
def glue (r : ℕ) (hr : 3 ≤ r) (v : Fin 3 → ℕ) (u : Fin (r - 3) → ℕ) : Fin r → ℕ :=
  fun i => if h : (i : ℕ) < 3 then v ⟨(i : ℕ), h⟩ else u ⟨(i : ℕ) - 3, by have := i.isLt; omega⟩

/-- The head weight `∑_{i<3} v i * (r - i)`. -/
def headW (r : ℕ) (hr : 3 ≤ r) (v : Fin 3 → ℕ) : ℕ := ∑ i, v i * wval r (headIdx r hr i)

/-- The tail weight `∑_{3 ≤ i} u (i-3) * (r - i)`. -/
def tailW (r : ℕ) (hr : 3 ≤ r) (u : Fin (r - 3) → ℕ) : ℕ := ∑ j, u j * wval r (tailIdx r hr j)

/-- The tail deficit `∑_{3 ≤ i} u (i-3) * dval i`. -/
def tailD (r : ℕ) (hr : 3 ≤ r) (u : Fin (r - 3) → ℕ) : ℕ := ∑ j, u j * dval r (tailIdx r hr j)

@[simp] lemma headPart_apply (r : ℕ) (hr : 3 ≤ r) (n : Fin r → ℕ) (i : Fin 3) :
    headPart r hr n i = n (headIdx r hr i) := rfl

@[simp] lemma tailPart_apply (r : ℕ) (hr : 3 ≤ r) (n : Fin r → ℕ) (j : Fin (r - 3)) :
    tailPart r hr n j = n (tailIdx r hr j) := rfl

lemma dval_headIdx (r : ℕ) (hr : 3 ≤ r) (i : Fin 3) : dval r (headIdx r hr i) = 0 := by
  have hi : (i : ℕ) ≤ 2 := by have := i.isLt; omega
  simp [dval, headIdx, Nat.sub_eq_zero_of_le hi]

lemma dval_tailIdx_le (r : ℕ) (hr : 3 ≤ r) (j : Fin (r - 3)) : 1 ≤ dval r (tailIdx r hr j) := by
  have hj : (j : ℕ) < r - 3 := j.isLt
  simp only [dval, tailIdx]
  have h1 : 1 ≤ (j : ℕ) + 3 - 2 := by omega
  have h2 : 1 ≤ r - ((j : ℕ) + 3) := by omega
  calc 1 = 1 * 1 := by ring
    _ ≤ ((j : ℕ) + 3 - 2) * (r - ((j : ℕ) + 3)) := Nat.mul_le_mul h1 h2

lemma wval_pos {r : ℕ} (i : Fin r) : 1 ≤ wval r i := by
  simp only [wval]
  have := i.isLt
  omega

end

end Work.HP.dyadic
