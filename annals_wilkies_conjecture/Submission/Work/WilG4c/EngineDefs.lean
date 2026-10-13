/-
  WilG4c — vocabulary for the per-cell engine of BNZ §5.5 (definitions only).

  See the module docstring of the main file `StepCellEngine` for the mathematics.  Here we fix:

  * `midFun lo hi χ`, `widFun lo hi χ` — the midpoint and the shifted half-width of the fibre
    of a cell, evaluated along a base parametrisation `χ`;
  * `engFam χ M W` — the family (of `n`-variable functions) whose members are the coordinates
    of `χ`, then `M`, then `W`; the inductive hypothesis `FLem` in dimension `n` is applied to
    it;
  * `cellChart χ M W ψ` — the resulting chart of the `(n+1)`-cube.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.YbddAux

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- The midpoint `(lo + hi)/2` of the fibre of `κ` over the base point `(l, χ l u)`. -/
def midFun {p n : ℕ} (lo hi : (Fin (p + n) → ℝ) → ℝ)
    (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin p → ℝ) → (Fin n → ℝ) → ℝ :=
  fun l u => (lo (Fin.append l (χ l u)) + hi (Fin.append l (χ l u))) / 2

/-- The shifted half-width `((hi - lo) + 1/2)/2` of the fibre of `κ` over `(l, χ l u)`; the
actual width is `2 * widFun lo hi χ l u - 1/2`. -/
def widFun {p n : ℕ} (lo hi : (Fin (p + n) → ℝ) → ℝ)
    (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin p → ℝ) → (Fin n → ℝ) → ℝ :=
  fun l u => ((hi (Fin.append l (χ l u)) - lo (Fin.append l (χ l u))) + 1 / 2) / 2

/-- The family whose members are the `n` coordinates of `χ` followed by `M` and `W`: member
`j` for `j < n` is `χ j`, member `n` is `M` and member `n+1` is `W`. -/
def engFam {p n : ℕ} (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) : Work.WilkG4c.Family (n + 2) p n :=
  fun i l u =>
    if h : (i : ℕ) < n then χ l u ⟨(i : ℕ), h⟩
    else if (i : ℕ) = n then M l u else W l u

/-- The per-cell chart of the `(n+1)`-cube induced by the base parametrisation `χ`, the
midpoint `M`, the shifted half-width `W` and an `n`-cube chart `ψ`:
`(l, (t,ζ)) ↦ (χ (ψ l t), M (ψ l t) + (ζ - 1/2) (2 W (ψ l t) - 1/2))`, where
`t = Fin.init z` and `ζ = z (Fin.last n)`. -/
def cellChart {p n : ℕ} (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ)
    (ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin p → ℝ) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
  fun l z j =>
    if h : (j : ℕ) = n then
      M l (ψ l (Fin.init z)) + (z (Fin.last n) - 1 / 2) *
        (2 * W l (ψ l (Fin.init z)) - 1 / 2)
    else
      χ l (ψ l (Fin.init z)) ⟨(j : ℕ), by omega⟩

end Work.WilG4c
