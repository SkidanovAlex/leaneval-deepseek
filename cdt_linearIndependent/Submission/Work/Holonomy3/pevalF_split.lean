import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.pevalF_consPt

/-!
# Splitting `pevalF` along the first variable, at a torus point

Writing `w = e^{2πi u}`, the torus point `tor (Fin.insertNth 0 u s)` is the point
`consPt w (tor s) = (w, tor s₁, …, tor s_d)`.  The general slice decomposition
`pevalF_consPt` then gives

`pevalF c (tor (Fin.insertNth 0 u s)) = ∑ t ∈ suppFst c, w ^ t * pevalF (sliceF c t) (tor s)`.

This is the form in which the decomposition is used to slice the torus integral along the
first variable.
-/

namespace Work.Holonomy3

open scoped BigOperators

theorem pevalF_split {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (u : ℝ) (s : Fin d → ℝ) :
    pevalF c (tor (Fin.insertNth (0 : Fin (d + 1)) u s))
      = ∑ t ∈ suppFst c,
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) ^ t * pevalF (sliceF c t) (tor s) := by
  -- Inserting `u` in the first coordinate of `s` is `Fin.cons u s`.
  have hins : (Fin.insertNth (0 : Fin (d + 1)) u s : Fin (d + 1) → ℝ) = Fin.cons u s := by
    rw [Fin.insertNth_zero]
    rfl
  -- Hence the corresponding torus point is `consPt w (tor s)` with `w = e^{2πi u}`.
  have hpt : tor (Fin.insertNth (0 : Fin (d + 1)) u s)
      = consPt (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) (tor s) := by
    rw [hins]
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ i => rfl
  rw [hpt, pevalF_consPt]

end Work.Holonomy3
