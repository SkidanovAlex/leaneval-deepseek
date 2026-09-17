import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# The multiplicity sum over the `E₈` lattice points of squared length `≤ 10`

`Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count` produces a list `L` of all
`v : Fin 8 → ℤ` with `qZ v ≤ 10` (where `qZ` is the squared length, `E8NormTwo.qZ`) together with
the norm distribution `1, 240, 2160, 6720, 17520, 30240`.  The result below adds the corresponding
weight multiplicities `1407, 455, 133, 34, 7, 1` and shows that the total is `779247`.

The proof is purely combinatorial: the weight multiplicity attached to a lattice vector only
depends on `qZ v`, and the number of vectors of `L` with `qZ v = q` is the length of the
corresponding filter, so the sum splits into the six groups `1407·1 + 455·240 + 133·2160 +
34·6720 + 7·17520 + 1·30240 = 779247`.
-/

set_option linter.unusedVariables false

open scoped BigOperators

/-- In the `cons` case, the length of a filtered list, as a natural number. -/
private lemma filter_length_cons {α : Type*} (p : α → Bool) (a : α) (t : List α) :
    ((a :: t).filter p).length
      = (t.filter p).length + (if p a = true then 1 else 0) := by
  rw [List.filter_cons]
  by_cases h : p a = true <;> simp [h]

/-- A step function written as a sum of indicators. -/
private lemma mult_eq_indicator (n : ℤ) :
    (if n = 0 then (1407:ℕ)
      else if n = 2 then 455
      else if n = 4 then 133
      else if n = 6 then 34
      else if n = 8 then 7
      else if n = 10 then 1 else 0)
      = 1407 * (if n = 0 then (1:ℕ) else 0) + 455 * (if n = 2 then 1 else 0)
        + 133 * (if n = 4 then 1 else 0) + 34 * (if n = 6 then 1 else 0)
        + 7 * (if n = 8 then 1 else 0) + 1 * (if n = 10 then 1 else 0) := by
  split_ifs <;> omega

/-- The sum of a step function of `f` over a list depends only on the lengths of the level
filters of `f`. -/
private lemma list_sum_step {α : Type*} (L : List α) (f : α → ℤ) :
    (L.map (fun v => if f v = 0 then (1407:ℕ)
      else if f v = 2 then 455
      else if f v = 4 then 133
      else if f v = 6 then 34
      else if f v = 8 then 7
      else if f v = 10 then 1 else 0)).sum
      = 1407 * (L.filter (fun v => f v = 0)).length
      + 455 * (L.filter (fun v => f v = 2)).length
      + 133 * (L.filter (fun v => f v = 4)).length
      + 34 * (L.filter (fun v => f v = 6)).length
      + 7 * (L.filter (fun v => f v = 8)).length
      + 1 * (L.filter (fun v => f v = 10)).length := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih]
    rw [filter_length_cons, filter_length_cons, filter_length_cons, filter_length_cons,
        filter_length_cons, filter_length_cons]
    simp only [decide_eq_true_eq]
    rw [mult_eq_indicator (f a)]
    ring

theorem e8_lattice_mnorm_sum (L : List (Fin 8 → ℤ)) (hnd : L.Nodup) (hcard : L.length = 56881)
    (hall : ∀ v : Fin 8 → ℤ, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v ≤ 10 → v ∈ L)
    (h0 : (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 0)).length
      = 1)
    (h2 : (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 2)).length
      = 240)
    (h4 : (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 4)).length
      = 2160)
    (h6 : (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 6)).length
      = 6720)
    (h8 : (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 8)).length
      = 17520)
    (h10 : (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 10)).length
      = 30240) :
    (L.map (fun v => if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 0 then 1407
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 2 then 455
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 4 then 133
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 6 then 34
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 8 then 7
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 10 then 1 else 0)).sum
      = 779247 := by
  rw [list_sum_step L (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v),
      h0, h2, h4, h6, h8, h10]

end Commons.LinearAlgebra.Matrix.Cartan
