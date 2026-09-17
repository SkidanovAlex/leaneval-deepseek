import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# The multiplicity sum over the `E₈` lattice points: `ℕ`-valued version

For any list `L` of all lattice points `v : Fin 8 → ℤ` with `qZ v ≤ 10` (`E8NormTwo.qZ` the
squared length) whose norm distribution is `1, 240, 2160, 6720, 17520, 30240`, the sum of the
corresponding multiplicities `1407, 455, 133, 34, 7, 1` is `779247`.

Note there is NO hypothesis on `L.length`: elements of `L` outside the six norm classes contribute
`0` because the function below vanishes there, so only the six `filter` cardinalities matter.
-/

open scoped BigOperators

set_option linter.unusedVariables false

/-- In the `cons` case, the length of a filtered list, as a natural number. -/
private lemma filter_length_cons {α : Type*} (p : α → Bool) (a : α) (t : List α) :
    ((a :: t).filter p).length
      = (t.filter p).length + (if p a = true then 1 else 0) := by
  rw [List.filter_cons]
  by_cases h : p a = true <;> simp [h]

/-- The step function `1407, 455, 133, 34, 7, 1` at `0, 2, 4, 6, 8, 10` written as a sum of
indicators. -/
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

theorem e8_lattice_toNat_sum (L : List (Fin 8 → ℤ)) (hnd : L.Nodup)
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
    L.toFinset.sum (fun v => if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 0 then 1407
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 2 then 455
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 4 then 133
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 6 then 34
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 8 then 7
      else if Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 10 then 1 else 0)
      = 779247 := by
  rw [List.sum_toFinset _ hnd]
  rw [list_sum_step L (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v)]
  rw [h0, h2, h4, h6, h8, h10]

end Commons.LinearAlgebra.Matrix.Cartan
