import Mathlib.NumberTheory.Height.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The logarithmic height of a tuple is at most the sum of the heights of its coordinates

For a finite tuple `x : ι → K` over a field `K` with `Height.AdmissibleAbsValues`, we prove

  `Height.logHeight x ≤ ∑ i, Height.logHeight₁ (x i)`.

The multiplicative content is the inequality `Height.mulHeight x ≤ ∏ i, Height.mulHeight₁ (x i)`.
It is deduced from the Segre embedding: writing `y a = ![x a, 1]` (so that
`mulHeight₁ (x a) = mulHeight (y a)`), the height of the "multiplication table"
`fun I ↦ ∏ a, y a (I a)` is exactly `∏ a, mulHeight₁ (x a)`, while `x` is recovered as the
restriction of that table along the injection `i ↦ (fun j ↦ if j = i then 0 else 1)`. Since the
tuple height is monotone under composition with a function (`Height.mulHeight_comp_le`), the
inequality follows. Taking logarithms gives the claimed bound.
-/

open scoped BigOperators

namespace Commons.NumberTheory.Height.LogHeight

theorem logHeight_le_sum_logHeight1 {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
    {ι : Type*} [Fintype ι] (x : ι → K) :
    Height.logHeight x ≤ ∑ i, Height.logHeight₁ (x i) := by
  classical
  -- Multiplicative form: the height of the tuple is at most the product of the coordinate heights.
  have hmul : Height.mulHeight x ≤ ∏ i, Height.mulHeight₁ (x i) := by
    -- The "multiplication table" attached to the pairs `![x a, 1]`.
    let Y : (ι → Fin 2) → K := fun I => ∏ a, ![x a, 1] (I a)
    -- The injection selecting, for each `i`, the index of `Y` that evaluates to `x i`.
    let f : ι → (ι → Fin 2) := fun i j => if j = i then 0 else 1
    -- The height of `Y` is the product of the heights of the pairs `![x a, 1]`.
    have hYeq : Height.mulHeight Y = ∏ a, Height.mulHeight₁ (x a) := by
      have h := Height.mulHeight_fun_prod_eq (x := fun a : ι => ![x a, 1]) (fun a => by simp)
      rw [show (fun I : ι → Fin 2 => ∏ a, ![x a, 1] (I a)) = Y from rfl] at h
      rw [h]
      exact Finset.prod_congr rfl fun a _ => (Height.mulHeight₁_eq_mulHeight (x a)).symm
    -- `x` is the restriction of `Y` along `f`.
    have hcomp : Y ∘ f = x := by
      funext i
      simp only [Function.comp_apply, Y, f]
      rw [Finset.prod_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    calc Height.mulHeight x = Height.mulHeight (Y ∘ f) := by rw [hcomp]
      _ ≤ Height.mulHeight Y := Height.mulHeight_comp_le f Y
      _ = ∏ a, Height.mulHeight₁ (x a) := hYeq
  calc Height.logHeight x = Real.log (Height.mulHeight x) := Height.logHeight_eq_log_mulHeight x
    _ ≤ Real.log (∏ i, Height.mulHeight₁ (x i)) :=
        Real.log_le_log (Height.mulHeight_pos x) hmul
    _ = ∑ i, Height.logHeight₁ (x i) := by
        rw [Real.log_prod (fun i _ => (Height.mulHeight₁_pos (x i)).ne')]
        exact Finset.sum_congr rfl fun i _ => Height.logHeight₁_eq_log_mulHeight₁ (x i)

end Commons.NumberTheory.Height.LogHeight