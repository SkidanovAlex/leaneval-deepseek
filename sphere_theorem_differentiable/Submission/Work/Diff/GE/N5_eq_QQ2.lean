import Mathlib
import Submission.Work.Diff.GE.frobSq5_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `N5` is the five-slot contraction `QQ2 5` of the uncurried tensor

`N5 Γ S` (see `Work.Diff.GE.norms_defs`) is the full contraction of a `(0,5)`-tensor array
`S : Fin n → Curv4 n` with `Γ⁻¹` in every slot.  `QQ2 5 Γ X Y` (see `Work.Diff.GE.frobSq5_defs`)
is the same contraction of two *uncurried* `(0,5)`-tensors `X Y : (Fin 5 → Fin n) → ℝ`.

The two agree: this file proves

* `Work.Diff.GE.N5_eq_QQ2` : `N5 Γ T = QQ2 5 Γ (uncurry T) (uncurry T)`,

re-indexing the ten `ℕ`-indexed sums of `N5` by the bijection
`(Fin 5 → Fin n) ≃ Fin n × Fin n × Fin n × Fin n × Fin n`.

The ingredients are `vec5Equiv` (the bijection, realised with the vector notation `![a,b,c,d,e]`),
`sum_vec5` / `sum_vec5_pair` (re-indexing sums over `Fin 5 → Fin n` as five nested sums), and the
projection lemmas `vec5_val_one` … `vec5_val_four` (`Matrix.cons_val_zero` handles slot `0`).
-/

namespace Work.Diff.GE

open Finset LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The bijection between `Fin 5`-tuples in `Fin n` and `5`-tuples of elements of `Fin n`
(the latter as a right-nested product). -/
def vec5Equiv (n : ℕ) : (Fin 5 → Fin n) ≃ (Fin n × Fin n × Fin n × Fin n × Fin n) where
  toFun x := (x 0, x 1, x 2, x 3, x 4)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

/-- Re-index a sum over `Fin 5 → Fin n` as five nested sums. -/
theorem sum_vec5 (f : (Fin 5 → Fin n) → ℝ) :
    (∑ x : Fin 5 → Fin n, f x) = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, f ![m, i, j, k, l] := by
  rw [(Equiv.sum_comp (vec5Equiv n).symm f).symm]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Re-index a double sum over `Fin 5 → Fin n` as ten nested sums. -/
theorem sum_vec5_pair (f : (Fin 5 → Fin n) → (Fin 5 → Fin n) → ℝ) :
    (∑ x : Fin 5 → Fin n, ∑ y : Fin 5 → Fin n, f x y)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q, ∑ r, ∑ s, ∑ t,
          f ![m, i, j, k, l] ![p, q, r, s, t] := by
  rw [sum_vec5 (fun x => ∑ y, f x y)]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
    Finset.sum_congr rfl (fun l _ => ?_)))))
  exact sum_vec5 (fun y => f ![m, i, j, k, l] y)

/-- Slot `1` of the vector `![a,b,c,d,e]`. -/
theorem vec5_val_one {α : Type*} (a b c d e : α) : (![a, b, c, d, e] : Fin 5 → α) 1 = b := rfl

/-- Slot `2` of the vector `![a,b,c,d,e]`. -/
theorem vec5_val_two {α : Type*} (a b c d e : α) : (![a, b, c, d, e] : Fin 5 → α) 2 = c := rfl

/-- Slot `3` of the vector `![a,b,c,d,e]`. -/
theorem vec5_val_three {α : Type*} (a b c d e : α) : (![a, b, c, d, e] : Fin 5 → α) 3 = d := rfl

/-- Slot `4` of the vector `![a,b,c,d,e]`. -/
theorem vec5_val_four {α : Type*} (a b c d e : α) : (![a, b, c, d, e] : Fin 5 → α) 4 = e := rfl

/-- `QQ2 5` applied to the uncurried tensor is the ten-fold nested contraction of `N5`. -/
theorem QQ2_five_nested {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (L : (Fin 5 → Fin n) → ℝ) :
    QQ2 5 Γ L L = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q, ∑ r, ∑ s, ∑ t,
      Γ⁻¹ m p * Γ⁻¹ i q * Γ⁻¹ j r * Γ⁻¹ k s * Γ⁻¹ l t
        * L ![m, i, j, k, l] * L ![p, q, r, s, t] := by
  rw [QQ2]
  rw [sum_vec5_pair (fun x y => (∏ d : Fin 5, Γ⁻¹ (x d) (y d)) * L x * L y)]
  simp only [Fin.prod_univ_five, Matrix.cons_val_zero, vec5_val_one, vec5_val_two,
    vec5_val_three, vec5_val_four]

theorem N5_eq_QQ2 {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Curv4 n) :
    N5 Γ T = QQ2 5 Γ (fun x : Fin 5 → Fin n => T (x 0) (x 1) (x 2) (x 3) (x 4))
      (fun x : Fin 5 → Fin n => T (x 0) (x 1) (x 2) (x 3) (x 4)) := by
  set L : (Fin 5 → Fin n) → ℝ := fun x => T (x 0) (x 1) (x 2) (x 3) (x 4) with hL
  rw [QQ2_five_nested Γ L, N5]
  simp only [hL, Matrix.cons_val_zero, vec5_val_one, vec5_val_two, vec5_val_three, vec5_val_four]

end

end Work.Diff.GE
