import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic

namespace Commons.Logic.Equiv

/-- For a type with decidable equality, given two distinct points `p q` and two
distinct targets `x y`, there is a permutation sending `p ↦ x` and `q ↦ y`.
This is the (sharply) 2-transitivity of the symmetric group on a type with at
least two elements. -/
theorem exists_equiv_apply_eq {α : Type*} [DecidableEq α] {p q x y : α}
    (hpq : p ≠ q) (hxy : x ≠ y) :
    ∃ τ : α ≃ α, τ p = x ∧ τ q = y := by
  -- `swap p x` is an involution.
  have hinv : ∀ z, Equiv.swap p x (Equiv.swap p x z) = z := by
    intro z
    exact congrArg (fun e : α ≃ α => e z) (Equiv.swap_swap p x)
  -- Take `τ = (swap q (swap p x y)).trans (swap p x)`, i.e. first swap `q` with
  -- `(swap p x) y`, then apply `swap p x`.
  refine ⟨(Equiv.swap q (Equiv.swap p x y)).trans (Equiv.swap p x), ?_, ?_⟩
  · -- `τ p = x`:  need `p` fixed by the first swap, i.e. `p ≠ q` and `p ≠ swap p x y`.
    change Equiv.swap p x (Equiv.swap q (Equiv.swap p x y) p) = x
    have hpne : p ≠ Equiv.swap p x y := by
      intro h
      have h4 : Equiv.swap p x p = Equiv.swap p x (Equiv.swap p x y) :=
        congrArg (Equiv.swap p x) h
      rw [Equiv.swap_apply_left] at h4
      rw [hinv] at h4
      exact hxy h4
    rw [Equiv.swap_apply_of_ne_of_ne hpq hpne, Equiv.swap_apply_left]
  · -- `τ q = y`:  `(swap q (swap p x y)) q = swap p x y`, and `swap p x` is an involution.
    change Equiv.swap p x (Equiv.swap q (Equiv.swap p x y) q) = y
    rw [Equiv.swap_apply_left, hinv y]

/-- For `n : ℕ` and distinct `a j : Fin (n + 1)`, there is a permutation of
`Fin (n + 1)` sending `0 ↦ a` and `1 ↦ j`. -/
theorem exists_equiv_zero_one {n : ℕ} {a j : Fin (n + 1)} (haj : a ≠ j) :
    ∃ τ : Fin (n + 1) ≃ Fin (n + 1), τ 0 = a ∧ τ 1 = j := by
  by_cases hn : n = 0
  · -- Vacuously true: `Fin 1` is a subsingleton, so `a = j`.
    subst hn
    exact absurd ((Fin.eq_zero a).trans (Fin.eq_zero j).symm) haj
  · -- `0 ≠ 1` in `Fin (n + 1)` since `n + 1 ≥ 2`.
    have h01 : (0 : Fin (n + 1)) ≠ 1 := by
      have h2 : 1 < n + 1 := by omega
      intro h
      have hv : ((0 : Fin (n + 1)) : ℕ) = ((1 : Fin (n + 1)) : ℕ) := congrArg Fin.val h
      rw [Fin.val_one', Nat.mod_eq_of_lt h2] at hv
      simp at hv
    exact exists_equiv_apply_eq h01 haj

end Commons.Logic.Equiv