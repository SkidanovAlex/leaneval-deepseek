/-
`Work.CORE4.A7S4.n2Check`: the `N_{A₇}(V₂)` companion fact, verified case by case.

For each of the `9` involutions `s ∈ n2Inv` and each of the `8` elements `k ∈ n2Ord3` with
`s k s⁻¹ = k⁻¹` we exhibit a *companion* `k' ∈ n2Ord3` with `s k' s⁻¹ = k'⁻¹`,
`k' ≠ k`, `k' ≠ k * k`; in the remaining (finitely many, decidable) cases the hypothesis
`s k s⁻¹ = k⁻¹` is false for the two concrete permutations, which is again decided by `decide`.
-/
import Mathlib
import Submission.Work.CORE4.A7S4Defs

namespace Work.CORE4.A7S4

/-- The eight elements of `n2Ord3`, named for use as witnesses. -/
private def W0 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)) *
    (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7))

private def W1 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) *
    (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7))

private def W2 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)) *
    (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7))

private def W3 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7)) *
    (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7))

theorem n2Check : ∀ s : Equiv.Perm (Fin 7), s ∈ n2Inv → ∀ k : Equiv.Perm (Fin 7), k ∈ n2Ord3 → s * k * s⁻¹ = k⁻¹ → ∃ k' : Equiv.Perm (Fin 7), k' ∈ n2Ord3 ∧ InN2P k' ∧ Equiv.Perm.sign k' = 1 ∧ k' * k' * k' = 1 ∧ k' ≠ 1 ∧ s * k' * s⁻¹ = k'⁻¹ ∧ k' ≠ k ∧ k' ≠ k * k := by
  intro s hs k hk h
  simp only [n2Inv, Finset.mem_insert, Finset.mem_singleton] at hs
  simp only [n2Ord3, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd h (by decide)
        | exact ⟨W0, by decide⟩
        | exact ⟨W1, by decide⟩
        | exact ⟨W2, by decide⟩
        | exact ⟨W3, by decide⟩

end Work.CORE4.A7S4
