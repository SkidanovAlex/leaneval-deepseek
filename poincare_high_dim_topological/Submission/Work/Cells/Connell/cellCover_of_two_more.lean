import Mathlib
import Submission.Work.PL.Defs

/-!
# Padding a family of open cells by two more

If `U₁`, `U₂` are open `n`-cells and `W : Fin k → Set M` is a `k`-indexed family of open
`n`-cells whose union together with `U₁ ∪ U₂` covers `M`, then `M` admits a `PL.CellCover`
by `k + 2` open `n`-cells.

The combined family is `Fin.append W ![U₁, U₂] : Fin (k + 2) → Set M`, whose union is
`(⋃ i, W i) ∪ U₁ ∪ U₂ = univ` by `hcover`.
-/

namespace Work.Cells.Connell

theorem cellCover_of_two_more {n : ℕ} {M : Type*} [TopologicalSpace M] {k : ℕ}
    {W : Fin k → Set M} (hW : ∀ i, PL.IsOpenCell n (W i))
    (U₁ U₂ : Set M) (h₁ : PL.IsOpenCell n U₁) (h₂ : PL.IsOpenCell n U₂)
    (hcover : ∀ x : M, x ∈ U₁ ∨ x ∈ U₂ ∨ ∃ i : Fin k, x ∈ W i) :
    PL.CellCover n M (k + 2) := by
  refine ⟨Fin.append W (fun j : Fin 2 => if j = 0 then U₁ else U₂), ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact hW i
    · rw [Fin.append_right]
      fin_cases i
      · simpa using h₁
      · simpa using h₂
  · apply Set.eq_univ_of_forall
    intro x
    rcases hcover x with hx | hx | ⟨i, hi⟩
    · exact Set.mem_iUnion.mpr ⟨Fin.natAdd k 0, by rw [Fin.append_right]; simpa using hx⟩
    · exact Set.mem_iUnion.mpr ⟨Fin.natAdd k 1, by rw [Fin.append_right]; simpa using hx⟩
    · exact Set.mem_iUnion.mpr ⟨Fin.castAdd 2 i, by rw [Fin.append_left]; exact hi⟩

end Work.Cells.Connell
