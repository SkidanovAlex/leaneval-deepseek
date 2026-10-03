import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.ModuleDim
import Submission.Work.ORHughesFree.NaturalExtension.dimOf_principal
import Submission.Work.ORHughesFree.NaturalExtension.rdimAdditivity

universe u

namespace Work.Section3

open Matrix Work.ORHughesFree

/-- **The dimension of the span of a row vector fixed by a projection.**  If `u ∈ S^n` satisfies
`e • u = u` (i.e. `u i = e * u i` for every `i`), then the `1 × n` matrix `M` with row `u`
satisfies `oneByOne e * M = M`, so by (SMat2) `rk M ≤ rk (oneByOne e)`.  Since
`rdim ρ (span {u}) = rk M` (`NaturalExtension.rdim_eq_rk_rows` applied to the single-row matrix
`M`), the claim follows. -/
theorem rdim_span_le_oneByOne {S : Type u} [Ring S] [Work.ORHughesFree.VonNeumannRegularRing S]
    (ρ : Work.ORHughesFree.SylvesterRank S) {n : ℕ} (e : S) (u : Fin n → S) (hu : e • u = u) :
    Work.ORHughesFree.NaturalExtension.rdim ρ (Submodule.span S ({u} : Set (Fin n → S)))
      ≤ ρ.rk 1 1 (Work.ORHughesFree.oneByOne e) := by
  -- The single-row matrix whose row is `u`.
  let M : Matrix (Fin 1) (Fin n) S := fun _ j => u j
  -- Its row span is `span {u}`.
  have hrange : Set.range (fun i : Fin 1 => (fun j : Fin n => M i j)) = {u} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      funext j
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  -- `e` fixes the row of `M` entrywise, hence `oneByOne e * M = M`.
  have hM : Work.ORHughesFree.oneByOne e * M = M := by
    ext i j
    simp only [Work.ORHughesFree.oneByOne, Matrix.mul_apply, Fin.sum_univ_one]
    have h := congrFun hu j
    simpa using h
  calc Work.ORHughesFree.NaturalExtension.rdim ρ (Submodule.span S ({u} : Set (Fin n → S)))
      = Work.ORHughesFree.NaturalExtension.rdim ρ (Submodule.span S
          (Set.range (fun i : Fin 1 => (fun j : Fin n => M i j)))) := by rw [hrange]
    _ = ρ.rk 1 n M := Work.ORHughesFree.NaturalExtension.rdim_eq_rk_rows ρ M
    _ = ρ.rk 1 n (Work.ORHughesFree.oneByOne e * M) := by rw [hM]
    _ ≤ ρ.rk 1 1 (Work.ORHughesFree.oneByOne e) := ρ.rk_mul_le_left _ _

end Work.Section3
