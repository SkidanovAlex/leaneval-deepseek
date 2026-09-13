import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra.Submodule

open Module
open scoped Pointwise

/-- If `W ≤ B` are submodules of a finite-dimensional space and `finrank W < finrank B`,
then there is a vector `x` of `B` outside `W`. -/
lemma exists_mem_of_finrank_lt {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {W B : Submodule K V} (hWB : W ≤ B)
    (hlt : Module.finrank K W < Module.finrank K B) :
    ∃ x : V, x ∈ B ∧ x ∉ W := by
  classical
  -- If every element of `B` lay in `W`, then `B = W`, contradicting the strict rank inequality.
  have hnot : ¬ B ≤ W := by
    intro hBW
    have hBeq : B = W := le_antisymm hBW hWB
    rw [hBeq] at hlt
    exact (lt_irrefl (Module.finrank K W)) hlt
  -- hence `(B : Set V) \ (W : Set V)` is nonempty
  have hnon : ((B : Set V) \ (W : Set V)).Nonempty := by
    exact Set.sdiff_nonempty.mpr (mt (SetLike.coe_subset_coe.mp) hnot)
  rcases hnon with ⟨x, hxB, hxW⟩
  exact ⟨x, by simpa using hxB, by simpa using hxW⟩

/-- The interval of submodules between `A` and `B` in a finite-dimensional space contains
a submodule of any rank `ℓ` between `finrank A` and `finrank B`. -/
theorem exists_submodule_between_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (A B : Submodule K V) (hAB : A ≤ B) {ℓ : ℕ}
    (hA : Module.finrank K A ≤ ℓ) (hℓ : ℓ ≤ Module.finrank K B) :
    ∃ W : Submodule K V, A ≤ W ∧ W ≤ B ∧ Module.finrank K W = ℓ := by
  classical
  let rec go : (W : Submodule K V) → W ≤ B → Module.finrank K W ≤ ℓ →
      ∃ W', W ≤ W' ∧ W' ≤ B ∧ Module.finrank K W' = ℓ :=
    fun W hWB hWl => by
      by_cases hEq : Module.finrank K W = ℓ
      · exact ⟨W, le_rfl, hWB, hEq⟩
      · have hlt : Module.finrank K W < ℓ := lt_of_le_of_ne hWl hEq
        have hltB : Module.finrank K W < Module.finrank K B :=
          lt_of_lt_of_le hlt hℓ
        rcases exists_mem_of_finrank_lt (W := W) (B := B) hWB hltB with ⟨x, hxB, hxW⟩
        have hsup_le : W ⊔ Submodule.span K {x} ≤ B := by
          exact sup_le hWB ((Submodule.span_singleton_le_iff_mem x B).mpr hxB)
        have hfin : Module.finrank K ↥(W ⊔ Submodule.span K {x}) =
            Module.finrank K W + 1 := by
          exact Submodule.finrank_sup_span_singleton (p := W) (v := x) hxW
        have hsupl : Module.finrank K ↥(W ⊔ Submodule.span K {x}) ≤ ℓ := by
          rw [hfin]
          exact Nat.succ_le_of_lt hlt
        rcases go (W ⊔ Submodule.span K {x}) hsup_le hsupl with ⟨W', hWW', hW'B, hfin'⟩
        exact ⟨W', le_trans le_sup_left hWW', hW'B, hfin'⟩
  termination_by W _ _ => ℓ - Module.finrank K W
  decreasing_by
    rw [hfin]
    omega
  exact go A hAB hA

end Commons.LinearAlgebra.Submodule