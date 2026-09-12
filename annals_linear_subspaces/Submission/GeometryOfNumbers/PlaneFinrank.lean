import Mathlib
import Submission.GeometryOfNumbers.WedgeBlocks

/-!
# Finrank and nonzero facts for the model planes (coordinate model)

* `finrank_span_range` : `finrank (span (range u)) = k` for a linearly independent
  family `u : Fin k → ℝᵈ`;
* `finrank_modelX` : `finrank (modelX ℓ) = ℓ` for `ℓ ≤ d`;
* `span_range_ne_bot`, `modelX_ne_bot` : nonzero variants (so the challenge-distance bridge
  applies to the pair `(span (range u), modelX ℓ)` when `0 < k ≤ ℓ`).

All Mathlib-only.
-/

noncomputable section

open Module Real
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks

namespace Submission.PlaneFinrank

variable {d : ℕ}

/-- A linearly independent family `u : Fin k → ℝᵈ` spans a `k`-dimensional subspace. -/
lemma finrank_span_range {k : ℕ} (u : Fin k → RD d) (hu : LinearIndependent ℝ u) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range u)) = k := by
  simpa using (finrank_span_eq_card (R := ℝ) hu)

/-- The model plane `x₀ = Span { e_i | i < ℓ }` has dimension `ℓ` (for `ℓ ≤ d`). -/
lemma finrank_modelX (ℓ : ℕ) (hℓd : ℓ ≤ d) :
    Module.finrank ℝ (modelX (d := d) ℓ) = ℓ := by
  classical
  let f : Fin ℓ → RD d := fun j => (B d) (Fin.castLE hℓd j)
  have hf_li : LinearIndependent ℝ f := by
    dsimp [f]
    exact (B d).toBasis.linearIndependent.comp (Fin.castLE hℓd) (Fin.castLE_injective hℓd)
  have hspan : Submodule.span ℝ (Set.range f) = modelX (d := d) ℓ := by
    unfold modelX
    apply congrArg (Submodule.span ℝ)
    ext e
    constructor
    · intro he
      rcases (Set.mem_range.mp he) with ⟨j, rfl⟩
      refine ⟨Fin.castLE hℓd j, j.isLt, rfl⟩
    · intro he
      rcases he with ⟨i, hi, rfl⟩
      refine ⟨⟨i.val, hi⟩, ?_⟩
      apply congrArg (B d)
      apply Fin.ext
      rfl
  have hfin : Module.finrank ℝ (modelX (d := d) ℓ) = Fintype.card (Fin ℓ) := by
    rw [← hspan]
    exact finrank_span_eq_card (R := ℝ) hf_li
  simpa using hfin

/-- For `k > 0`, an independent family spans a nonzero plane. -/
lemma span_range_ne_bot {k : ℕ} (hk : 0 < k) (u : Fin k → RD d) (hu : LinearIndependent ℝ u) :
    (Submodule.span ℝ (Set.range u)) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨u ⟨0, hk⟩, ?_, hu.ne_zero ⟨0, hk⟩⟩
  exact Submodule.subset_span ⟨⟨0, hk⟩, rfl⟩

/-- For `0 < ℓ ≤ d`, the model plane `x₀` is nonzero. -/
lemma modelX_ne_bot (ℓ : ℕ) (hℓpos : 0 < ℓ) (hℓd : ℓ ≤ d) :
    modelX (d := d) ℓ ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨(B d) (⟨0, lt_of_lt_of_le hℓpos hℓd⟩ : Fin d), ?_, ?_⟩
  · exact std_mem_modelX (d := d) ℓ (⟨0, lt_of_lt_of_le hℓpos hℓd⟩ : Fin d) hℓpos
  · exact (B d).toBasis.linearIndependent.ne_zero ⟨0, lt_of_lt_of_le hℓpos hℓd⟩

end Submission.PlaneFinrank
