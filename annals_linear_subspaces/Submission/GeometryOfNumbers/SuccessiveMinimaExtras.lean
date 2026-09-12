import Mathlib
import Submission.GeometryOfNumbers.SuccessiveMinima

/-!
# Successive minima: realisation lemmas

Extensions of `Submission.SuccessiveMinima`:
- the defining set of the `i`-th successive minimum is upward closed in the radius;
- if `r` is strictly above the `i`-th successive minimum, then the closed ball of radius `r`
  contains `i` linearly independent lattice points (the defining set is upward closed and
  `sInf` is its infimum, so the infimum is "honest").

All results here are Mathlib-only.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module
open scoped ENNReal
set_option linter.unusedSectionVars false

namespace Submission.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The defining set of the `i`-th successive minimum is upward closed in the radius:
if a radius `r` admits `i` linearly independent lattice points of norm `≤ r`, so does any
larger radius. -/
lemma upwardClosed_successiveMinimumSet (L : Submodule ℤ E) (i : ℕ) {r r' : ℝ}
    (hr : r ∈ successiveMinimumSet L i) (hrr' : r ≤ r') :
    r' ∈ successiveMinimumSet L i := by
  rcases hr with ⟨hr0, f, hlin, hnorm⟩
  refine ⟨le_trans hr0 hrr', f, hlin, fun j => le_trans (hnorm j) hrr'⟩

/-- The defining set of the `i`-th successive minimum contains every radius strictly above
the infimum (provided the set is nonempty). -/
lemma mem_successiveMinimumSet_of_sInf_lt (L : Submodule ℤ E) (i : ℕ) {r : ℝ}
    (hr : successiveMinimum L i < r) (hS : (successiveMinimumSet L i).Nonempty) :
    r ∈ successiveMinimumSet L i := by
  -- `r` is not a lower bound of the set (otherwise `sInf ≥ r`), so some `s ∈ S` has `s < r`,
  -- and upward closedness then gives `r ∈ S`.
  by_contra hrS
  have hlb : ∀ s ∈ successiveMinimumSet L i, r ≤ s := by
    intro s hs
    by_contra hlt
    exact hrS (upwardClosed_successiveMinimumSet L i hs (le_of_lt (lt_of_not_ge hlt)))
  have hinf : r ≤ sInf (successiveMinimumSet L i) := le_csInf hS hlb
  exact (not_lt_of_ge hinf) hr

/-- If `r > λᵢ(L)`, then the closed ball of radius `r` contains `i` `ℤ`-linearly independent
elements of `L`. This is the standard "realisation" property of the successive minima. -/
lemma exists_linearIndependent_of_successiveMinimum_lt (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (i : ℕ) (hi : i ≤ Module.finrank ℤ L) {r : ℝ}
    (hr : successiveMinimum L i < r) :
    ∃ f : Fin i → L, LinearIndependent ℤ (fun j : Fin i => (f j : E)) ∧
      ∀ j : Fin i, ‖(f j : E)‖ ≤ r := by
  have hmem : r ∈ successiveMinimumSet L i :=
    mem_successiveMinimumSet_of_sInf_lt L i hr (nonempty_successiveMinimumSet L i hi)
  exact hmem.2

/-- Any nonzero lattice point `v` satisfies `λ₁(L) ≤ ‖v‖`. -/
lemma first_successiveMinimum_le_of_mem {L : Submodule ℤ E} (v : L) (hv : v ≠ 0) :
    successiveMinimum L 1 ≤ ‖(v : E)‖ := by
  have hvE : (v : E) ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    exact h
  haveI : Module.IsTorsionFree ℤ E := by
    refine Module.IsTorsionFree.of_smul_eq_zero (R := ℤ) (M := E) ?_
    intro z m hm
    rw [← Int.cast_smul_eq_zsmul ℝ z m] at hm
    rcases (smul_eq_zero.mp hm) with hz | hm
    · exact Or.inl (Int.cast_eq_zero.mp hz)
    · exact Or.inr hm
  refine successiveMinimum_le_of_exists L 1 (norm_nonneg _) (fun _ : Fin 1 => v) ?_
    (by intro j; simpa using (le_refl ‖(v : E)‖))
  exact (linearIndependent_subsingleton_index_iff (f := fun _ : Fin 1 => (v : E))).2
    (by intro i; exact hvE)

end Submission.SuccessiveMinima
