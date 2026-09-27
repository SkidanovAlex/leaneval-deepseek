import Mathlib
import Submission.Work.EKLC6Core.cutHelpers

/-!
# A uniform entrywise bound for the shape, inherited along atoms

If every `x ∈ Z` has an "atom-mate" `y ∈ H` with `x = u • y` for some `u` in the small ball
`Uball U ρ`, and `C` bounds the entries of every element of `shape A U y` for `y ∈ H`, and
`D` bounds the entries of `g⁻¹` for `g ∈ Uball U ρ`, then `3 * |C| * D` bounds the entries of
every element of `shape A U x` for `x ∈ Z`.

The proof is the "single bound" form of `exists_bound_shape_of_forall_exists_atom_eq_c`: the
shape is a right translate along an atom (`shape_eq_translate_of_atom_eq_c`), so a matrix
`v ∈ shape A U x` factors as `v = v' * u⁻¹` with `v' ∈ shape A U y`, and the product entry
bound `mul_entries_le_c` finishes.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem exists_bound_shape_uniform_of_atom_eq
    {A : MeasurableSpace Work.EKLContract.X3} {U : Subgroup Work.EKLContract.SL3}
    {Z H : Set Work.EKLContract.X3} {ρ C : ℝ}
    (hatom : ∀ x ∈ Z, ∃ y ∈ H, ∃ u ∈ Work.EKLComp.Uball U ρ,
      x = u • y ∧ Work.EKLContract.atom A x = Work.EKLContract.atom A y)
    (hbd : ∀ y ∈ H, ∀ v ∈ Work.EKLContract.shape A U y, ∀ i j : Fin 3,
      |(v : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C)
    {D : ℝ} (hD : ∀ gg ∈ Work.EKLComp.Uball U ρ, ∀ i j : Fin 3,
      |(((gg⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j| ≤ D) (hD0 : 0 ≤ D) :
    ∀ x ∈ Z, ∀ v ∈ Work.EKLContract.shape A U x, ∀ i j : Fin 3,
      |(v : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 3 * |C| * D := by
  intro x hx v hv i j
  obtain ⟨y, hyH, u, huU, hux, hatomeq⟩ := hatom x hx
  subst hux
  rw [shape_eq_translate_of_atom_eq_c huU.1 hatomeq] at hv
  obtain ⟨v', hv', rfl⟩ := hv
  have hcoe : (((v' * u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      = ((v' : SL3) : Matrix (Fin 3) (Fin 3) ℝ) * ((u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [hcoe]
  exact mul_entries_le_c i j (fun k l => le_trans (hbd y hyH v' hv' k l) (le_abs_self C))
    (fun k l => hD u huU k l) (abs_nonneg C) hD0

end Work.EKLC6Core
