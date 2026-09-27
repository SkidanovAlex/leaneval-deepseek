import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.cutHelpers

/-!
# Boundedness of the shape is an atom property

If the atom `[x]_A` is carried by the `U`-orbit of `x`, and `[x]_A = [y]_A`, then the shape
`shape A U ·` at the two points is the same up to *right translation* by an element `u ∈ U` with
`u • x = y` (`Work.EKLC6Core.shape_eq_translate_of_atom_eq_c`).  Hence an entrywise bound on the
shape at `y` transfers to an entrywise bound at `x`: a matrix `v ∈ shape A U x` satisfies
`v = (v u⁻¹) · u` with `v u⁻¹ ∈ shape A U y`, so its entries are bounded by
`3 · C · (entry bound of u)` (`Work.EKLC6Core.mul_entries_le_c`).

This is the single-point form of the "entrywise bound" clause of `IsPlaqueAlgebra`.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem exists_bound_shape_of_atom_eq
    {A : MeasurableSpace Work.EKLContract.X3} {U : Subgroup Work.EKLContract.SL3}
    {x y : Work.EKLContract.X3}
    (horb : Work.EKLContract.atom A x ⊆
      (fun u : Work.EKLContract.SL3 => u • x) '' (U : Set Work.EKLContract.SL3))
    (hatom : Work.EKLContract.atom A x = Work.EKLContract.atom A y)
    (hbd : ∃ C : ℝ, ∀ v ∈ Work.EKLContract.shape A U y, ∀ i j : Fin 3, |v i j| ≤ C) :
    ∃ C : ℝ, ∀ v ∈ Work.EKLContract.shape A U x, ∀ i j : Fin 3, |v i j| ≤ C := by
  -- `y` lies in the atom of `x`, so `y = u • x` for some `u ∈ U`
  have hy : y ∈ atom A x := by rw [hatom]; exact mem_atom_self_c A y
  obtain ⟨u, huU, hux⟩ := horb hy
  have hatomeq : atom A (u • x) = atom A x := by
    rw [show u • x = y from hux]; exact hatom.symm
  obtain ⟨C, hC⟩ := hbd
  -- an entrywise bound `D` for the fixed group element `u`
  set D : ℝ := ∑ k : Fin 3, ∑ l : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) k l| with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]; exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg _
  have hDu : ∀ i j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ D := by
    intro i j
    rw [hDdef]
    have h1 : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ ∑ l : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i l| :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun l => |(u : Matrix (Fin 3) (Fin 3) ℝ) i l|)
        (fun l _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ l : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i l|)
        ≤ ∑ k : Fin 3, ∑ l : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) k l| :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun k => ∑ l : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) k l|)
        (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg _) (Finset.mem_univ i)
    exact le_trans h1 h2
  refine ⟨3 * |C| * D, fun v hv i j => ?_⟩
  -- the shape at `y = u • x` is the right translate by `u⁻¹` of the shape at `x`
  have hshape : shape A U y = (fun s : SL3 => s * u⁻¹) '' shape A U x := by
    rw [← hux, shape_eq_translate_of_atom_eq_c huU hatomeq]
  have hvu : v * u⁻¹ ∈ shape A U y := by
    rw [hshape]; exact ⟨v, hv, rfl⟩
  have hbound : ∀ k l, |((v * u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ |C| :=
    fun k l => le_trans (hC _ hvu k l) (le_abs_self C)
  have hcoe : ((v : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = ((v * u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) * ((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul]
    have h : (v * u⁻¹) * u = v := by group
    rw [h]
  rw [hcoe]
  exact mul_entries_le_c i j hbound hDu (abs_nonneg C) hD0

end Work.EKLC6Core
