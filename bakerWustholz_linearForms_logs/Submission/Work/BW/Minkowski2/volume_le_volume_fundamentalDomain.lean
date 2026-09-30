import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory
open scoped Pointwise

/-- **Minkowski / lattice packing bound.**  If `Λ` is a countable lattice in `Fin d → ℝ`
(i.e. an additive subgroup of the ambient space), `F` a fundamental domain for `Λ` and `S` a
null-measurable set which contains no two points differing by a nonzero element of `Λ`, then
`vol S ≤ vol F`.

The proof is the classical "translate into the fundamental domain" argument: the sets
`g +ᵥ S ∩ F` (for `g : Λ`) are pairwise disjoint as sets (any point of the intersection would
produce two points of `S` differing by the nonzero lattice element `g' - g`), and they are all
contained in `F`.  Hence `measure_le_of_pairwise_disjoint` applied to the fundamental domain
gives `vol S ≤ vol F`. -/
theorem volume_le_volume_fundamentalDomain {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ))
    [Countable Λ] (F : Set (Fin d → ℝ))
    (hF : MeasureTheory.IsAddFundamentalDomain Λ.toAddSubgroup F MeasureTheory.volume)
    {S : Set (Fin d → ℝ)} (hS : MeasureTheory.NullMeasurableSet S MeasureTheory.volume)
    (h : ∀ z ∈ (Λ : Set (Fin d → ℝ)), z ≠ 0 → ∀ x ∈ S, x + z ∉ S) :
    MeasureTheory.volume S ≤ MeasureTheory.volume F := by
  -- It suffices that the translates `g +ᵥ S ∩ F` are pairwise a.e.-disjoint.
  refine hF.measure_le_of_pairwise_disjoint hS ?_
  refine Pairwise.aedisjoint fun g g' hgg' => ?_
  rw [Function.onFun]
  -- in fact they are disjoint as sets
  refine Set.disjoint_left.mpr ?_
  intro x hx hx'
  simp only [Set.mem_inter_iff] at hx hx'
  obtain ⟨hxg, -⟩ := hx
  obtain ⟨hxg', -⟩ := hx'
  rw [Set.mem_vadd_set] at hxg hxg'
  obtain ⟨y, hyS, hyx⟩ := hxg
  obtain ⟨y', hy'S, hy'x⟩ := hxg'
  rw [AddSubmonoid.vadd_def, vadd_eq_add] at hyx hy'x
  -- `z = g' - g` is a nonzero element of the lattice
  have hzmem : ((g' - g : Λ.toAddSubgroup) : Fin d → ℝ) ∈ (Λ : Set (Fin d → ℝ)) := by
    have h1 : ((g' - g : Λ.toAddSubgroup) : Fin d → ℝ) ∈ (Λ.toAddSubgroup : Set (Fin d → ℝ)) :=
      (g' - g).2
    simpa using h1
  have hzne : ((g' - g : Λ.toAddSubgroup) : Fin d → ℝ) ≠ 0 := by
    intro hzero
    apply hgg'
    have hsub : (g' - g : Λ.toAddSubgroup) = 0 := by
      apply Subtype.ext
      simpa using hzero
    exact (sub_eq_zero.mp hsub).symm
  -- and `y' + z = y` is a point of `S`
  have hsum : (g : Fin d → ℝ) + y = (g' : Fin d → ℝ) + y' := by rw [hyx, hy'x]
  have hcoe : ((g' - g : Λ.toAddSubgroup) : Fin d → ℝ) = (g' : Fin d → ℝ) - (g : Fin d → ℝ) := by
    simp
  have heq : y' + ((g' - g : Λ.toAddSubgroup) : Fin d → ℝ) = y := by
    rw [hcoe]
    linear_combination -hsum
  exact h _ hzmem hzne y' hy'S (heq ▸ hyS)

end Work.BW.Minkowski2
