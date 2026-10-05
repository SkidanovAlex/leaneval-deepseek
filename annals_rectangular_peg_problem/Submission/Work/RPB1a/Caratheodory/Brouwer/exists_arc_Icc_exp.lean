import Mathlib

/-!
# A closed proper subset of the circle is contained in a closed arc of length `< 2π`

Given a closed subset `D` of the unit circle `Circle` with `D ≠ univ`, we produce real numbers
`a < b` with `b - a < 2 * Real.pi` and `D ⊆ Circle.exp '' Set.Icc a b`: every point of `D` is
attained by the parametrisation `Circle.exp : ℝ → Circle` at an angle lying in one closed
interval of length strictly smaller than a full turn.

## Idea of the proof

Pick a point `p ∉ D`.  Since `D` is closed, `Dᶜ` is an open neighbourhood of `p`.  As `Circle.exp`
is a local homeomorphism, `p = Circle.exp θ` for `θ = arg p`, and some interval
`Ioo (θ - δ) (θ + δ)` with `0 < δ < π` is mapped entirely into `Dᶜ`.  Thus no point of `D` lies on
the open arc `Circle.exp '' Ioo (θ - δ) (θ + δ)`.

Now let `z ∈ D`.  Using the periodicity of `Circle.exp` with period `2π`
(`Circle.periodic_exp.exists_mem_Ico`), lift `z` to an angle in `Ico (θ + δ) (θ + δ + 2π)`.
That angle cannot exceed `θ - δ + 2π`: otherwise subtracting `2π` would place it in the forbidden
open interval `Ioo (θ - δ) (θ + δ)` while still mapping to `z ∈ D`.  Hence
`z ∈ Circle.exp '' Set.Icc (θ + δ) (θ - δ + 2π)`, and the interval has length `2π - 2δ < 2π`.
-/

open Set Filter

namespace Work.RPB1a.Caratheodory.Brouwer

theorem exists_arc_Icc_exp (D : Set Circle) (hD : IsClosed D) (hne : D ≠ Set.univ) :
    ∃ a b : ℝ, a < b ∧ b - a < 2 * Real.pi ∧ D ⊆ Circle.exp '' Set.Icc a b := by
  -- A point of the circle outside `D`.
  obtain ⟨p, hpD⟩ := Set.nonempty_compl.mpr hne
  set θ : ℝ := Complex.arg (p : ℂ) with hθ
  have hp : Circle.exp θ = p := by rw [hθ]; exact Circle.exp_arg p
  -- An open interval of angles around `θ` whose arc avoids `D`.
  have hmem : Dᶜ ∈ nhds p := hD.isOpen_compl.mem_nhds hpD
  rw [← hp, ← isLocalHomeomorph_circleExp.map_nhds_eq θ, Filter.mem_map] at hmem
  obtain ⟨ε, hεpos, hεsub⟩ := (nhds_basis_Ioo_pos θ).mem_iff.mp hmem
  -- Shrink it so that its length is less than half a turn.
  set δ : ℝ := min ε (Real.pi / 2) with hδ
  have hδpos : 0 < δ := lt_min hεpos (by positivity)
  have hδle : δ ≤ ε := min_le_left _ _
  have hδlt : δ < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_gt_three])
  have hsub : Ioo (θ - δ) (θ + δ) ⊆ Circle.exp ⁻¹' Dᶜ :=
    (Set.Ioo_subset_Ioo (by linarith) (by linarith)).trans hεsub
  refine ⟨θ + δ, θ - δ + 2 * Real.pi, by linarith, by linarith, ?_⟩
  rintro z hzD
  obtain ⟨t, ht⟩ := Circle.exp_surjective z
  obtain ⟨y, hy, hyeq⟩ := Circle.periodic_exp.exists_mem_Ico Real.two_pi_pos t (θ + δ)
  have hyI : y ∈ Icc (θ + δ) (θ - δ + 2 * Real.pi) := by
    refine ⟨hy.1, ?_⟩
    by_contra hcon
    have hcon' : θ - δ + 2 * Real.pi < y := not_le.mp hcon
    have hy' : y - 2 * Real.pi ∈ Ioo (θ - δ) (θ + δ) := by
      constructor <;> linarith [hy.2]
    have hthis : Circle.exp (y - 2 * Real.pi) ∈ Dᶜ := hsub hy'
    have hEq : Circle.exp (y - 2 * Real.pi) = z := by
      rw [Circle.exp_sub_two_pi, ← hyeq, ht]
    rw [hEq] at hthis
    exact hthis hzD
  exact ⟨y, hyI, hyeq.symm.trans ht⟩

end Work.RPB1a.Caratheodory.Brouwer
