import ChallengeDeps
import Submission.ScatFlux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exterior form and integral identity for the *chosen* scattering solution

In the `a v ≠ 0` branch of `theorem_1_2` a radial scattering solution exists
(`h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`), and the scattering length
is defined from the chosen one `w₀ := Classical.choose h`:

    a v = (8π)⁻¹ · ∫ v(1−w₀)      (`ScatteringDefs.a_eq_integral_of_exists`).

Combining the exterior form (`ScatExterior.scattering_solution_exterior_form`:
`w₀ = c/‖x‖` a.e. outside the support) with the Gauss/shell identity
(`ScatFlux.scattering_flux`: `c = (8π)⁻¹∫v(1−w₀)`) gives the two facts the
box-bound proof needs:

1. `chosen_scattering_av_exterior`: `w₀ x = a v / ‖x‖` a.e. for `‖x‖ ≥ R`;
2. `chosen_scattering_integral`: `∫v(1−w₀) = 8π·a v`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The chosen scattering solution equals `a v / ‖x‖` a.e. on the exterior
`{x | R ≤ ‖x‖}`.  (This is the `omega_outside_support` scattering fact, in
the chosen-solution form used by the box bound.) -/
theorem chosen_scattering_av_exterior {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ᵐ x : ℝ³, R ≤ ‖x‖ → (Classical.choose h) x = a v / ‖x‖ := by
  let w₀ : ℝ³ → ℝ := Classical.choose h
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial w₀ := hspec.1
  have hw₀ : IsScatteringSolution w₀ v := hspec.2
  -- exterior form: w₀ = c/‖x‖ a.e. on the exterior
  rcases scattering_solution_exterior_form (w := w₀) (v := v) (R := R) hR hrad₀ hw₀ hv_supp with
    ⟨c, hform⟩
  -- flux: c = (8π)⁻¹∫v(1−w₀) = a v
  have hc : c = a v := by
    have hcflux : c = (1 / (8 * π)) * (∫ x : ℝ³, v x * (1 - w₀ x)) :=
      scattering_flux (v := v) (w := w₀) (R := R) hR hrad₀ hw₀ hv_supp (c := c) hform
    have hav : a v = (1 / (8 * π)) * (∫ x : ℝ³, v x * (1 - w₀ x)) := by
      simpa [w₀] using (a_eq_integral_of_exists v h)
    linarith
  -- substitute c = a v into the a.e. form
  filter_upwards [hform] with x hx
  rw [← hc]
  exact hx

/-- `∫ v(1−w₀) = 8π · a v` for the chosen solution (arithmetic from the
defining identity of `a v`). -/
lemma chosen_scattering_integral {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ x : ℝ³, v x * (1 - (Classical.choose h) x)) = 8 * π * a v := by
  have hav := a_eq_integral_of_exists v h
  have h8 : (8 * π : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  rw [hav]
  field_simp [h8]

end Submission.BoseGases
