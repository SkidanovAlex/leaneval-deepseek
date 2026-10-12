import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.BoseFixB1B.ae_profile_norm_transfer
import Submission.Work.BoseFixB1B.bornGap
import Submission.Work.BoseFixB1B.secant_div_le_of_concaveOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.w0_ge_const_on_ball` — a quantitative lower bound for the scattering
solution inside the support ball

If `0 ≤ v` is radial with `tsupport v ⊆ ball 0 R0` and `w₀` is *the* chosen radial scattering
solution of `v` (`w₀ = Classical.choose h`, `h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`),
then almost everywhere on `ball 0 R0`,

    `a v / (2·R0) ≤ w₀ z`.

## Route

Write `U := canonicalProfile v w₀ R0`.  The corpus knows

* `canonicalProfile_concaveOn_Icc`: `U` is concave on `[0,R0]` (this is the classical fact that
  the scattering profile `r ↦ r·ω(r)` of a nonnegative potential has antitone secant slope);
* `canonicalProfile_zero`: `U 0 = 0`;
* `canonicalProfile_at_R_eq_a`: `U R0 = a v` (the profile at the right endpoint is the scattering
  length, `canonicalProfile v w₀ R0 R0 = (8π)⁻¹∫v(1−w₀) = a v`);
* `canonicalProfile_eq_profile` (`Submission.ProfileFormula`): `U r = r·radialProfile w₀ r` for
  almost every `r > 0`;
* `scattering_bounds_ae`: `0 ≤ w₀` almost everywhere.

Concavity with `U 0 = 0` gives `U r ≥ (r/R0)·U R0 = (r/R0)·a v` for `0 < r < R0`, i.e.
`radialProfile w₀ r ≥ a v / R0` for a.e. `r`; radiality (`radial_eq_profile`) transfers this to
`w₀ z ≥ a v / R0` for a.e. `z` with `0 < ‖z‖` (the norm-preimage of a null set of radii is null:
`Submission.BoseGases.volume_preimage_norm_null`).  Since `R0 ≤ 2 R0`, this is stronger than the
claimed `a v / (2 R0)` when `a v ≥ 0`; if `a v < 0` the claim follows from `0 ≤ w₀` a.e.

The two independent pieces of the argument are delegated:
`Work.BoseFixB1B.secant_div_le_of_concaveOn` (the concavity/arithmetic step) and
`Work.BoseFixB1B.ae_profile_norm_transfer` (the a.e. transfer from radii to `ℝ³`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

theorem w0_ge_const_on_ball {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ‖z‖ < R0 → _root_.BoseGases.a v / (2 * R0) ≤ Classical.choose h z := by
  classical
  have hrad : _root_.BoseGases.IsRadial (Classical.choose h) := (Classical.choose_spec h).1
  have hwsol : _root_.BoseGases.IsScatteringSolution (Classical.choose h) v :=
    (Classical.choose_spec h).2
  -- the canonical profile `U` of `w₀` and its three structural properties
  have hUR : Submission.BoseGases.canonicalProfile v (Classical.choose h) R0 R0 =
      _root_.BoseGases.a v :=
    canonicalProfile_at_R_eq_a (v := v) (R := R0) hR0 hvrad hv_supp h
  have hconc : ConcaveOn ℝ (Set.Icc 0 R0)
      (Submission.BoseGases.canonicalProfile v (Classical.choose h) R0) :=
    canonicalProfile_concaveOn_Icc (v := v) (w := Classical.choose h) (R := R0)
      hR0 hv hvrad hv_supp hrad hwsol
  have hprof := Submission.BoseGases.canonicalProfile_eq_profile (v := v)
    (w := Classical.choose h) (R := R0) hR0 hvrad hv_supp hrad hwsol
  -- a.e. statements: the profile identity at `‖z‖`, nonnegativity, and `z ≠ 0`
  have htransfer := ae_profile_norm_transfer (w := Classical.choose h) hrad hprof
  have hnn : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³),
      0 ≤ Classical.choose h x :=
    (Submission.BoseGases.scattering_bounds_ae (v := v) (w := Classical.choose h) (R := R0)
      hR0 hv hvrad hv_supp hrad hwsol).1
  have hne : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [htransfer, hnn, hne] with z hzprof hznn hzne
  intro hzR
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  -- the secant inequality `U R0 / R0 ≤ U ‖z‖ / ‖z‖`, rewritten as `a v / R0 ≤ w₀ z`
  have hsec := secant_div_le_of_concaveOn
    (U := Submission.BoseGases.canonicalProfile v (Classical.choose h) R0)
    hR0 hconc (Submission.BoseGases.canonicalProfile_zero v (Classical.choose h) R0) hz0 hzR
  rw [hUR] at hsec
  rw [hzprof hz0] at hsec
  rw [mul_div_cancel_left₀ (Classical.choose h z) (ne_of_gt hz0)] at hsec
  -- conclude, splitting on the sign of the scattering length
  by_cases hav : 0 ≤ _root_.BoseGases.a v
  · calc _root_.BoseGases.a v / (2 * R0) ≤ _root_.BoseGases.a v / R0 :=
        div_le_div_of_nonneg_left hav hR0 (by linarith)
      _ ≤ Classical.choose h z := hsec
  · have hav' : _root_.BoseGases.a v < 0 := not_le.mp hav
    have h1 : _root_.BoseGases.a v / (2 * R0) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hav'.le (by linarith)
    linarith

end Work.BoseFixB1B
