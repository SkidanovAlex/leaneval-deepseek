import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.PotSharp
import Submission.Work.SmallBoxA0.g0_rotation_invariant
import Submission.Work.SmallBoxA0.radial_coulomb_nonneg
import Submission.Work.SmallBoxA0.radial_rep_of_rotation_invariant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Nonnegativity of the `ĝω(0)`-mass for an arbitrary weak scattering solution.**
For any real potential `v` (NO sign hypothesis `0 ≤ v` and NO radiality hypothesis
`IsRadial v`) which has a radial weak scattering solution `w₀ := Classical.choose h`
with `tsupport v ⊆ ball 0 R`, `R > 0`, the Newtonian self-energy
`g0w0Mass v h = ∫ z, (v z * (1 − w₀ z)) * w₀ z` is nonnegative.  Mathematically
this is `∫ g₀ w₀ = 2∫ ‖∇w₀‖² = (1/(8π))∬ g₀(x)g₀(y)/‖x−y‖ ≥ 0`, `g₀ := v(1−w₀)`;
it is *not* covered by the corpus's `SmallBoxBogMainTerm.g0w0Mass_nonneg`
(which needs `0 ≤ v` and `IsRadial v` and uses the maximum principle `0 ≤ w₀ ≤ 1`).

Suggested routes (either suffices):

* *Spherical-mean / 1D-energy route.*  `w₀` is radial, so the weak equation restricted
  to radial test functions is the *spherically averaged* 1D equation: with
  `ṽ(r) := ⨍_{S²} v(rω)dω` (the spherical mean of `v`) and `U(r) := r·w₀(r·radU0)`,
  one has `U'' = (ṽ/2)(U − id)` a.e. (the corpus's `ScatProfileODE.scat_profile_ODE_ae`
  re-run with the spherically averaged source; its `IsRadial v` hypothesis is used
  only for the identification `radialProfile v = v`, while the spherical mean of
  `g₀ = v(1−w₀)` is `ṽ(r)·(1−W(r))` because `1−w₀` is radial).  Polar coordinates give
  `g0w0Mass = ∫ g₀ w₀ = 4π∫₀^∞ ṽ(r)(1−W(r))W(r) r² dr = −8π∫₀^∞ U'' U
             = 8π∫₀^∞ (U')² ≥ 0`.
* *Rotational route.*  `g₀` is rotation-invariant a.e. (test the weak equation
  against `φ∘R` and use `Δ(φ∘R) = (Δφ)∘R` plus radiality of `w₀`); hence the
  spherical mean `G` of `g₀` satisfies `G =ᵐ g₀`, and `ṽ(x) := G(x)/(1−w₀(x))`
  (`0` where `1−w₀ = 0`) is radial with `tsupport ṽ ⊆ ball 0 (R+1)` and
  `ṽ(1−w₀) =ᵐ g₀`, so `w₀` is a scattering solution of `ṽ`.  The corpus's
  `ScatGIntegrals.scattering_newton_double_eq` at `(ṽ, w₀, R+1)` gives
  `∬g₀g₀/‖x−y‖ = 8π·g0w0Mass`, and the Riesz factorisation
  `‖x−y‖⁻¹ = π⁻³∫‖x−z‖⁻²‖z−y‖⁻²dz` makes the double integral a square
  (`π⁻³∫(∫g₀(z)‖·−z‖⁻²)² ≥ 0`).  This route uses the sibling delegated lemma
  `coulomb_form_nonneg` for the last step. -/
lemma g0w0Mass_nonneg_general {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ g0w0Mass (v := v) h := by
  let w₀ : ℝ³ → ℝ := Classical.choose h
  have hspec : IsRadial w₀ ∧ IsScatteringSolution w₀ v := Classical.choose_spec h
  have hrad₀ : IsRadial w₀ := hspec.1
  have hw₀ : IsScatteringSolution w₀ v := hspec.2
  have hrot : ∀ A : ℝ³ ≃ₗᵢ[ℝ] ℝ³, g0 v h =ᵐ[volume] fun x => g0 v h (A x) :=
    fun A => g0_rotation_invariant hR hv_supp h A
  have hg0int : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0li : LocallyIntegrable (g0 v h) := hg0int.locallyIntegrable
  have hg0supp : tsupport (g0 v h) ⊆ ball (0 : ℝ³) R := by
    have hsuppsub : Function.support (g0 v h) ⊆ Function.support v := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [g0, h0])
    exact subset_trans (closure_mono hsuppsub) hv_supp
  obtain ⟨g, hgrad, hgli, hgaeeq, hgsupp⟩ :=
    radial_rep_of_rotation_invariant hrot hg0li hg0supp
  have hgint : Integrable g := hg0int.congr hgaeeq
  let vt : ℝ³ → ℝ := fun x => g x * (1 - w₀ x)⁻¹
  have hAeq : (fun x => vt x * (1 - w₀ x)) =ᵐ[volume] g := by
    filter_upwards [hgaeeq] with x hx
    have hx3 : g x = v x * (1 - w₀ x) := hx.symm
    dsimp only [vt]
    by_cases h0 : 1 - w₀ x = 0
    · rw [h0, mul_zero, hx3, h0, mul_zero]
    · rw [mul_assoc, inv_mul_cancel₀ h0, mul_one]
  have hvtrad : IsRadial vt := by
    intro x y hxy
    have h1 : g x = g y := hgrad x y hxy
    have h2 : w₀ x = w₀ y := hrad₀ x y hxy
    simp only [vt, h1, h2]
  have hvtsupp : tsupport vt ⊆ ball (0 : ℝ³) R := by
    have hsuppsub : Function.support vt ⊆ Function.support g := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [vt, h0])
    exact subset_trans (closure_mono hsuppsub) hgsupp
  have hvtli : LocallyIntegrable (vt * (1 - w₀)) := hgli.congr hAeq.symm
  have hvtscat : IsScatteringSolution w₀ vt := by
    refine ⟨hw₀.lhs_integrable, hvtli, ?_, hw₀.lim⟩
    intro φ hφ
    have hveq : (fun x => vt x * (1 - w₀ x) * φ x) =ᵐ[volume]
        (fun x => v x * (1 - w₀ x) * φ x) := by
      filter_upwards [hAeq, hgaeeq] with x hx hg
      have hgx : g x = v x * (1 - w₀ x) := by rw [← hg]; rfl
      rw [hx, hgx]
    have hI : (∫ x, vt x * (1 - w₀ x) * φ x) = ∫ x, v x * (1 - w₀ x) * φ x :=
      integral_congr_ae hveq
    rw [hI]
    exact hw₀.eq φ hφ
  have hdouble := scattering_newton_double_eq (v := vt) (w := w₀) hR hvtrad hvtsupp hrad₀ hvtscat
  have hL : (∫ x, ∫ y, (vt x * (1 - w₀ x)) * (vt y * (1 - w₀ y)) * (‖x - y‖ : ℝ)⁻¹)
      = ∫ x, ∫ y, g x * g y * (‖x - y‖ : ℝ)⁻¹ := by
    apply integral_congr_ae
    filter_upwards [hAeq] with x hx
    rw [hx]
    apply integral_congr_ae
    filter_upwards [hAeq] with y hy
    rw [hy]
  have hRhs : (∫ x, (vt x * (1 - w₀ x)) * w₀ x) = ∫ x, g x * w₀ x := by
    apply integral_congr_ae
    filter_upwards [hAeq] with x hx
    rw [hx]
  have hmain : (∫ x, ∫ y, g x * g y * (‖x - y‖ : ℝ)⁻¹) = 8 * Real.pi * (∫ x, g x * w₀ x) := by
    rw [← hL, hdouble, hRhs]
  have hgw0 : ∫ x, g x * w₀ x = g0w0Mass (v := v) h := by
    rw [g0w0Mass]
    apply integral_congr_ae
    filter_upwards [hgaeeq] with x hx
    rw [hx]
  have hnn := radial_coulomb_nonneg hgrad hgint hgsupp
  have h8 : (0 : ℝ) < 8 * Real.pi := by positivity
  rw [hgw0] at hmain
  nlinarith [hmain, hnn, h8]

end Work.SmallBoxA0
