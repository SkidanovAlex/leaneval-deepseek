import ChallengeDeps
import Submission.ScatGIntegrals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Chosen-branch `g`-integral corollaries (Layer 3 interface for Layer 5)

In the `a v ≠ 0` branch of Theorem 1.2 the scattering length is realized by
the chosen radial scattering solution `w₀ := Classical.choose h`
(`h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`), with

    g₀ := v·(1−w₀),    ∫g₀ = 8π·a v          (ScatChosen.chosen_scattering_integral)
    0 ≤ w₀ ≤ 1 a.e.,  g₀ ≥ 0 a.e., w₀ = a v/‖x‖ a.e. on the exterior
                                               (ScatT3.scattering_bounds_ae / scattering_g_nonneg /
                                                ScatChosen.chosen_scattering_av_exterior)
    0 < a v ≤ R                                (ScatT3.chosen_av_bounds in the a v ≠ 0 branch)

This module instantiates the `g`-integral machinery of `ScatGIntegrals` for
`w₀`, recording the bounds that the Fournais--Solovej box-bound package needs
in terms of `ĝ(0) := ∫g₀ = 8π a v` and `ĝω(0) := ∫g₀·w₀ ∈ [0, 8π a v]`:

  * `chosen_gomega_integral_bounds` — `0 ≤ ∫g₀·w₀ ≤ 8π·a v`;
  * `chosen_newton_double_eq` — `∫∫ g₀(x)g₀(y)/‖x−y‖ = 8π·∫g₀·w₀`;
  * `chosen_newton_double_le` — `∫∫ g₀(x)g₀(y)/‖x−y‖ ≤ (8π)²·a v`.

(For completeness the module also records `chosen_g1pomega_integral_le`:
`∫v(1−w₀)·(1+w₀) ∈ [8π a v, 16π a v]`, the `w₂`-type quantity of FS
eq:w2int: `(1/2)∫g(1+ω)`.)  All statements require only the existence
hypothesis `h` (no separate `a v ≠ 0` hypothesis is needed except where
`0 < a v` is used; the bounds below are stated with `0 ≤ a v`, which holds by
`ScatT3.chosen_av_bounds_weak`).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `0 ≤ ∫g₀·w₀ ≤ ∫g₀ = 8π·a v` for the chosen scattering solution. -/
theorem chosen_gomega_integral_bounds {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * Classical.choose h x) ∧
      (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * Classical.choose h x) ≤
        8 * π * a v := by
  let w₀ : ℝ³ → ℝ := Classical.choose h
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial w₀ := hspec.1
  have hw₀ : IsScatteringSolution w₀ v := hspec.2
  have hb := scat_gomega_integral_bounds (w := w₀) hR hv_nonneg hvrad hv_supp hrad₀ hw₀
  have hg : (∫ x : ℝ³, v x * (1 - w₀ x)) = 8 * π * a v := by
    simpa [w₀] using (chosen_scattering_integral (v := v) h)
  constructor
  · simpa [w₀] using hb.1
  · calc
      (∫ x : ℝ³, (v x * (1 - w₀ x)) * w₀ x) ≤ (∫ x : ℝ³, v x * (1 - w₀ x)) := hb.2
      _ = 8 * π * a v := hg


/-- `∫∫ g₀(x)·g₀(y)/‖x−y‖ dx dy = 8π·∫g₀·w₀` (the Newton double-integral
identity for the chosen scattering solution). -/
theorem chosen_newton_double_eq {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ x : ℝ³, ∫ y : ℝ³,
        (v x * (1 - Classical.choose h x)) * (v y * (1 - Classical.choose h y)) *
          (‖x - y‖ : ℝ)⁻¹) =
      8 * π * (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * Classical.choose h x) := by
  let w₀ : ℝ³ → ℝ := Classical.choose h
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial w₀ := hspec.1
  have hw₀ : IsScatteringSolution w₀ v := hspec.2
  simpa [w₀] using
    (scattering_newton_double_eq (w := w₀) (v := v) (R := R) hR hvrad hv_supp hrad₀ hw₀)

/-- `∫∫ g₀(x)·g₀(y)/‖x−y‖ dx dy ≤ (8π)²·a v`. -/
theorem chosen_newton_double_le {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ x : ℝ³, ∫ y : ℝ³,
        (v x * (1 - Classical.choose h x)) * (v y * (1 - Classical.choose h y)) *
          (‖x - y‖ : ℝ)⁻¹) ≤ (8 * π) ^ 2 * a v := by
  have heq := chosen_newton_double_eq hR hvrad hv_supp h
  have hb := chosen_gomega_integral_bounds hR hv_nonneg hvrad hv_supp h
  have hpi : 0 ≤ 8 * π := by positivity
  calc
    (∫ x : ℝ³, ∫ y : ℝ³,
        (v x * (1 - Classical.choose h x)) * (v y * (1 - Classical.choose h y)) *
          (‖x - y‖ : ℝ)⁻¹)
        = 8 * π * (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * Classical.choose h x) := heq
    _ ≤ 8 * π * (8 * π * a v) := by
        exact mul_le_mul_of_nonneg_left hb.2 hpi
    _ = (8 * π) ^ 2 * a v := by ring

/-- `∫v(1−w₀)(1+w₀) ∈ [8π a v, 16π a v]`: the `w₂`-type (FS `g(1+ω)`)
quantity of the chosen solution lies between `∫g₀` and `2∫g₀`. -/
theorem chosen_g1pomega_integral_bounds {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    8 * π * a v ≤
        (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * (1 + Classical.choose h x)) ∧
      (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * (1 + Classical.choose h x)) ≤
        16 * π * a v := by
  let w₀ : ℝ³ → ℝ := Classical.choose h
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial w₀ := hspec.1
  have hw₀ : IsScatteringSolution w₀ v := hspec.2
  have hb := scat_gomega_integral_bounds (w := w₀) hR hv_nonneg hvrad hv_supp hrad₀ hw₀
  have hg : (∫ x : ℝ³, v x * (1 - w₀ x)) = 8 * π * a v := by
    simpa [w₀] using (chosen_scattering_integral (v := v) h)
  have hG : MeasureTheory.Integrable (fun x : ℝ³ => v x * (1 - w₀ x)) :=
    scatG_integrable hv_supp hw₀
  have hGw : MeasureTheory.Integrable (fun x : ℝ³ => (v x * (1 - w₀ x)) * w₀ x) :=
    scat_gomega_integrable hv_nonneg hvrad hv_supp hrad₀ hw₀
  have hfun : (fun x : ℝ³ => (v x * (1 - w₀ x)) * (1 + w₀ x)) =
      (fun x : ℝ³ => v x * (1 - w₀ x) + (v x * (1 - w₀ x)) * w₀ x) := by
    funext x
    ring
  have hsplit :
      (∫ x : ℝ³, (v x * (1 - w₀ x)) * (1 + w₀ x)) =
        (∫ x : ℝ³, v x * (1 - w₀ x)) +
          (∫ x : ℝ³, (v x * (1 - w₀ x)) * w₀ x) := by
    rw [hfun, MeasureTheory.integral_add hG hGw]
  have hgw_le : (∫ x : ℝ³, (v x * (1 - w₀ x)) * w₀ x) ≤ 8 * π * a v := by
    calc
      (∫ x : ℝ³, (v x * (1 - w₀ x)) * w₀ x) ≤ (∫ x : ℝ³, v x * (1 - w₀ x)) := hb.2
      _ = 8 * π * a v := hg
  constructor
  · calc
      8 * π * a v = (∫ x : ℝ³, v x * (1 - w₀ x)) := hg.symm
      _ ≤ (∫ x : ℝ³, v x * (1 - w₀ x)) +
            (∫ x : ℝ³, (v x * (1 - w₀ x)) * w₀ x) := by linarith [hb.1]
      _ = (∫ x : ℝ³, (v x * (1 - w₀ x)) * (1 + w₀ x)) := hsplit.symm
  · calc
      (∫ x : ℝ³, (v x * (1 - w₀ x)) * (1 + w₀ x))
          = (∫ x : ℝ³, v x * (1 - w₀ x)) +
            (∫ x : ℝ³, (v x * (1 - w₀ x)) * w₀ x) := hsplit
      _ ≤ 8 * π * a v + 8 * π * a v := by linarith
      _ = 16 * π * a v := by ring

end BoseGases

end Submission
