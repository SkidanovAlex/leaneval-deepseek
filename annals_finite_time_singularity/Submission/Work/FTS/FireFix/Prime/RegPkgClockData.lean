/-
# `Work.FTS.Physical.Clock.regPkg_clock_data` — the clock data for the firing from `RegPkg'`

This module supplies the clock data that the reconstruction needs when it is fired from node N7's
`Work.FTS.RegPkgGal.RegPkg'`:

* `one_div_A_lipschitz`: the reciprocal amplitude `τ ↦ 1/A(τ)` is Lipschitz on the fake-time
  strip `[0,S]` (bounded derivative `|A'| ≤ a₂` and lower bound `A ≥ a₀ > 0` in `RegPkg'`);
* `lipschitz_of_hasDerivAt_bounded`: a differentiable function on `[0,T]` with bounded derivative
  is Lipschitz (the mean value inequality);
* `regPkg_clock_data`: hence `d = (1/A) ∘ τ` is bounded and `α`-Hölder on `[0,T]` whenever `τ` is
  Lipschitz and maps `[0,T]` into `[0,S]` — exactly the derivative data required by
  `Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Physical.Clock
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.RegPkgGal.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

open Work.FTS.Physical (PhysClock)

/-- **The reciprocal amplitude is Lipschitz on the strip.**  Under the clock fields of `RegPkg'`
(`A` differentiable on `[0,S]` with `|A'| ≤ a₂`, and `A ≥ a₀ > 0`), the map `τ ↦ 1/A(τ)` is
Lipschitz on `[0,S]` with constant `a₂/a₀²`. -/
theorem one_div_A_lipschitz {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∃ L : ℝ, ∀ tau ∈ Set.Icc (0 : ℝ) S, ∀ tau' ∈ Set.Icc (0 : ℝ) S,
      |(A tau)⁻¹ - (A tau')⁻¹| ≤ L * |tau - tau'| := by
  obtain ⟨a₀, a₁, ha₀pos, ha⟩ := h.hAb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  have ha₀pos' : 0 < a₀ := ha₀pos
  refine ⟨max (max a₂ 0 / a₀ ^ 2) 0, fun tau htau tau' htau' => ?_⟩
  have hAτ : a₀ ≤ A tau := (ha tau htau).1
  have hAτ' : a₀ ≤ A tau' := (ha tau' htau').1
  have hposτ : 0 < A tau := lt_of_lt_of_le ha₀pos' hAτ
  have hposτ' : 0 < A tau' := lt_of_lt_of_le ha₀pos' hAτ'
  -- Lipschitz bound for `A` on the strip
  have hlip : |A tau - A tau'| ≤ max a₂ 0 * |tau - tau'| := by
    have h2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A) (f' := deriv A) (s := Set.Icc (0 : ℝ) S)
      (fun x hx => (h.hAdiff x hx).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact le_trans (ha₂ x hx) (le_max_left a₂ 0))
      (convex_Icc 0 S) htau htau'
    simpa [Real.norm_eq_abs, abs_sub_comm] using h2
  have hkey : (A tau)⁻¹ - (A tau')⁻¹ = (A tau' - A tau) / (A tau * A tau') := by
    field_simp
  have hden : a₀ * a₀ ≤ A tau * A tau' :=
    mul_le_mul hAτ hAτ' ha₀pos'.le (le_trans ha₀pos'.le hAτ)
  have hdenpos : (0 : ℝ) < A tau * A tau' := mul_pos hposτ hposτ'
  have hnum : |A tau' - A tau| ≤ max a₂ 0 * |tau' - tau| := by
    simpa [abs_sub_comm] using hlip
  rw [hkey, abs_div, abs_of_pos hdenpos]
  have hstep1 : |A tau' - A tau| / (A tau * A tau')
      ≤ (max a₂ 0 * |tau' - tau|) / (A tau * A tau') :=
    div_le_div_of_nonneg_right hnum hdenpos.le
  have hstep2 : (max a₂ 0 * |tau' - tau|) / (A tau * A tau')
      ≤ (max a₂ 0 * |tau' - tau|) / (a₀ * a₀) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_max_right a₂ 0) (abs_nonneg _))
    simpa [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < a₀ * a₀) hden
  have hstep3 : (max a₂ 0 * |tau' - tau|) / (a₀ * a₀)
      = max a₂ 0 / a₀ ^ 2 * |tau' - tau| := by
    field_simp
  have hstep4 : max a₂ 0 / a₀ ^ 2 * |tau' - tau| ≤ max (max a₂ 0 / a₀ ^ 2) 0 * |tau' - tau| :=
    mul_le_mul_of_nonneg_right (le_max_left (max a₂ 0 / a₀ ^ 2) 0) (abs_nonneg _)
  have habs : |tau' - tau| = |tau - tau'| := abs_sub_comm tau' tau
  calc |A tau' - A tau| / (A tau * A tau')
      ≤ (max a₂ 0 * |tau' - tau|) / (A tau * A tau') := hstep1
    _ ≤ (max a₂ 0 * |tau' - tau|) / (a₀ * a₀) := hstep2
    _ = max a₂ 0 / a₀ ^ 2 * |tau' - tau| := hstep3
    _ ≤ max (max a₂ 0 / a₀ ^ 2) 0 * |tau' - tau| := hstep4
    _ = max (max a₂ 0 / a₀ ^ 2) 0 * |tau - tau'| := by rw [← habs]

/-- **A differentiable function with bounded derivative on `[0,T]` is Lipschitz** (the mean value
inequality, stated on the closed interval). -/
theorem lipschitz_of_hasDerivAt_bounded {T L : ℝ} {tau d : ℝ → ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt tau (d t) t)
    (hbdd : ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ L) :
    ∃ L' : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ L' * |t - t'| := by
  refine ⟨L, fun t ht t' ht' => ?_⟩
  have h2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := tau) (f' := d) (s := Set.Icc (0 : ℝ) T)
    (fun x hx => (hderiv x hx).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hbdd x hx)
    (convex_Icc 0 T) ht ht'
  simpa [Real.norm_eq_abs, abs_sub_comm] using h2

/-- **The clock data of the reconstruction, from `RegPkg'`.**  If `τ` maps `[0,T]` into the
fake-time strip `[0,S]` and is Lipschitz, and `d t = (A (τ t))⁻¹`, then `d` is bounded on `[0,T]`
and `α`-Hölder there (with `α ` the `RegPkg'` exponent, `0 < α ≤ 1/3`). -/
theorem regPkg_clock_data {α S T : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hreg : Work.FTS.RegPkgGal.RegPkg' α S A B g) {tau d : ℝ → ℝ}
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, tau t ∈ Set.Icc (0 : ℝ) S)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) T, d t = (A (tau t))⁻¹)
    (hlip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ L * |t - t'|) :
    (∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ L) ∧
      (∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
        |d t - d t'| ≤ L * |t - t'| ^ α) := by
  obtain ⟨a₀, a₁, ha₀pos, ha⟩ := hreg.hAb
  obtain ⟨LA₀, hLA₀⟩ := one_div_A_lipschitz hreg
  obtain ⟨Lτ₀, hLτ₀⟩ := hlip
  have hαpos : 0 < α := hreg.hα
  have hαle : α ≤ 1 := by linarith [hreg.hα13]
  -- nonnegative versions of the constants
  have hLA : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |(A τ)⁻¹ - (A τ')⁻¹| ≤ max LA₀ 0 * |τ - τ'| := fun τ hτ τ' hτ' =>
    le_trans (hLA₀ τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left LA₀ 0) (abs_nonneg _))
  have hLτ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ max Lτ₀ 0 * |t - t'| := fun t ht t' ht' =>
    le_trans (hLτ₀ t ht t' ht') (mul_le_mul_of_nonneg_right (le_max_left Lτ₀ 0) (abs_nonneg _))
  have hLAnn : 0 ≤ max LA₀ 0 := le_max_right LA₀ 0
  have hLτnn : 0 ≤ max Lτ₀ 0 := le_max_right Lτ₀ 0
  -- boundedness of `d`
  have hbdd : ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ max (a₀⁻¹) 0 := by
    intro t ht
    have hApos : 0 < A (tau t) := lt_of_lt_of_le ha₀pos (ha (tau t) (hmem t ht)).1
    rw [hd t ht, abs_of_pos (inv_pos.mpr hApos)]
    exact le_trans (by simpa [one_div] using
      one_div_le_one_div_of_le ha₀pos (ha (tau t) (hmem t ht)).1) (le_max_left (a₀⁻¹) 0)
  refine ⟨⟨max (a₀⁻¹) 0, hbdd⟩, ?_⟩
  -- Hölder bound for `d`
  refine ⟨max (max LA₀ 0 * max Lτ₀ 0) (2 * max (a₀⁻¹) 0), fun t ht t' ht' => ?_⟩
  rcases le_total |t - t'| 1 with hsmall | hbig
  · have h1 : |d t - d t'| ≤ max LA₀ 0 * |tau t - tau t'| := by
      rw [hd t ht, hd t' ht']
      exact hLA (tau t) (hmem t ht) (tau t') (hmem t' ht')
    have h3 : |t - t'| ≤ |t - t'| ^ α := Real.self_le_rpow_of_le_one (abs_nonneg _) hsmall hαle
    calc |d t - d t'| ≤ max LA₀ 0 * |tau t - tau t'| := h1
      _ ≤ max LA₀ 0 * (max Lτ₀ 0 * |t - t'|) := mul_le_mul_of_nonneg_left (hLτ t ht t' ht') hLAnn
      _ = (max LA₀ 0 * max Lτ₀ 0) * |t - t'| := by ring
      _ ≤ (max LA₀ 0 * max Lτ₀ 0) * |t - t'| ^ α :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hLAnn hLτnn)
      _ ≤ max (max LA₀ 0 * max Lτ₀ 0) (2 * max (a₀⁻¹) 0) * |t - t'| ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
  · have hone : (1 : ℝ) ≤ |t - t'| ^ α := Real.one_le_rpow hbig hαpos.le
    have h1 : |d t - d t'| ≤ 2 * max (a₀⁻¹) 0 := by
      have h2 := hbdd t ht
      have h3 := hbdd t' ht'
      calc |d t - d t'| ≤ |d t| + |d t'| :=
            abs_sub_le_iff.mpr ⟨by linarith [le_abs_self (d t), neg_le_abs (d t')],
              by linarith [le_abs_self (d t'), neg_le_abs (d t)]⟩
        _ ≤ 2 * max (a₀⁻¹) 0 := by linarith
    calc |d t - d t'| ≤ 2 * max (a₀⁻¹) 0 := h1
      _ = (2 * max (a₀⁻¹) 0) * 1 := by ring
      _ ≤ (2 * max (a₀⁻¹) 0) * |t - t'| ^ α :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ ≤ max (max LA₀ 0 * max Lτ₀ 0) (2 * max (a₀⁻¹) 0) * |t - t'| ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _)

end Work.FTS.FireFix.Prime
