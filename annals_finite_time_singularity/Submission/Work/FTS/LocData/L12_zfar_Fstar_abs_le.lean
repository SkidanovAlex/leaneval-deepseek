/-
# `|L₁₂(zfar L F_*)(0)| ≤ 4α/L`

The localisation node of the route replaces the profile `F_*` by the *far part*
`zfar L F_* = (1 - χ(z/L))·F_*` (`Work.Stability.zfar`), which vanishes for `z ≤ L` and is
supported at the outer scale `L`.  The value of `L₁₂` of that far part at the origin is of
order `α/L`, which is what this module establishes.

The proof has three parts.

* **The operator identity** (`L12_zfar_Fstar_eq`): since `zfar L F_*` is the profile `F_*`
  multiplied by the *radial* factor `1 - χ(s/L)`, and `L₁₂dens` integrates over the angle only,
  that factor comes out of the angular integral: `L₁₂dens (zfar L F_*) s
  = (1 - χ(s/L))·L₁₂dens (F_*) s`.  With `L₁₂dens (F_*)(s) = α·F_*(s)/s`
  (`Work.Construction.L12dens_Fstar`) this gives the exact value

    `L₁₂(zfar L F_*)(0) = α · ∫_0^∞ (1 - χ(s/L)) · F_*(s)/s ds`.

* **The cut-off integral estimate** (`zfar_cut_integral_bounds`): the integrand of that last
  integral is nonnegative and vanishes identically on `(0, L]` (there `χ(s/L) = 1`), while on
  `s > L` it is at most `F_*(s)/s = 2/(1+s)²`.  Hence

    `0 ≤ ∫_0^∞ (1 - χ(s/L))·F_*(s)/s ds ≤ ∫_L^∞ 2/(1+s)² ds = 2/(1+L)`.

* **Arithmetic**: `α·2/(1+L) ≤ 4α/L` for `1 ≤ L`, and the integral is nonnegative, so it
  equals its own absolute value.

This is the bound `|L₁₂(g(0))(0)| = O(α/L)` used in the localised-data chapter of the route
(`FTS_AUDIT_LEAD.md` §4, node N9).
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## The `L₁₂`-density of the far part -/

/-- The angular density of `L₁₂` at the far part `zfar L F_*`: the radial factor
`1 - χ(s/L)` of the cut-off comes out of the angular integral, so that the density of the far
part is that of `F_*` multiplied by that factor. -/
theorem L12dens_zfar_Fstar (α : ℝ) (L s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (Work.Stability.zfar L (Work.Construction.Fstar α)) s
      = (1 - Work.Stability.chi (s / L)) *
          Work.Construction.L12dens (Work.Construction.Fstar α) s := by
  rw [Work.Construction.L12dens, Work.FM.L12dens, Work.FM.L12dens]
  have hpoint : Set.EqOn
      (fun θ => Work.Spaces.K θ * (Work.Stability.zfar L (Work.Construction.Fstar α)) s θ / s)
      (fun θ => (1 - Work.Stability.chi (s / L)) *
        (Work.Spaces.K θ * Work.Construction.Fstar α s θ / s))
      (Set.Icc 0 (Real.pi / 2)) := by
    intro θ _
    show Work.Spaces.K θ * Work.Stability.zfar L (Work.Construction.Fstar α) s θ / s
      = (1 - Work.Stability.chi (s / L)) *
          (Work.Spaces.K θ * Work.Construction.Fstar α s θ / s)
    rw [Work.Stability.zfar_apply]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint]
  rw [MeasureTheory.integral_const_mul]

/-- **`L₁₂` of the far part of the profile at `z = 0`.**  Using
`L₁₂dens (F_*) = α·F_*(s)/s` (`Work.Construction.L12dens_Fstar`) the whole operator collapses
to the elementary integral `α ∫_0^∞ (1 - χ(s/L))·F_*(s)/s ds`. -/
theorem L12_zfar_Fstar_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (L : ℝ) :
    Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0
      = α * ∫ s in Set.Ioi (0 : ℝ),
          (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s _ => L12dens_zfar_Fstar α L s)]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s _ => by rw [Work.Construction.L12dens_Fstar hα hα1 s])]
  rw [show (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (α * (Work.FM.Fstar s / s)))
      = (fun s : ℝ => α * ((1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)))
      from funext fun s => by ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## The cut-off integral estimate -/

/-- **The far-part integral is of order `1/L`.**  For `1 ≤ L` the integral
`∫_0^∞ (1 - χ(s/L))·F_*(s)/s ds` is nonnegative and at most `2/(1+L)`: the integrand vanishes
for `s ≤ L` (`χ(s/L) = 1` there) and is dominated by `F_*(s)/s = 2/(1+s)²` for `s ≥ L`, whose
tail integral is `2/(1+L)`. -/
theorem zfar_cut_integral_bounds {L : ℝ} (hL : 1 ≤ L) :
    0 ≤ ∫ s in Set.Ioi (0 : ℝ), (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s) ∧
      ∫ s in Set.Ioi (0 : ℝ), (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)
        ≤ 2 / (1 + L) := by
  have hL0 : (0 : ℝ) < L := by linarith
  -- the elementary form of the density on `s > 0`
  have hFstar : ∀ s ∈ Set.Ioi (0 : ℝ), Work.FM.Fstar s / s = 2 / (s + 1) ^ 2 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [Work.FM.Fstar]
    field_simp
    ring_nf
  constructor
  · -- nonnegativity of the integrand
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
    have h1 : 0 ≤ 1 - Work.Stability.chi (s / L) := by
      linarith [Work.Stability.chi_le_one (s / L)]
    have h2 : 0 ≤ Work.FM.Fstar s / s := by
      rw [hFstar s hs]
      positivity
    exact mul_nonneg h1 h2
  · -- the integrand is supported on `(L, ∞)` and dominated there by `2/(1+s)²`
    have hsupp : ∀ s ∈ Set.Ioi (0 : ℝ),
        (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)
          = (Set.Ioi L).indicator
              (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)) s := by
      intro s hs
      by_cases hmem : s ∈ Set.Ioi L
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem]
        have hsL : s ≤ L := le_of_not_gt hmem
        have h1 : s / L ≤ 1 := by
          rw [div_le_one hL0]
          exact hsL
        have h2 : -(1 : ℝ) ≤ s / L := by
          have : (0 : ℝ) ≤ s / L := div_nonneg (le_of_lt (show (0 : ℝ) < s from hs)) hL0.le
          linarith
        have hchi : Work.Stability.chi (s / L) = 1 :=
          Work.Stability.chi_eq_one (abs_le.mpr ⟨h2, h1⟩)
        rw [hchi]
        ring
    have step1 : ∫ s in Set.Ioi (0 : ℝ),
          (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)
        = ∫ s in Set.Ioi (0 : ℝ), (Set.Ioi L).indicator
            (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)) s := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      rw [hFstar s hs]
      exact hsupp s hs
    have step2 : ∫ s in Set.Ioi (0 : ℝ), (Set.Ioi L).indicator
          (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)) s
        = ∫ s in Set.Ioi L, (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2) := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
      rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioi L = Set.Ioi L from
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hL0.le)]
    have hint : MeasureTheory.IntegrableOn (fun s : ℝ => 2 / (s + 1) ^ 2) (Set.Ioi L) := by
      have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => 2 * (s + 1) ^ (-2 : ℝ)) (Set.Ioi L) :=
        (integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := L) (m := 1) (by norm_num)
          (by linarith)).integrable.const_mul 2
      refine h1.congr_fun (fun s hs => ?_) measurableSet_Ioi
      have hs1 : (0 : ℝ) < s + 1 := by
        have hsL : L < s := hs
        linarith
      have h : (s + 1) ^ (-2 : ℝ) = 1 / (s + 1) ^ 2 := by
        simp only [Real.rpow_neg hs1.le, Real.rpow_ofNat, one_div]
      show 2 * (s + 1) ^ (-2 : ℝ) = 2 / (s + 1) ^ 2
      rw [h]
      ring_nf
    have step3 : ∫ s in Set.Ioi L, (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)
        ≤ ∫ s in Set.Ioi L, 2 / (s + 1) ^ 2 := by
      refine MeasureTheory.setIntegral_mono_of_nonneg (fun s _ => ?_) (fun s _ => ?_) hint
      · have h1 : 0 ≤ 1 - Work.Stability.chi (s / L) := by
          linarith [Work.Stability.chi_le_one (s / L)]
        exact mul_nonneg h1 (by positivity)
      · have h1 : 1 - Work.Stability.chi (s / L) ≤ 1 := by
          linarith [Work.Stability.chi_nonneg (s / L)]
        exact mul_le_of_le_one_left (by positivity) h1
    have step4 : ∫ s in Set.Ioi L, 2 / (s + 1) ^ 2 = 2 / (1 + L) := by
      rw [← Work.FM.integral_Ioi_Fstar_div L hL0.le]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      have hs0 : (0 : ℝ) < s := by
        have hsL : L < s := hs
        linarith
      rw [hFstar s (show s ∈ Set.Ioi (0 : ℝ) from hs0)]
    calc ∫ s in Set.Ioi (0 : ℝ), (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)
        = ∫ s in Set.Ioi (0 : ℝ), (Set.Ioi L).indicator
            (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)) s := step1
      _ = ∫ s in Set.Ioi L, (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2) := step2
      _ ≤ ∫ s in Set.Ioi L, 2 / (s + 1) ^ 2 := step3
      _ = 2 / (1 + L) := step4

/-! ## The bound -/

theorem L12_zfar_Fstar_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L : ℝ} (hL : 1 ≤ L) :
    |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0| ≤ 4 * α / L := by
  obtain ⟨h0, hle⟩ := zfar_cut_integral_bounds hL
  rw [L12_zfar_Fstar_eq α hα hα1 L, abs_mul, abs_of_pos hα, abs_of_nonneg h0]
  have h1 : α * (∫ s in Set.Ioi (0 : ℝ),
        (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)) ≤ α * (2 / (1 + L)) :=
    mul_le_mul_of_nonneg_left hle hα.le
  have h2 : α * (2 / (1 + L)) ≤ 4 * α / L := by
    rw [show α * (2 / (1 + L)) = 2 * α / (1 + L) by ring]
    exact div_le_div₀ (by linarith : (0 : ℝ) ≤ 4 * α) (by linarith : 2 * α ≤ 4 * α)
      (by linarith : (0 : ℝ) < L) (by linarith : L ≤ 1 + L)
  linarith

end Work.FTS.LocData
