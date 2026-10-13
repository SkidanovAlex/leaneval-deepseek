/-
Copyright: work module for the Elgindi finite-time singularity project.

# The dilation `z ↦ 2z` of the squared radial weight `w`

`Work.FTS.EllipticEst.AngSecond.lintegral_w_sq_shift_two_le` bounds the weighted
`L¹`-norm of the dilated function `z ↦ w(z)² · g(2z)` by the weighted `L¹`-norm of `g`
itself, with the universal constant `8`:

  `∫_{z > 0} w(z)² g(2z) dz ≤ 8 ∫_{z > 0} w(z)² g(z) dz`  whenever `g ≥ 0` on `(0,∞)`.

The argument is the substitution `t = 2z` (so `z = t/2`, `dz = dt/2`), which converts the
left-hand side into `2⁻¹ ∫_{t > 0} w(t/2)² g(t) dt`, combined with the pointwise weight
comparison `w(t/2) ≤ 4 w(t)`, i.e. `((t+2)/t)² ≤ 4 ((t+1)/t)²`, for `w(t) = (1+t)²/t²`:
the latter is `t + 2 ≤ 2 (t + 1)` for `t ≥ 0`.  Hence `2⁻¹ w(t/2)² ≤ 2⁻¹ · 16 w(t)² = 8 w(t)²`.

Everything is stated for the lower Lebesgue integral (`∫⁻`), so no measurability of `g` is
needed: `MeasureTheory.lintegral` is a supremum over simple minorants and the change of
variables is available through `lintegral_map_equiv` for a measurable equivalence.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false

/-! ## Change of variables for the lower Lebesgue integral on `(0,∞)` -/

/-- **Change of variables** `z ↦ c * z` (`c > 0`) for the lower Lebesgue integral over
`(0,∞)`:  `∫_{z > 0} F (c z) dz = c⁻¹ ∫_{z > 0} F z dz`.

No (a.e.) measurability of `F` is required: `z ↦ c z` is a measurable equivalence of `ℝ` and
`MeasureTheory.lintegral_map_equiv` holds for arbitrary `ℝ≥0∞`-valued integrands. -/
theorem lintegral_Ioi_comp_mul_pos (c : ℝ) (hc : 0 < c) (F : ℝ → ENNReal) :
    (∫⁻ z in Set.Ioi 0, F (c * z)) = ENNReal.ofReal c⁻¹ * ∫⁻ z in Set.Ioi 0, F z := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hmem : ∀ z : ℝ, (z ∈ Set.Ioi 0) ↔ (c * z ∈ Set.Ioi 0) := by
    intro z
    simp only [Set.mem_Ioi]
    exact (mul_pos_iff_of_pos_left hc).symm
  -- the same statement without the restriction to `(0,∞)`
  have hmain : ∀ H : ℝ → ENNReal, (∫⁻ z, H (c * z)) = ENNReal.ofReal c⁻¹ * ∫⁻ z, H z := by
    intro H
    let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc0).toMeasurableEquiv
    have he : ⇑e = (fun z : ℝ => c * z) := rfl
    have hmap : Measure.map (⇑e) volume = ENNReal.ofReal c⁻¹ • volume := by
      rw [he, Real.map_volume_mul_left hc0, abs_of_pos (inv_pos.mpr hc)]
    calc ∫⁻ z, H (c * z)
        = ∫⁻ z, H (e z) := by rw [he]
      _ = ∫⁻ z, H z ∂(Measure.map (⇑e) volume) := (lintegral_map_equiv H e).symm
      _ = ∫⁻ z, H z ∂(ENNReal.ofReal c⁻¹ • volume) := by rw [hmap]
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ z, H z := by
            rw [lintegral_smul_measure, smul_eq_mul]
  -- restrict to `(0,∞)`: the indicators of `(0,∞)` agree for `F` and `F ∘ (c * ·)`
  set G : ℝ → ENNReal := Set.indicator (Set.Ioi 0) F with hG
  have hL : (∫⁻ z in Set.Ioi 0, F (c * z)) = ∫⁻ z, G (c * z) := by
    rw [← lintegral_indicator measurableSet_Ioi (fun z => F (c * z))]
    refine lintegral_congr (fun z => ?_)
    rw [hG]
    by_cases hz : z ∈ Set.Ioi 0
    · rw [Set.indicator_of_mem ((hmem z).mp hz), Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem (fun h => hz ((hmem z).mpr h)), Set.indicator_of_notMem hz]
  calc (∫⁻ z in Set.Ioi 0, F (c * z))
      = ∫⁻ z, G (c * z) := hL
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z, G z := hmain G
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in Set.Ioi 0, F z := by
          rw [hG, lintegral_indicator measurableSet_Ioi F]

/-! ## The pointwise weight comparison -/

/-- **The weight comparison.**  For `w t = (1+t)²/t²` and `t > 0`,
`2⁻¹ · w(t/2)² ≤ 8 · w(t)²`; equivalently `w(t/2) ≤ 4 w(t)`. -/
theorem half_sq_w_le (t : ℝ) (ht : 0 < t) :
    (2:ℝ)⁻¹ * (Work.Spaces.w (t/2))^2 ≤ 8 * (Work.Spaces.w t)^2 := by
  have htne : t ≠ 0 := ht.ne'
  have ht2 : (t/2) ≠ 0 := by positivity
  have hw2 : Work.Spaces.w (t/2) = ((t+2)/t)^2 := by
    rw [Work.Spaces.w]; field_simp; ring
  have hw1 : Work.Spaces.w t = ((t+1)/t)^2 := by
    rw [Work.Spaces.w]; field_simp; ring
  rw [hw2, hw1]
  have hle : (t+2)/t ≤ 2 * ((t+1)/t) := by
    rw [show 2 * ((t+1)/t) = (2*(t+1))/t by ring]
    exact div_le_div_of_nonneg_right (by linarith) ht.le
  have h0 : 0 ≤ (t+2)/t := by positivity
  have h4 : ((t+2)/t)^4 ≤ (2*((t+1)/t))^4 := pow_le_pow_left₀ h0 hle 4
  have h4' : (2*((t+1)/t))^4 = 16 * ((t+1)/t)^4 := by ring
  rw [show (((t+2)/t)^2)^2 = ((t+2)/t)^4 by ring,
      show (((t+1)/t)^2)^2 = ((t+1)/t)^4 by ring]
  linarith [h4, h4']

/-! ## The main estimate -/

/-- **The dilation `z ↦ 2z` of the squared radial weight**, with constant `8`. -/
theorem lintegral_w_sq_shift_two_le (g : ℝ → ℝ) (hg : ∀ y ∈ Set.Ioi 0, 0 ≤ g y) :
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * g (2 * z)))
      ≤ ENNReal.ofReal 8 * ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * g z) := by
  let B : ℝ → ENNReal := fun t => ENNReal.ofReal ((Work.Spaces.w (t/2))^2 * g t)
  let A : ℝ → ENNReal := fun t => ENNReal.ofReal ((Work.Spaces.w t)^2 * g t)
  -- rewrite the left-hand integrand as `B (2 * z)`
  have hstepA : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z)^2 * g (2*z)))
      = ∫⁻ z in Set.Ioi 0, B (2 * z) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    dsimp only [B]
    rw [show (2 * z)/2 = z by ring]
  -- substitution `t = 2 z`
  have hstepB : (∫⁻ z in Set.Ioi 0, B (2 * z))
      = ENNReal.ofReal (2:ℝ)⁻¹ * ∫⁻ z in Set.Ioi 0, B z :=
    lintegral_Ioi_comp_mul_pos 2 (by norm_num) B
  -- the pointwise comparison of the two weighted integrands
  have hstepC : ENNReal.ofReal (2:ℝ)⁻¹ * ∫⁻ z in Set.Ioi 0, B z
      ≤ ENNReal.ofReal 8 * ∫⁻ z in Set.Ioi 0, A z := by
    have h1 : ENNReal.ofReal (2:ℝ)⁻¹ * ∫⁻ z in Set.Ioi 0, B z
        = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (2:ℝ)⁻¹ * B z := by
      rw [lintegral_const_mul' (ENNReal.ofReal (2:ℝ)⁻¹) B ENNReal.ofReal_ne_top]
    have h2 : ENNReal.ofReal 8 * ∫⁻ z in Set.Ioi 0, A z
        = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal 8 * A z := by
      rw [lintegral_const_mul' (ENNReal.ofReal 8) A ENNReal.ofReal_ne_top]
    rw [h1, h2]
    refine setLIntegral_mono' measurableSet_Ioi (fun z hz => ?_)
    have hgz : 0 ≤ g z := hg z hz
    have hkey : (2:ℝ)⁻¹ * (Work.Spaces.w (z/2))^2 ≤ 8 * (Work.Spaces.w z)^2 :=
      half_sq_w_le z hz
    dsimp only [B, A]
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ (8:ℝ))]
    apply ENNReal.ofReal_le_ofReal
    calc (2:ℝ)⁻¹ * ((Work.Spaces.w (z/2))^2 * g z)
        = ((2:ℝ)⁻¹ * (Work.Spaces.w (z/2))^2) * g z := by ring
      _ ≤ (8 * (Work.Spaces.w z)^2) * g z := mul_le_mul_of_nonneg_right hkey hgz
      _ = 8 * ((Work.Spaces.w z)^2 * g z) := by ring
  calc (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z)^2 * g (2*z)))
      = ∫⁻ z in Set.Ioi 0, B (2*z) := hstepA
    _ = ENNReal.ofReal (2:ℝ)⁻¹ * ∫⁻ z in Set.Ioi 0, B z := hstepB
    _ ≤ ENNReal.ofReal 8 * ∫⁻ z in Set.Ioi 0, A z := hstepC

end Work.FTS.EllipticEst.AngSecond
