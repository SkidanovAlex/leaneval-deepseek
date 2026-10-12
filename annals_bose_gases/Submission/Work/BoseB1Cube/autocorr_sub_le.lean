import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseB1Cube.autocorrShiftIdentity
import Submission.Work.BoseB1Cube.fderivL2_le_mul
import Submission.Work.BoseB1Cube.integral_integral_line_swap
import Submission.Work.BoseB1Cube.shiftDiff_sq_pointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The autocorrelation defect of a smooth, compactly supported function is controlled by
`‖z‖²·sup‖∇χ‖·∫‖∇χ‖`.**

Writing `A(z) := ∫_x χ(x)χ(x − z) dx` for the autocorrelation, the polarisation identity
`2(∫χ² − A(z)) = ∫_x (χ(x + z) − χ(x))² dx` turns the claim into the `L²`-modulus-of-continuity
bound of `χ` at the shift `z`:

* the fundamental theorem of calculus along the segment `s ↦ x + s•z` gives
  `χ(x + z/2) − χ(x − z/2) = ∫_{s∈[-1/2,1/2]} fderiv ℝ χ (x + s•z) z ds`, whence by
  Cauchy–Schwarz on the interval of length `1`
  `(χ(x + z/2) − χ(x − z/2))² ≤ ‖z‖² ∫_{s} ‖fderiv ℝ χ (x + s•z)‖² ds`
  (`Work.BoseB1Cube.shiftDiff_sq_pointwise`);
* integrating in `x` and using the measure-preserving "line average"
  (`Work.BoseB1Cube.integral_integral_line_swap`) gives
  `∫_x (χ(x + z/2) − χ(x − z/2))² dx ≤ ‖z‖² ∫_x ‖fderiv ℝ χ x‖² dx`;
* finally `∫_x ‖fderiv ℝ χ x‖² dx ≤ H·L` because `‖fderiv ℝ χ x‖ ≤ H` pointwise
  (`Work.BoseB1Cube.fderivL2_le_mul`). -/
theorem autocorr_sub_le {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (h2 : ContDiff ℝ 2 χ)
    (hcs : HasCompactSupport χ) (hnn : ∀ x, 0 ≤ χ x) {H L : ℝ} (hH : ∀ x, ‖fderiv ℝ χ x‖ ≤ H)
    (hL : ∫ x, ‖fderiv ℝ χ x‖ ≤ L) :
    ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ x, (χ x) ^ 2) - ∫ x, χ x * χ (x - z) ≤ (‖z‖ ^ 2 / 2) * H * L := by
  intro z
  -- ## Integrability of the various pieces
  have hχcont : Continuous χ := h2.continuous
  have hmem : MemLp χ 2 (volume : Measure E3) := hχcont.memLp_of_hasCompactSupport hcs
  have hχ2 : Integrable (fun x : E3 => (χ x) ^ 2) := hmem.integrable_sq
  have hχ2p : Integrable (fun x : E3 => (χ (x + z)) ^ 2) := hχ2.comp_add_right z
  -- ## The polarisation identity at the shift `z`
  have hprod : Integrable (fun x : E3 => χ (x + z) * χ x) := by
    have hcont : Continuous (fun x : E3 => χ (x + z) * χ x) :=
      (hχcont.comp (by fun_prop)).mul hχcont
    have hmaj : Integrable (fun x : E3 => (1 / 2) * ((χ (x + z)) ^ 2 + (χ x) ^ 2)) :=
      (hχ2p.add hχ2).const_mul (1 / 2)
    refine hmaj.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|χ (x + z)| - |χ x|), sq_abs (χ (x + z)), sq_abs (χ x)]
  have hident := autocorrShiftIdentity (f := χ) (z := z) hχ2 hχ2p hprod
  -- ## Integrability of `‖fderiv ℝ χ‖` and `‖fderiv ℝ χ‖²`
  have hgcont : Continuous (fun x : E3 => ‖fderiv ℝ χ x‖) :=
    (h2.continuous_fderiv (by norm_num)).norm
  have hgcs : HasCompactSupport (fun x : E3 => ‖fderiv ℝ χ x‖) := (hcs.fderiv ℝ).norm
  have hgint : Integrable (fun x : E3 => ‖fderiv ℝ χ x‖) :=
    hgcont.integrable_of_hasCompactSupport hgcs
  have hHnn : 0 ≤ H := le_trans (norm_nonneg _) (hH 0)
  have hg2int : Integrable (fun x : E3 => ‖fderiv ℝ χ x‖ ^ 2) := by
    refine (hgint.const_mul H).mono' (hgcont.pow 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_right (hH x) (norm_nonneg _)
  -- ## The line-average identity (`∫_x ∫_{|s| ≤ 1/2} G (x + s•z) ds dx = ∫ G`)
  obtain ⟨hline_int, hline_val⟩ :=
    integral_integral_line_swap (g := fun x : E3 => ‖fderiv ℝ χ x‖ ^ 2) hg2int z
  -- ## Integrability of the squared centred shift-difference of `χ`
  have hleft : Integrable (fun x : E3 =>
      (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)) ^ 2) := by
    have hcont : Continuous (fun x : E3 =>
        (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)) ^ 2) :=
      (((hχcont.comp (by fun_prop)).sub (hχcont.comp (by fun_prop)))).pow 2
    have hs1 : Integrable (fun x : E3 => (χ (x + (1 / 2 : ℝ) • z)) ^ 2) :=
      hχ2.comp_add_right ((1 / 2 : ℝ) • z)
    have hs2 : Integrable (fun x : E3 => (χ (x - (1 / 2 : ℝ) • z)) ^ 2) :=
      hχ2.comp_sub_right ((1 / 2 : ℝ) • z)
    have hmaj : Integrable (fun x : E3 =>
        2 * ((χ (x + (1 / 2 : ℝ) • z)) ^ 2 + (χ (x - (1 / 2 : ℝ) • z)) ^ 2)) :=
      (hs1.add hs2).const_mul 2
    refine hmaj.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)))]
    nlinarith [sq_nonneg (χ (x + (1 / 2 : ℝ) • z) + χ (x - (1 / 2 : ℝ) • z))]
  -- ## Integrating the pointwise shift bound
  have hmono : (∫ x, (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)) ^ 2) ≤
      ∫ x, ‖z‖ ^ 2 * (∫ s in (-(1 / 2) : ℝ)..(1 / 2),
        (‖fderiv ℝ χ (x + s • z)‖) ^ 2) :=
    integral_mono hleft (hline_int.const_mul (‖z‖ ^ 2)) (fun x => shiftDiff_sq_pointwise h2 x z)
  have hshift : (∫ x, (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)) ^ 2) ≤
      ‖z‖ ^ 2 * ∫ x, ‖fderiv ℝ χ x‖ ^ 2 := by
    calc (∫ x, (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)) ^ 2)
        ≤ ∫ x, ‖z‖ ^ 2 * (∫ s in (-(1 / 2) : ℝ)..(1 / 2),
            (‖fderiv ℝ χ (x + s • z)‖) ^ 2) := hmono
      _ = ‖z‖ ^ 2 * ∫ x, (∫ s in (-(1 / 2) : ℝ)..(1 / 2),
            (‖fderiv ℝ χ (x + s • z)‖) ^ 2) := integral_const_mul _ _
      _ = ‖z‖ ^ 2 * ∫ x, ‖fderiv ℝ χ x‖ ^ 2 := by rw [hline_val]
  -- ## Passing from the centred shift-difference to the shift-difference
  have hsym : (∫ x, (χ (x + z) - χ x) ^ 2) =
      (∫ x, (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)) ^ 2) := by
    set F : E3 → ℝ := fun y => (χ (y + (1 / 2 : ℝ) • z) - χ (y - (1 / 2 : ℝ) • z)) ^ 2
    have h := integral_add_right_eq_self (μ := (volume : Measure E3)) F ((1 / 2 : ℝ) • z)
    have hpt : ∀ y : E3, F (y + (1 / 2 : ℝ) • z) = (χ (y + z) - χ y) ^ 2 := by
      intro y
      have h1 : y + (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • z = y + z := by
        rw [add_assoc, ← add_smul]; norm_num
      have h2 : y + (1 / 2 : ℝ) • z - (1 / 2 : ℝ) • z = y := by abel
      simp only [F, h1, h2]
    calc (∫ x, (χ (x + z) - χ x) ^ 2)
        = ∫ y, F (y + (1 / 2 : ℝ) • z) :=
          (integral_congr_ae (Filter.Eventually.of_forall hpt)).symm
      _ = ∫ y, F y := h
      _ = ∫ x, (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)) ^ 2 := rfl
  have hJ : (∫ x, (χ (x + z) - χ x) ^ 2) ≤ ‖z‖ ^ 2 * (H * L) := by
    rw [hsym]
    exact le_trans hshift (mul_le_mul_of_nonneg_left (fderivL2_le_mul h2 hcs hH hL) (sq_nonneg ‖z‖))
  -- ## Final arithmetic
  have hA : (∫ x, (χ x) ^ 2) - ∫ x, χ x * χ (x - z) =
      (1 / 2) * ∫ x, (χ (x + z) - χ x) ^ 2 := by
    rw [hident]; ring
  calc (∫ x, (χ x) ^ 2) - ∫ x, χ x * χ (x - z)
      = (1 / 2) * ∫ x, (χ (x + z) - χ x) ^ 2 := hA
    _ ≤ (1 / 2) * (‖z‖ ^ 2 * (H * L)) := mul_le_mul_of_nonneg_left hJ (by norm_num)
    _ = (‖z‖ ^ 2 / 2) * H * L := by ring

end Work.BoseB1Cube
