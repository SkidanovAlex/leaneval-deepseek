import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.Spaces.ProductTools
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L₁₂(F)(z) → 0` as `z → ∞` for `F ∈ L²(dz dθ)`

The singular part of Elgindi's §'The singular term' is built from the radial integral

  `L₁₂(F)(z) = ∫_z^∞ ∫_0^{π/2} F(r,θ) K(θ)/r dθ dr`,  `K(θ) = 3 sin θ cos²θ`,

which after the angular integration only involves the angular moment `F_*`:

  `L₁₂(F)(z) = 3 ∫_z^∞ F_*(r)/r dr = 3 · L12rad F z`  (`Work.Elliptic.L12_eq_radial`).

The mathematical content of this file is that **the tail integral of an `L²` function tends
to `0`**: the angular moment of `F` satisfies, by Cauchy--Schwarz (`Fstar_sq_le`),

  `|F_*(r)| ≤ √(π/2 · ∫_θ F(r,θ)² dθ)`,

so `|F_*(r)| / r` is dominated by the `L¹(Ioi 1)` function

  `L12Maj F r = (π/2 · ∫_θ F(r,θ)² dθ + r^{-2}) / 2`,

the second term coming from the elementary inequality `√(a)/r ≤ (a + r^{-2})/2` for
`a ≥ 0`, `r ≥ 1`.  Since the tail integrals of an `L¹` function vanish at `∞`
(`MeasureTheory.tendsto_integral_Ioi_zero`), `L₁₂(F)(z) → 0`.

Note that the hypothesis `Work.Spaces.L2Mem F` is used only through the Cauchy--Schwarz
majorant; the *conclusion* is a statement about the tail integrals of an `L¹` function.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The angular slice of `F` and the majorant of `F_*` -/

/-- The angular `L²` density `∫_θ F(r,θ)² dθ` of `F`, i.e. the `r`-slice of the `L²` norm. -/
def L12slice (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, (F r θ) ^ 2

/-- The Cauchy--Schwarz majorant `√(π/2 · ∫_θ F(r,θ)²)` of the angular moment `|F_*|`. -/
def L12maj (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ := Real.sqrt (Real.pi / 2 * L12slice F r)

/-- The `L¹(Ioi 1)` majorant of `|F_*(r)|/r`: AM–GM turns `√(π/2 · ∫_θ F²)/r` into
`(π/2 · ∫_θ F² + r^{-2})/2`. -/
def L12Maj (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  (Real.pi / 2 * L12slice F r + r ^ (-2 : ℝ)) / 2

lemma L12slice_nonneg (F : ℝ → ℝ → ℝ) (r : ℝ) : 0 ≤ L12slice F r :=
  integral_nonneg fun _ => sq_nonneg _

/-- `r^{-2} = (r⁻¹)²` for `r > 0`. -/
lemma rpow_neg_two_eq (r : ℝ) (hr : 0 < r) : r ^ (-2 : ℝ) = (r⁻¹) ^ 2 := by
  rw [Real.rpow_neg (le_of_lt hr), Real.rpow_two, inv_pow]

lemma L12Maj_nonneg (F : ℝ → ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ L12Maj F r := by
  rw [L12Maj]
  exact div_nonneg (add_nonneg (mul_nonneg (by positivity) (L12slice_nonneg F r))
    (Real.rpow_nonneg hr (-2))) (by norm_num)

lemma L12maj_nonneg (F : ℝ → ℝ → ℝ) (r : ℝ) : 0 ≤ L12maj F r := Real.sqrt_nonneg _

lemma L12maj_sq (F : ℝ → ℝ → ℝ) (r : ℝ) : (L12maj F r) ^ 2 = Real.pi / 2 * L12slice F r := by
  rw [L12maj, Real.sq_sqrt (mul_nonneg (by positivity) (L12slice_nonneg F r))]

/-! ## The `L¹` properties of the majorant -/

/-- The angular slice of an `L2Mem` function is integrable on `(0,∞)`. -/
lemma integrableOn_L12slice_Ioi (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    IntegrableOn (L12slice F) (Set.Ioi 0) := by
  have h2 : IntegrableOn (L12slice F) (Set.Ici (0 : ℝ)) := hL2.2
  exact h2.mono_set Set.Ioi_subset_Ici_self

/-- The majorant is integrable on `(1,∞)`: the second term is `x^{-2}` and the first is the
angular slice of `F`, which is integrable by hypothesis. -/
lemma integrableOn_L12Maj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    IntegrableOn (L12Maj F) (Set.Ioi 1) := by
  have hS : IntegrableOn (fun r : ℝ => Real.pi / 2 * L12slice F r) (Set.Ioi 1) :=
    ((integrableOn_L12slice_Ioi F hL2).mono_set (Set.Ioi_subset_Ioi (by norm_num))).const_mul _
  have hp : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hsum : IntegrableOn (fun r : ℝ => Real.pi / 2 * L12slice F r + r ^ (-2 : ℝ))
      (Set.Ioi 1) := hS.add hp
  exact hsum.div_const 2

/-! ## Cauchy--Schwarz for the angular moment, and the pointwise bound -/

/-- Cauchy--Schwarz (`Work.Elliptic.Fstar_sq_le`): `|F_*|` is dominated by `L12maj`. -/
lemma abs_Fstar_le_L12maj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) {r : ℝ} (hr : 0 < r) :
    |Work.Elliptic.Fstar F r| ≤ L12maj F r := by
  have h := Work.Elliptic.Fstar_sq_le F r (hL2.1 r (le_of_lt hr))
  calc |Work.Elliptic.Fstar F r| = Real.sqrt ((Work.Elliptic.Fstar F r) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Real.pi / 2 * L12slice F r) :=
        Real.sqrt_le_sqrt (by simpa [L12slice] using h)
    _ = L12maj F r := by rw [L12maj]

/-- `|F_*(r)|/r ≤ L12Maj F r` on `[1,∞)` (AM–GM applied to `√(π/2 ∫_θ F²)/r`). -/
lemma abs_Fstar_div_le_Maj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) {r : ℝ} (hr : 1 ≤ r) :
    |Work.Elliptic.Fstar F r| / r ≤ L12Maj F r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  refine le_trans (div_le_div_of_nonneg_right (abs_Fstar_le_L12maj F hL2 hr0) (le_of_lt hr0)) ?_
  rw [L12Maj, rpow_neg_two_eq r hr0, div_eq_mul_inv, ← L12maj_sq F r]
  nlinarith [sq_nonneg (L12maj F r - r⁻¹)]

/-! ## The tail bound and the limit -/

/-- The radial integral defining `L₁₂` is bounded by the tail integral of the `L¹` majorant:
for `z ≥ 1`,

  `|∫_z^∞ F_*(r)/r dr| ≤ ∫_z^∞ L12Maj F r dr`.

(When `F_*/r` is not integrable the left hand side is `0` by the convention for the
totalised Bochner integral, and the claim is trivial since the majorant is nonnegative.) -/
lemma norm_L12rad_le (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) {z : ℝ} (hz : 1 ≤ z) :
    ‖Work.Elliptic.L12rad F z‖ ≤ ∫ r in Set.Ioi z, L12Maj F r := by
  rw [Work.Elliptic.L12rad]
  by_cases hInt : IntegrableOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi z)
  · refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine integral_mono_of_nonneg (MeasureTheory.ae_of_all _ fun r => norm_nonneg _)
      ((integrableOn_L12Maj F hL2).mono_set (Set.Ioi_subset_Ioi hz)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hzr : z < r := hr
    have hr1 : (1 : ℝ) ≤ r := by linarith
    have hr0 : 0 < r := by linarith
    show ‖Work.Elliptic.Fstar F r / r‖ ≤ L12Maj F r
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg (le_of_lt hr0)]
    exact abs_Fstar_div_le_Maj F hL2 hr1
  · rw [integral_undef hInt, norm_zero]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hzr : z < r := hr
    exact L12Maj_nonneg F (by linarith)

/-- The tail integrals of the majorant vanish at `∞`. -/
lemma tendsto_tail_L12Maj (F : ℝ → ℝ → ℝ) :
    Filter.Tendsto (fun z : ℝ => ∫ r in Set.Ioi z, L12Maj F r) Filter.atTop
      (nhds (0 : ℝ)) :=
  MeasureTheory.tendsto_integral_Ioi_zero (μ := volume) (f := L12Maj F)
    (b := fun z : ℝ => z) tendsto_id

/-- `L₁₂(F)(z) → 0` as `z → ∞` for `F ∈ L²`: `L₁₂(F) = 3 ∫_z^∞ F_*(r)/r dr`
(`Work.Elliptic.L12_eq_radial`), the integrand is dominated by the `L¹(Ioi 1)` majorant
`L12Maj F` (`abs_Fstar_div_le_Maj`, using `L2Mem F` through `Fstar_sq_le`), and the tail of
an `L¹` function vanishes at `∞`. -/
theorem L12_tendsto_atTop_zero (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    Filter.Tendsto (Work.Elliptic.L12 F) Filter.atTop (nhds (0 : ℝ)) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun z => 3 * ∫ r in Set.Ioi z, L12Maj F r)
    (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
    calc ‖Work.Elliptic.L12 F z‖ = ‖3 * Work.Elliptic.L12rad F z‖ := by
          rw [Work.Elliptic.L12_eq_radial]
      _ = 3 * ‖Work.Elliptic.L12rad F z‖ := by rw [norm_mul]; norm_num
      _ ≤ 3 * ∫ r in Set.Ioi z, L12Maj F r :=
          mul_le_mul_of_nonneg_left (norm_L12rad_le F hL2 hz) (by norm_num)
  · simpa using (tendsto_tail_L12Maj F).const_mul 3

end Work.FTS.EllipticEst
