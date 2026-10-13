/-
Copyright: work module for the Elgindi finite-time singularity project.

# `aeFirstEnergyDTools` — the slice toolkit for the first-energy estimate in the a.e. class

This module collects, in a clean import cone, the facts about the `θ`-slices of a datum
`Work.FTS.EllipticEst.H2W.Ae.AeData α u G` that the first-order (Step 1) estimate needs:

* `slice_pth_sq_D` — for every `z > 0` the slice `θ ↦ ∂_θu(z,θ)` is square integrable on `Iθ`
  (the honesty hypothesis of the constrained slice gap `Honest.Gap9Open`);
* `slice_sigma_sq_D` — for every `z > 0` the slice `θ ↦ ∂_θθu(z,θ)` is square integrable
  against `σ = sin(2θ)^{-η}`;
* `slice_u_sigma_sq_D` — the same for `u` itself (via the already proved `HkMem α 0 u`);
* `slice_z_smooth_D` — for interior `θ` the `z`-slice `z ↦ u z θ` is `C^∞` on `(0,∞)`;
* the elementary facts about the weights.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev AeData := Work.FTS.EllipticEst.H2W.Ae.AeData

/-! ## The truncated radial weights -/

/-- The radial weight `χ z · w(z)²` of the truncated energy identity. -/
def Wcut (χ : ℝ → ℝ) : ℝ → ℝ := fun z => χ z * (Work.Spaces.w z) ^ 2

/-- `χ z · w(z)² · z`. -/
def WcutZ (χ : ℝ → ℝ) : ℝ → ℝ := fun z => Wcut χ z * z

/-- `χ z · w(z)² · z²`. -/
def WcutZ2 (χ : ℝ → ℝ) : ℝ → ℝ := fun z => Wcut χ z * z ^ 2

theorem Wcut_nonneg {χ : ℝ → ℝ} (hχ : ∀ z, 0 ≤ χ z) (z : ℝ) : 0 ≤ Wcut χ z :=
  mul_nonneg (hχ z) (sq_nonneg _)

/-! ## The weights -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ_D {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) > 0` on the open interval. -/
theorem sin_two_pos_Ioo_D {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `σ θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
theorem sEta_nonneg_Iθ_D {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ_D hθ) _

/-- `1 ≤ σ θ` on the open interval. -/
theorem one_le_sEta_D {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  have hpos := sin_two_pos_Ioo_D hθ
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hpos hle
    (show -(Work.Spaces.eta) ≤ 0 by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

theorem w_nonneg_D (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w_pos_D {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem one_le_w_D {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
  nlinarith

/-! ## The level-`0` integrand -/

/-- On `Iθ` the level-`0` integrand is `w(z)² · g² · σ`. -/
theorem HkIntegrand_zero_D (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, mul_pow,
    Work.FTS.EllipticEst.Honest.sq_weight_eq (sin_two_nonneg_Iθ_D hθ)]
  simp only [Work.FTS.EllipticEst.sEta]
  ring

/-- The `θ`-integral of the level-`0` integrand, with `w(z)²` pulled out. -/
theorem integral_HkIntegrand_zero_D (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  exact HkIntegrand_zero_D α g hθ

/-! ## Slicewise honesty from the `ℋ⁰`-memberships -/

/-- **`σ`-honesty of the `θ`-slice of a function whose `ℋ⁰`-integrand is honest.** -/
theorem slice_sigma_sq_of_hkMem_D {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have h0 := hm.1 z (le_of_lt hz)
  have h1 := h0.const_mul (1 / (Work.Spaces.w z) ^ 2)
  have hw : Work.Spaces.w z ≠ 0 := ne_of_gt (w_pos_D hz)
  refine h1.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  show (1 / (Work.Spaces.w z) ^ 2) * Work.Spaces.HkIntegrand α 0 g z θ
    = (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  rw [HkIntegrand_zero_D α g hθ, ← mul_assoc, one_div,
    inv_mul_cancel₀ (pow_ne_zero 2 hw), one_mul]

/-- **The `θ`-slice of `∂_θθu` is `σ`-square integrable**, for every `z > 0`. -/
theorem slice_ang2_sigma_D {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
  slice_sigma_sq_of_hkMem_D h.memAng2 hz

/-- **The `θ`-slice of `∂_θu` is square integrable on `Iθ`**, for every `z > 0`
(the honesty hypothesis of the constrained slice gap). -/
theorem slice_pth_sq_D {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  -- the slice is `C¹` on the open interval
  have hslice : ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 1
  have hcont : ContinuousOn (fun θ => Work.Spaces.pth u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hd := hslice.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    simpa only [Work.Spaces.pth] using hd
  -- the measure comparison `volume.restrict Iθ = volume.restrict (0,π/2)`
  have hIoo : MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2))).symm
  obtain ⟨C, hCpos, hC⟩ :=
    Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
  refine MeasureTheory.IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (C ^ 2) ?_
  · rw [hIoo]
    exact (hcont.pow 2).aestronglyMeasurable measurableSet_Ioo
  · rw [hIoo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hb : |Work.Spaces.pth u z θ| ≤ C := (hC θ hθ).2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2

/-! ## The `z`-slices -/

/-- For interior `θ` the `z`-slice of an `AeData` datum is `C^∞` on `(0,∞)`. -/
theorem slice_z_smooth_D {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    ContDiffOn ℝ n (fun z => u z θ) (Set.Ioi 0) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact contDiffOn_iff_forall_nat_le.mp (hSO.curry_z hθ) n le_top

/-- For interior `θ` and `z > 0`, the `z`-derivative of the slice is `∂_zu`. -/
theorem slice_z_hasDerivAt_D {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => u z' θ) (Work.Spaces.pz u z θ) z := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact hSO.hasDerivAt_slice hθ hz

/-- The `z`-slice of `∂_z^j u` at `z`, for interior `θ`: `C^∞` on `(0,∞)`. -/
theorem slice_z_smooth_pz_succ_D {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => Work.Spaces.pz u z' θ) (Work.Spaces.pzIter 2 u z θ) z := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have h1 := hSO.hasDerivAt_slice_pzIter 1 hθ hz
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h1

end Work.FTS.EllipticEst.Dispatch
