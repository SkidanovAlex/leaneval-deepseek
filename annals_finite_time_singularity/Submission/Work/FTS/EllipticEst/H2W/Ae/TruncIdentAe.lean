import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.Zsq
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
-- ===== merged: Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.FTS.EllipticEst.H2W.Slot01W.Zsq`, so importing both was a duplicate-declaration error.
-- The names stay available to every consumer through the import above.
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Toolbox: smoothness of the source, measurability, Cauchy–Schwarz

The hypotheses of the certificate are `SmoothNbhd Ψ` (`Ψ` is smooth on a neighbourhood of
the closed quadrant) and `IsBslSol α F Ψ` (the elliptic law `F = bslOp α Ψ` on the open
quadrant `Q0 = (0,∞) × (0,π/2)`).  Together they give `SmoothOpen F`, i.e. `F` is `C^∞` on
the *open* quadrant: the certificate `Cert.SmoothOpen_bslOp` shows that `bslOp α Ψ` is
`C^∞` there, and `F` agrees with it on `Q0`.  Consequently

* `r ↦ F_*(F)(r)/r` is a.e. strongly measurable on `(0,∞)`
  (`aestronglyMeasurable_integral_Itheta_Q0`, a Fubini argument over the product measure);
* the Cauchy–Schwarz estimate `FstarDzIter_sq_mul_w_le_open` at `j = 0` reads
  `F_*(F)(r)²·w(r)² ≤ (π/2)·∫_θ (F(r,θ)·w(r)/sin(2θ)^{η/2})² dθ`. -/



/-! ## The two elementary pointwise estimates -/

/-- Young's inequality `√X·Y ≤ (X + Y²)/2` (valid for every `Y : ℝ`). -/
theorem sqrt_mul_le_half (X Y : ℝ) (hX : 0 ≤ X) : Real.sqrt X * Y ≤ (X + Y ^ 2) / 2 := by
  nlinarith [Real.sq_sqrt hX, sq_nonneg (Real.sqrt X - Y)]

/-- The radial weight is nonnegative. -/
theorem w_nonneg (r : ℝ) : 0 ≤ Work.Spaces.w r := by
  rw [Work.Spaces.w]; positivity

/-- **Cauchy–Schwarz for the angular moment, in the form used below**: for `r > 0`,

  `|F_*(F)(r)|·w(r) ≤ √((π/2)·∫_θ (F(r,θ)·w(r)/sin(2θ)^{η/2})² dθ)`. -/
theorem Fstar_mul_w_le_sqrt (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {r : ℝ} (hr : 0 < r) :
    |Work.Elliptic.Fstar F r| * Work.Spaces.w r
      ≤ Real.sqrt ((Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
          (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  set X : ℝ := (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
      (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (by positivity) (integral_nonneg fun θ => sq_nonneg _)
  have hsq : (Work.Elliptic.Fstar F r * Work.Spaces.w r) ^ 2 ≤ X := by
    rw [hX]
    have h := Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open α k F hF hmem 0 (Nat.zero_le k) hr
    simpa only [Work.Spaces.DzIter_zero, mul_pow] using h
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at h
  rwa [abs_mul, abs_of_nonneg (w_nonneg r)] at h

/-- **The angular slice of the weighted square of `F` is dominated by the `ℋ^k`-integrand**:
this is the `i = 0` term of the first sum of `Work.Spaces.HkIntegrand`. -/
theorem slice_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) {r : ℝ} (hr : r ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ,
        (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ :=
  integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 r hr)
    (Eventually.of_forall fun θ => by
      simpa only [Work.Spaces.DzIter_zero] using
        Work.Spaces.sq_le_HkIntegrand_z α k F r θ 0 (Nat.zero_le k))

/-! ## The majorants on `(0,1]` and on `(1,∞)`

Both use `|F_*(F)(r)|·w(r) ≤ √X(r)` with `X(r) = (π/2)∫_θ (…)²`, and then trade the weight
`w` against the radial factor `r`:

* on `(0,1]` one has `r²·w(r) = (1+r)² ≥ 1`, so `|F_*(F)(r)| ≤ √X(r)·r²` and hence
  `|F_*(F)(r)|/r ≤ √X(r)·r ≤ √X(r) ≤ (X(r)+1)/2`;
* on `(1,∞)` one has `w(r) ≥ 1`, so `|F_*(F)(r)|/r ≤ √X(r)/r ≤ (X(r) + r^{-2})/2`. -/

/-- **Majorant on `(0,1]`.** -/
theorem Fstar_div_le_majorant_Ioc (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 1) :
    |Work.Elliptic.Fstar F r| / r
      ≤ ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2 := by
  have hr0 : 0 < r := hr.1
  have hrI : r ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hr0
  set G : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ with hG
  set X : ℝ := (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
      (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (by positivity) (integral_nonneg fun θ => sq_nonneg _)
  have hXG : X ≤ (Real.pi / 2) * G := by
    rw [hX, hG]
    exact mul_le_mul_of_nonneg_left (slice_le_HkIntegrand α k F hmem hrI) (by positivity)
  have hAw : |Work.Elliptic.Fstar F r| * Work.Spaces.w r ≤ Real.sqrt X := by
    rw [hX]; exact Fstar_mul_w_le_sqrt α k F hF hmem hr0
  have hone : 1 ≤ r ^ 2 * Work.Spaces.w r := by
    rw [Work.Spaces.w]
    field_simp
    nlinarith [hr0]
  have hstep1 : |Work.Elliptic.Fstar F r| ≤ Real.sqrt X * r ^ 2 := by
    calc |Work.Elliptic.Fstar F r| = |Work.Elliptic.Fstar F r| * 1 := by ring
      _ ≤ |Work.Elliptic.Fstar F r| * (r ^ 2 * Work.Spaces.w r) :=
          mul_le_mul_of_nonneg_left hone (abs_nonneg _)
      _ = (|Work.Elliptic.Fstar F r| * Work.Spaces.w r) * r ^ 2 := by ring
      _ ≤ Real.sqrt X * r ^ 2 := mul_le_mul_of_nonneg_right hAw (by positivity)
  have hstep2 : |Work.Elliptic.Fstar F r| / r ≤ Real.sqrt X * r := by
    rw [div_eq_mul_inv]
    calc |Work.Elliptic.Fstar F r| * r⁻¹ ≤ (Real.sqrt X * r ^ 2) * r⁻¹ :=
          mul_le_mul_of_nonneg_right hstep1 (by positivity)
      _ = Real.sqrt X * r := by
          rw [mul_assoc, sq, mul_assoc, mul_inv_cancel₀ hr0.ne', mul_one]
  have hstep3 : Real.sqrt X * r ≤ Real.sqrt X := by
    nth_rewrite 2 [← mul_one (Real.sqrt X)]
    exact mul_le_mul_of_nonneg_left hr.2 (Real.sqrt_nonneg _)
  have hstep4 : Real.sqrt X ≤ (X + 1) / 2 := by
    simpa using sqrt_mul_le_half X 1 hXnn
  calc |Work.Elliptic.Fstar F r| / r ≤ Real.sqrt X * r := hstep2
    _ ≤ Real.sqrt X := hstep3
    _ ≤ (X + 1) / 2 := hstep4
    _ ≤ ((Real.pi / 2) * G + 1) / 2 := by linarith [hXG]

/-- **Majorant on `(1,∞)`.** -/
theorem Fstar_div_le_majorant_Ioi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {r : ℝ} (hr : 1 < r) :
    |Work.Elliptic.Fstar F r| / r
      ≤ ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
          + (r⁻¹) ^ 2) / 2 := by
  have hr0 : 0 < r := by linarith
  have hrI : r ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hr0
  set G : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ with hG
  set X : ℝ := (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
      (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (by positivity) (integral_nonneg fun θ => sq_nonneg _)
  have hXG : X ≤ (Real.pi / 2) * G := by
    rw [hX, hG]
    exact mul_le_mul_of_nonneg_left (slice_le_HkIntegrand α k F hmem hrI) (by positivity)
  have hAw : |Work.Elliptic.Fstar F r| * Work.Spaces.w r ≤ Real.sqrt X := by
    rw [hX]; exact Fstar_mul_w_le_sqrt α k F hF hmem hr0
  have hone : 1 ≤ Work.Spaces.w r := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < r ^ 2)]
    nlinarith [hr]
  have hstep1 : |Work.Elliptic.Fstar F r| ≤ Real.sqrt X := by
    calc |Work.Elliptic.Fstar F r| = |Work.Elliptic.Fstar F r| * 1 := by ring
      _ ≤ |Work.Elliptic.Fstar F r| * Work.Spaces.w r :=
          mul_le_mul_of_nonneg_left hone (abs_nonneg _)
      _ ≤ Real.sqrt X := hAw
  have hstep2 : |Work.Elliptic.Fstar F r| / r ≤ Real.sqrt X * r⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hstep1 (by positivity)
  have hstep3 : Real.sqrt X * r⁻¹ ≤ (X + (r⁻¹) ^ 2) / 2 := sqrt_mul_le_half X r⁻¹ hXnn
  calc |Work.Elliptic.Fstar F r| / r ≤ Real.sqrt X * r⁻¹ := hstep2
    _ ≤ (X + (r⁻¹) ^ 2) / 2 := hstep3
    _ ≤ ((Real.pi / 2) * G + (r⁻¹) ^ 2) / 2 := by linarith [hXG]

/-! ## The certificate -/


end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgmScratchSect =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.DzAmgmSect

open Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Step 1: the identity between the two forms of the pure angular weight -/

/-- On the angular interval `Iθ`, the pure summand of `HkIntegrand` written with the division
`w z / sin(2θ)^{η/2}` equals the same summand written with the product `w z · angZ θ`
(`angZ θ = sin(2θ)^{-η/2}`).  At the two endpoints both sides vanish. -/
theorem mul_angZ_eq_mul_div (z θ x : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    x * Work.Spaces.w z * angZ θ
      = x * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  rcases eq_or_ne (Real.sin (2 * θ)) 0 with h | h
  · have hη : ((-(Work.Spaces.eta / 2)) : ℝ) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    have hη2 : ((Work.Spaces.eta / 2) : ℝ) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    have hzero : angZ θ = 0 := by rw [angZ, h, Real.zero_rpow hη]
    rw [hzero, mul_zero, h, Real.zero_rpow hη2, div_zero, mul_zero]
  · have hnn : 0 ≤ Real.sin (2 * θ) := by
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
      exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    rw [angZ, div_eq_mul_inv, Real.rpow_neg hnn]
    ring

/-! ## Step 2: a.e. strong measurability of the `z`-slices -/

/-- The `z`-slice of a function continuous on the open quadrant is a.e. strongly measurable on
`Iz = [0,∞)`. -/
theorem aesm_zs (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable (fun z => g (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun z : ℝ => g (z, θ)) (Set.Ioi 0) :=
    hg.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hz, hθ⟩)
  have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => g (z, θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hset : (Set.Ioi (0 : ℝ)) =ᵐ[MeasureTheory.volume] Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact MeasureTheory.Ioi_ae_eq_Ici
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set hset.symm
  rw [hmeas]
  exact h1

/-! ## Step 3: splitting a finite sum out of the double `lintegral` -/

/-- **Splitting a finite sum of summands continuous on the open quadrant.**  For a finite family
of real functions continuous on `Q0`, the double (`θ`-then-`z`) `lintegral` of the finite sum of
their `ofReal`-lifts is the sum of the individual double `lintegral`s.  Both `ℒ²`-measurability
inputs come from the continuity on `Q0` (the `z`-slices for the inner integral and the joint
a.e. strong measurability for the partial `θ`-integral). -/
theorem lintegral_sum_split {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ)
    (hF : ∀ m ∈ s, ContinuousOn (fun p : ℝ × ℝ => F m p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ∑ m ∈ s, ENNReal.ofReal (F m z θ))
      = ∑ m ∈ s, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (F m z θ) := by
  classical
  -- a.e. angle in the open interval
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      refine MeasureTheory.Measure.restrict_congr_set ?_
      rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hset]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  -- the inner integral splits for a.e. angle
  have hsplit : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫⁻ z in Work.Spaces.Iz, ∑ m ∈ s, ENNReal.ofReal (F m z θ))
        = ∑ m ∈ s, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (F m z θ) := by
    filter_upwards [hae] with θ hθ
    exact MeasureTheory.lintegral_finsetSum' s fun m hm =>
      ((aesm_zs _ (hF m hm) hθ).aemeasurable.ennreal_ofReal)
  -- the partial `z`-integrals are a.e. strongly measurable in `θ`
  have hθmeas : ∀ m ∈ s, AEMeasurable
      (fun θ => ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (F m z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro m hm
    have huncurry : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (F m p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      ((Work.Spaces.aesm_of_continuousOn_Qd _ (hF m hm)).aemeasurable).ennreal_ofReal
    exact huncurry.lintegral_prod_left'
  rw [MeasureTheory.lintegral_congr_ae hsplit]
  exact MeasureTheory.lintegral_finsetSum' s hθmeas

/-! ## Step 4: domain conversions -/

theorem lintegral_Iθ_eq_Ioo (f : ℝ → ℝ≥0∞) :
    ∫⁻ θ in Work.Spaces.Iθ, f θ = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ := by
  have h : MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [Work.Spaces.Iθ, h]

theorem lintegral_Iz_eq_Ioi (f : ℝ → ℝ≥0∞) :
    ∫⁻ z in Work.Spaces.Iz, f z = ∫⁻ z in Set.Ioi (0 : ℝ), f z := by
  have h : MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [Work.Spaces.Iz, h]

/-- The double integral over `Iθ × Iz` equals the double integral over the open quadrant
(angular variable first). -/
theorem lintegral_prod_eq_open (F : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, F θ z)
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ), F θ z := by
  rw [lintegral_Iθ_eq_Ioo]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact lintegral_Iz_eq_Ioi _

/-- The reverse direction of the previous lemma. -/
theorem lintegral_open_eq_prod (F : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ), F θ z)
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, F θ z :=
  (lintegral_prod_eq_open F).symm

/-- The pure summand in the `angZ`-form equals the summand of `HkIntegrand` (division form). -/
theorem pure_ofReal_eq (f : ℝ → ℝ → ℝ) (m : ℕ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    ENNReal.ofReal ((Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ) ^ 2)
      = ENNReal.ofReal ((Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  have h1 : Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ
      = Work.Spaces.DzIter m f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
    mul_angZ_eq_mul_div z θ (Work.Spaces.DzIter m f z θ) hθ
  have h2 : (Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ) ^ 2
      = (Work.Spaces.DzIter m f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [h1]
  rw [h2]

/-- The mixed summand in the `w · angM`-form equals the summand of `HkIntegrand` (using `Wt`). -/
theorem mixed_ofReal_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (i j : ℕ) (z θ : ℝ) :
    ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2)
      = ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
  have h1 : Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ
      = Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ := by
    rw [mul_assoc]; rfl
  have h2 : (Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [h1]
  rw [h2]

/-! ## Step 5: the termwise Agmon–Nirenberg estimate -/

/-- **Termwise AM–GM, pure summands.**  Applying `TermAMGMLintegral` with `V = D_z^m f`,
`wth = angZ` and rewriting `D_z (D_z^m f) = D_z^{m+1} f`,
`z²∂_z²(D_z^m f) = D_z^m (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate for `TZ`. -/
theorem TZ_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (m : ℕ),
      ENNReal.ofReal (α ^ 2) * TZ f (m + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) m + TZ f m) := by
  intro α hα hα1 f hf m
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angZ θ := fun θ hθ =>
    angZ_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.DzIter m f) angZ (hf.DzIter m) hang
  -- the first factor of the left-hand integrand
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ * Work.Spaces.w z
          * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter (m + 1) f z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [Work.Spaces.DzIter_succ]
  -- the second-derivative factor of the right-hand side
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
          * Work.Spaces.w z * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter m (zsqPz2 f) z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := ZsqPz2Comm f hf m 0 (show (z, θ) ∈ Q0 from ⟨hz, hθ⟩)
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
        = Work.Spaces.DzIter m (zsqPz2 f) z θ := hcomm
    rw [h1]
  rw [hL, hR2] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-- **Termwise AM–GM, mixed summands.**  Applying `TermAMGMLintegral` with
`V = D_z^j D_θ^i f`, `wth = angM α` and rewriting `D_z (D_z^j D_θ^i f) = D_z^{j+1} D_θ^i f`,
`z²∂_z²(D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate. -/
theorem TM_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (i j : ℕ),
      ENNReal.ofReal (α ^ 2) * TM α f i (j + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) i j + TM α f i j) := by
  intro α hα hα1 f hf i j
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angM α θ := fun θ hθ =>
    angM_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.mixed j i f) (angM α) (hf.mixed j i) hang
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed j i f) z θ * Work.Spaces.w z
          * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed (j + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hdz : Work.Spaces.Dz (Work.Spaces.mixed j i f)
        = Work.Spaces.mixed (j + 1) i f := by
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
    rw [hdz]
    exact mixed_ofReal_eq α f i (j + 1) z θ
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
          * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i (zsqPz2 f) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := ZsqPz2Comm f hf j i (show (z, θ) ∈ Q0 from ⟨hz, hθ⟩)
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
        = Work.Spaces.mixed j i (zsqPz2 f) z θ := hcomm
    rw [h1, mixed_ofReal_eq α (zsqPz2 f) i j z θ]
  have hR3 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact mixed_ofReal_eq α f i j z θ
  rw [hL, hR2, hR3] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-! ## Step 6: the pure/mixed parts of `HkIntegrand` -/

/-- The pure (`D_z`-) part of `HkIntegrand α k g`, as a real function. -/
def purePart (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed part of `HkIntegrand α k g`, as a real function. -/
def mixedPart (α : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0)

theorem HkIntegrand_eq_parts (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k g z θ = purePart g k z θ + mixedPart α g k z θ := rfl

theorem purePart_nonneg (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : 0 ≤ purePart g k z θ :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem mixedPart_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : 0 ≤ mixedPart α g k z θ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> simp [sq_nonneg]

theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hfun]
  refine hw.mul ?_
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem continuousOn_pureTerm (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Q0 :=
  (((hg.DzIter i).continuousOn).mul continuousOn_wdivsin_Q0).pow 2

theorem continuousOn_mixedTerm (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) (k i j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
        else 0)) Q0 := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · simp only [if_pos hc]
    exact (((hg.mixed j i).continuousOn).mul (continuousOn_Wt α)).pow 2
  · simp only [if_neg hc]
    exact continuousOn_const


/-- a.e. angles lie in the open interval. -/
theorem ae_mem_Ioo_theta : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- a.e. radii are positive. -/
theorem ae_mem_Ioi_z : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
    z ∈ Set.Ioi (0 : ℝ) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iz]; exact MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-- The family of summands of `HkIntegrand α k g`, indexed by `ℕ ⊕ (ℕ × ℕ)`
(pure indices on the left, mixed indices on the right). -/
def termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) : ℕ ⊕ (ℕ × ℕ) → ℝ → ℝ → ℝ
  | Sum.inl i => fun z θ => (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
  | Sum.inr p => fun z θ => (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
      (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)

theorem continuousOn_termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (σ : ℕ ⊕ (ℕ × ℕ)) :
    ContinuousOn (fun p : ℝ × ℝ => termFamily α k g σ p.1 p.2) Q0 := by
  rcases σ with i | p
  · exact continuousOn_pureTerm g hg i
  · exact continuousOn_mixedTerm α g hg k p.1 p.2

/-- Summing over a disjoint sum of finsets. -/
theorem sum_disjSum_eq {α β M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (f : α ⊕ β → M) :
    (∑ σ ∈ s.disjSum t, f σ) = (∑ a ∈ s, f (Sum.inl a)) + (∑ b ∈ t, f (Sum.inr b)) := by
  rw [← Finset.map_inl_disjUnion_map_inr, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.inl_apply, Function.Embedding.inr_apply]

/-- `ofReal` of a finite sum of nonnegative reals, in one index. -/
theorem ofReal_sum_range (k : ℕ) (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i) :
    (∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (h i))
      = ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), h i) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hh i)]

/-- `ofReal` of a finite double sum of nonnegative reals. -/
theorem ofReal_sum_range₂ (k : ℕ) (h : ℕ → ℕ → ℝ) (hh : ∀ i j, 0 ≤ h i j) :
    (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (h i j))
      = ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), h i j) := by
  have hinner : ∀ i, (∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (h i j))
      = ENNReal.ofReal (∑ j ∈ Finset.range (k + 1), h i j) := fun i =>
    ofReal_sum_range k (h i) (hh i)
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  exact ofReal_sum_range k (fun i => ∑ j ∈ Finset.range (k + 1), h i j)
    (fun i => Finset.sum_nonneg fun j _ => hh i j)

/-- The sum of the `ofReal`-lifts of the summand family is the `ofReal` of `HkIntegrand`. -/
theorem sum_termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (∑ σ ∈ (Finset.range (k + 1)).disjSum
        ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
        ENNReal.ofReal (termFamily α k g σ z θ))
      = ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) := by
  rw [sum_disjSum_eq]
  have hpure : (∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
        (termFamily α k g (Sum.inl a) z θ)) = ENNReal.ofReal (purePart g k z θ) := by
    simp only [termFamily, purePart]
    exact ofReal_sum_range k _ (fun a => sq_nonneg _)
  have hmixed : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)), ENNReal.ofReal
        (termFamily α k g (Sum.inr p) z θ)) = ENNReal.ofReal (mixedPart α g k z θ) := by
    rw [Finset.sum_product]
    simp only [termFamily, mixedPart]
    exact ofReal_sum_range₂ k _ (fun i j => by split_ifs <;> simp [sq_nonneg])
  rw [hpure, hmixed, ← ENNReal.ofReal_add (purePart_nonneg g k z θ)
    (mixedPart_nonneg α g k z θ), ← HkIntegrand_eq_parts]

/-- **Decomposition of `LkSq` into its individual summands.**  The honest `lintegral` of the
`H^k`-integrand of `g` is the sum of the honest sizes of its pure and mixed summands. -/
theorem LkSq_eq_sum (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    LkSq α k g
      = (∑ i ∈ Finset.range (k + 1), TZ g i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α g p.1 p.2 else 0) := by
  classical
  have hsplit := lintegral_sum_split
    ((Finset.range (k + 1)).disjSum ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))))
    (termFamily α k g) (fun σ _ => continuousOn_termFamily α k g hg σ)
  have hLHS : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ∑ σ ∈ (Finset.range (k + 1)).disjSum
          ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
          ENNReal.ofReal (termFamily α k g σ z θ)) = LkSq α k g := by
    show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ∑ σ ∈ (Finset.range (k + 1)).disjSum
          ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
          ENNReal.ofReal (termFamily α k g σ z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact sum_termFamily α k g z θ
  rw [hLHS] at hsplit
  rw [hsplit]
  rw [sum_disjSum_eq]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (termFamily α k g (Sum.inl i) z θ)) = TZ g i
    rw [TZ]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (pure_ofReal_eq g i z θ (by
      rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)).symm
  · refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc]
      show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (termFamily α k g (Sum.inr p) z θ)) = TM α g p.1 p.2
      rw [TM]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [termFamily, if_pos hc]
    · rw [if_neg hc]
      have hzero : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (termFamily α k g (Sum.inr p) z θ)) = 0 := by
        have hterm : termFamily α k g (Sum.inr p) = fun _ _ => (0 : ℝ) := by
          funext z θ; simp only [termFamily, if_neg hc]
        rw [hterm]
        simp
      rw [hzero]

/-! ## Step 7: re-indexing `TZ` and `TM` of `D_z f` -/

theorem DzIter_succ_eq (m : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (m + 1) f = Work.Spaces.DzIter m (Work.Spaces.Dz f) := by
  rw [Work.Spaces.DzIter_add_right m 1 f]
  rfl

/-- `z²∂_z² h = D_z² h − D_z h` on the open quadrant, for `h` smooth there. -/
theorem zsqPz2_eq_sub (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    zsqPz2 g z θ = Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ := by
  have h1 : DifferentiableAt ℝ (fun z' => g z' θ) z := (hg.hasDerivAt_slice hθ hz).differentiableAt
  have h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz g z' θ) z :=
    (hg.hasDerivAt_slice_pzIter 1 hθ hz).differentiableAt
  simpa only [zsqPz2] using Work.FTS.EllipticEst.zsq_pzIter2_eq g h1 h2


theorem TZ_Dz (f : ℝ → ℝ → ℝ) (i : ℕ) :
    TZ (Work.Spaces.Dz f) i = TZ f (i + 1) := by
  simp only [TZ]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  rw [DzIter_succ_eq]

theorem TM_Dz_of_comm (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hcomm : ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) (a b : ℕ) :
    TM α (Work.Spaces.Dz f) a b = TM α f a (b + 1) := by
  simp only [TM]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_Ioo_theta] with θ hθ
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_Ioi_z] with z hz
  have hpoint : Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
      = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ := hcomm a z θ ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter b (Work.Spaces.Dz (Work.Spaces.DthIter a f)) z θ :=
    SmoothOpen.DzIter_congr (F := Work.Spaces.DthIter a (Work.Spaces.Dz f))
      (G := Work.Spaces.Dz (Work.Spaces.DthIter a f))
      (fun z' θ' hz' h1 h2 => hcomm a z' θ' ⟨hz', ⟨h1, h2⟩⟩) b z θ hz hθ.1 hθ.2
  have hgoal : Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.mixed (b + 1) a f z θ := by
    simp only [Work.Spaces.mixed] at hcongr ⊢
    rw [hcongr, DzIter_succ_eq]
  rw [hgoal]

/-- Distributing a constant over a conditionally-defined finite sum of pairs. -/
theorem sum_ite_mul_split {s : Finset (ℕ × ℕ)} {k : ℕ} (B Cc : ℝ≥0∞)
    (x y : ℕ × ℕ → ℝ≥0∞) :
    (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then B * (Cc * x p + y p) else 0))
      = (B * Cc) * (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then x p else 0))
        + B * (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then y p else 0)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
  · rw [if_pos hc, if_pos hc, if_pos hc]; ring
  · rw [if_neg hc, if_neg hc, if_neg hc]; ring

/-! ## Step 8: the main `LkSq` inequality -/

/-! ## Step 8: the main `LkSq` inequality -/

/-- The second radial derivative of a smooth-on-the-quadrant function is smooth. -/
theorem SmoothOpen_zsqPz2 (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) : SmoothOpen (zsqPz2 f) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2) Q0 := by
    fun_prop
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 f p.1 p.2) Q0 := hf.pzIter 2
  have h3 := h1.mul h2
  have hfun : Function.uncurry (zsqPz2 f)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 f p.1 p.2 := by
    funext p; rfl
  rw [SmoothOpen, hfun]
  exact h3


/-- **The `θ`-integrated radial interpolation for `D_z f`, at the level of the honest
`lintegral`s.** -/
theorem LkSq_Dz_le (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (k : ℕ) (f : ℝ → ℝ → ℝ),
      (∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
        Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
          = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) →
      SmoothOpen f →
      ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) := by
  intro α hα hα1 k f hcomm hf
  have hDz : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQ : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hdec : LkSq α k (Work.Spaces.Dz f)
      = (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0) := by
    rw [LkSq_eq_sum α k (Work.Spaces.Dz f) hDz]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => TZ_Dz f i
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc, TM_Dz_of_comm α f hcomm p.1 p.2]
      · rw [if_neg hc, if_neg hc]
  have hdecQ : LkSq α k (zsqPz2 f)
      = (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0) :=
    LkSq_eq_sum α k (zsqPz2 f) hQ
  have hdecf : LkSq α k f
      = (∑ i ∈ Finset.range (k + 1), TZ f i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0) :=
    LkSq_eq_sum α k f hf
  -- the termwise bounds
  have hT : ∀ i ∈ Finset.range (k + 1), ENNReal.ofReal (α ^ 2) * TZ f (i + 1)
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) i + TZ f i) :=
    fun i _ => TZ_termwise C1 hC1 hgen α hα hα1 f hf i
  have hM : ∀ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
      (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
              ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0) := by
    intro p _
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc, if_pos hc]
      exact TM_termwise C1 hC1 hgen α hα hα1 f hf p.1 p.2
    · rw [if_neg hc, if_neg hc, mul_zero]
  -- the two sums
  have hS1le : ENNReal.ofReal (α ^ 2) * (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
            + (∑ i ∈ Finset.range (k + 1), TZ f i)) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum hT) (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
  have hS2le : ENNReal.ofReal (α ^ 2)
        * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4)
              * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0))
            + (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0))) := by
    rw [Finset.mul_sum]
    have hstep : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
          ENNReal.ofReal (α ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
        = ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
              then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [hstep]
    refine le_trans (Finset.sum_le_sum hM) (le_of_eq ?_)
    have hflat : ∀ p : ℕ × ℕ,
        ENNReal.ofReal (C1 ^ 2) * (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
            ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0)
          = (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (C1 ^ 2) *
                (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2)
              else 0) := by
      intro p; by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k <;> simp [hc]
    rw [Finset.sum_congr rfl (fun p _ => hflat p)]
    rw [sum_ite_mul_split (k := k) (ENNReal.ofReal (C1 ^ 2)) (ENNReal.ofReal (α ^ 4))
      (fun p => TM α (zsqPz2 f) p.1 p.2) (fun p => TM α f p.1 p.2)]
    rw [mul_add]
    ring
  -- combine
  rw [hdec, mul_add]
  refine le_trans (add_le_add hS1le hS2le) (le_of_eq ?_)
  rw [hdecQ, hdecf]
  ring

/-! ## Step 9: the bridges between `HkSq` and `LkSq` -/

/-- The `ofReal` of a Bochner integral of a nonnegative function is dominated by the
`lintegral` of the `ofReal`-lift. -/
theorem ofReal_integral_le_lintegral (s : Set ℝ) (u : ℝ → ℝ) (hu : ∀ θ, 0 ≤ u θ) :
    ENNReal.ofReal (∫ θ in s, u θ) ≤ ∫⁻ θ in s, ENNReal.ofReal (u θ) := by
  by_cases hg : IntegrableOn u s
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hu)]
  · rw [MeasureTheory.integral_undef hg]; simp

/-- The uncurried `H^k`-integrand is a.e. strongly measurable for the product of the restricted
measures (in either order). -/
theorem aesm_HkIntegrand_prod (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  ((Work.Spaces.aesm_of_continuousOn_Qd _ (hg.continuousOn_HkIntegrand α k)).aemeasurable).ennreal_ofReal

theorem HkSq_forall_smooth (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => (smoothOpen_iff_forall g).mp hg n

/-- `LkSq` written as the `z`-integral of the `ofReal` of the `θ`-integral. -/
theorem LkSq_eq_theta_integral (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) :
    LkSq α k g = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
  have hswap : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) :=
    MeasureTheory.lintegral_lintegral_swap
      ((aesm_HkIntegrand_prod α k g hg).prod_swap)
  have heq : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)] with z hz
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm
  rw [LkSq, hswap, heq]


/-- Honesty of `LkSq` from `HkMem`. -/
theorem LkSq_lt_top (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) : LkSq α k g < ⊤ := by
  rw [LkSq_eq_theta_integral α k g hg hmem]
  exact MeasureTheory.Integrable.lintegral_lt_top hmem.2

/-- Under honesty (`HkMem`), `LkSq` is the `ofReal` of `HkSq`. -/
theorem LkSq_eq_ofReal_HkSq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) :
    LkSq α k g = ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  have hforall := HkSq_forall_smooth g hg
  rw [LkSq_eq_theta_integral α k g hg hmem,
    Work.FTS.EllipticEst.HkSq_eq_lintegral α k g hforall]
  have hA : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) < ⊤ := by
    rw [← LkSq_eq_theta_integral α k g hg hmem]
    exact LkSq_lt_top α k g hg hmem
  exact (ENNReal.ofReal_toReal (ne_of_lt hA)).symm

/-- `√(x+y) ≤ √x + √y` for nonnegative reals. -/
theorem sqrt_add_le_sqrt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-! ## Step 10: from the `LkSq` inequality to the norm inequality -/

/-- The commutation hypothesis of `LkSq_Dz_le`, from the coprime theorem
`DthIterDzCommOpen`. -/
theorem comm_hyp (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) :
    ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ :=
  fun a z θ h => (DthIterDzCommOpen f hf a h).symm

/-- Finiteness of `LkSq (D_z f)` from the `LkSq` inequality. -/
theorem LkSq_Dz_lt_top (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f)) :
    LkSq α k (Work.Spaces.Dz f) < ⊤ := by
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ (SmoothOpen_zsqPz2 f hf) hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  have hfin : ENNReal.ofReal (C1 ^ 2) *
      (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin, hffin⟩
  have hlt : ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f) < ⊤ := lt_of_le_of_lt h hfin
  have hpos : ENNReal.ofReal (α ^ 2) ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < α ^ 2)).ne'
  rcases ENNReal.mul_lt_top_iff.mp hlt with ⟨-, h2⟩ | h0 | h0
  · exact h2
  · exact absurd h0 hpos
  · exact lt_top_iff_ne_top.mpr (by simp [h0])
/-- **The norm inequality**, given the honesty of `D_z f`. -/
theorem HkNorm_Dz_le_of (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f))
    (hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f)) :
    α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
      ≤ C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by
  have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQSm : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hDzfin := LkSq_Dz_lt_top C1 hC1 hgen α hα hα1 k f hf hmf hmQ
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ hQSm hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  -- (★) in terms of `HkSq`
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  rw [LkSq_eq_ofReal_HkSq α k (Work.Spaces.Dz f) hDzSm hmDz,
    LkSq_eq_ofReal_HkSq α k (zsqPz2 f) hQSm hmQ,
    LkSq_eq_ofReal_HkSq α k f hf hmf] at h
  have hnn : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz f) :=
    Work.Spaces.HkSq_nonneg α k _
  have hnnQ : 0 ≤ Work.Spaces.HkSq α k (zsqPz2 f) := Work.Spaces.HkSq_nonneg α k _
  have hnnf : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hL : ENNReal.ofReal (α ^ 2) * ENNReal.ofReal (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      = ENNReal.ofReal (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 2)]
  have hR : ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) *
        ENNReal.ofReal (Work.Spaces.HkSq α k (zsqPz2 f)) + ENNReal.ofReal (Work.Spaces.HkSq α k f))
      = ENNReal.ofReal (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
          + Work.Spaces.HkSq α k f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C1 ^ 2),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)) hnnf,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 4)]
  rw [hL, hR] at h
  have hsq : α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  -- take square roots
  have hsqrt : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := by
    have h1 : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
        = Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
      rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
    have h2 : C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        = Real.sqrt (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
            + Work.Spaces.HkSq α k f)) := by
      rw [Real.sqrt_mul (sq_nonneg C1), Real.sqrt_sq hC1.le]
    rw [h1, h2]
    exact Real.sqrt_le_sqrt hsq
  have hf1 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
      = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ α ^ 4), Work.Spaces.HkNorm,
      show Real.sqrt (α ^ 4) = α ^ 2 by
        rw [show α ^ 4 = (α ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ α ^ 2)]]
  have hadd : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
      ≤ α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
    calc Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
          + Real.sqrt (Work.Spaces.HkSq α k f) :=
          sqrt_add_le_sqrt _ _ (by positivity) (Work.Spaces.HkSq_nonneg α k f)
      _ = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
          rw [hf1]
          rfl
  calc α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := hsqrt
    _ ≤ C1 * (α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f) :=
        mul_le_mul_of_nonneg_left hadd (le_of_lt hC1)
    _ = C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by ring

/-! ## Step 11: pointwise decomposition of the `H^k`-integrand of `D_z f` -/

/-- `D_z² X = z²∂_z²X + D_z X` on the open quadrant. -/
theorem DzIter_two_decomp (X : ℝ → ℝ → ℝ) (hX : SmoothOpen X) :
    Set.EqOn (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 X z θ
        - (zsqPz2 X z θ + Work.Spaces.Dz X z θ))) (fun _ : ℝ × ℝ => (0 : ℝ)) Q0 := by
  intro y hy
  obtain ⟨hz, hθ⟩ := hy
  have h := zsqPz2_eq_sub X hX hz hθ
  show Work.Spaces.DzIter 2 X y.1 y.2
    - (zsqPz2 X y.1 y.2 + Work.Spaces.Dz X y.1 y.2) = 0
  rw [h]; ring








end Work.FTS.EllipticEst.DzAmgmSect
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `truncIdentAe` — the truncated energy identity in the almost-everywhere class

For `AeData α u G`, a weight `W ∈ C²` with compact support, vanishing near `0`, the truncated
`w²`-energy identity holds.  The proof follows the paper's route of
`Work.FTS.EllipticEst.TruncIdentity`, rebuilt in the weak (`AeData`) class:

* `G` is replaced by `bslOp α u` (they agree on the open quadrant, a conull set);
* for each `θ ∈ (0,π/2)` the one-dimensional `z`-integration by parts is applied to the slice
  `z ↦ u z θ` with the radial weight `σ = W w²` (`remov.ibpZZ`, `remov.ibpZ`);
* the resulting identity is integrated in `θ` and the five double integrals are swapped by
  Fubini.  The joint integrability that Fubini needs is the analytic content of the weak class.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## 1. Elementary facts about the weight `w` and the angle -/

private theorem w_sq_eq (z : ℝ) : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  ring

private theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

private theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

private theorem sin_two_nonneg_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])

private theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The level-`0` integrand in the `w²σ` form. -/
private theorem HkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ (sin_two_nonneg_Iθ_prv hθ)]

private theorem contDiffOn_w_sq :
    ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2 := by
    funext z
    rw [Work.Spaces.w, div_pow]
  rw [hfun]
  exact ContDiffOn.div (((contDiffOn_const.add contDiffOn_id).pow 2).pow 2)
    ((contDiffOn_id.pow 2).pow 2)
    (fun z hz => pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz)))

private theorem contDiffOn_sigma (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) :
    ContDiffOn ℝ 2 (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
  hW.contDiffOn.mul contDiffOn_w_sq

/-! ## 2. Support facts -/

private theorem W_eq_zero_of_large (W : ℝ → ℝ) (h : HasCompactSupport W) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℝ, R < |z| → W z = 0 := by
  obtain ⟨R, hRpos, hR⟩ := h.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R, hRpos, fun z hz => image_eq_zero_of_notMem_tsupport (fun hmem => ?_)⟩
  have h1 := hR z hmem
  rw [Real.norm_eq_abs] at h1
  linarith

private theorem W_bdd (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (h : HasCompactSupport W) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ, |W z| ≤ M := by
  obtain ⟨R, hRpos, hR⟩ := W_eq_zero_of_large W h
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-R) R)).exists_bound_of_continuousOn
    (hW.continuous.continuousOn : ContinuousOn W (Set.Icc (-R) R))
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc (-R) R
  · have h1 := hC z hz
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  · have hz' : R < |z| := by
      by_cases h : z ≤ 0
      · have h2 : z < -R := by
          by_contra hcon
          exact hz ⟨by linarith [not_lt.mp hcon], by linarith⟩
        rw [abs_of_nonpos h]
        linarith
      · have hzpos : 0 < z := not_le.mp h
        rw [abs_of_pos hzpos]
        by_contra hcon
        exact hz ⟨by linarith, not_lt.mp hcon⟩
    rw [hR z hz']
    exact le_trans (le_of_eq abs_zero) (le_max_right _ _)

/-! ## 3. Two general integration lemmas -/

/-- Extension of an integral from a compact support. -/
private theorem integrableOn_Ioi_of_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (h0 : ∀ z : ℝ, z < a → f z = 0) (hb : ∀ z : ℝ, b < z → f z = 0) :
    IntegrableOn f (Set.Ioi 0) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hint : IntegrableOn f (Set.Icc a b) :=
    (hcont.mono hsub).integrableOn_compact isCompact_Icc
  have hind : Integrable ((Set.Icc a b).indicator f) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr hint
  have heq : f =ᵐ[volume] (Set.Icc a b).indicator f := by
    filter_upwards with z
    by_cases hz : z ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      by_cases hza : z < a
      · exact h0 z hza
      · have hzb : b < z := by
          have h1 : a ≤ z := not_lt.mp hza
          by_contra hcon
          exact hz ⟨h1, not_lt.mp hcon⟩
        exact hb z hzb
  exact (hind.congr heq.symm).integrableOn

/-- The derivative of a function vanishing off an interval vanishes there as well. -/
private theorem deriv_zero_of_zero {f : ℝ → ℝ} {δ R : ℝ}
    (hfδ : ∀ z : ℝ, z < δ → f z = 0) (hfR : ∀ z : ℝ, R < z → f z = 0) :
    (∀ z : ℝ, z < δ → deriv f z = 0) ∧ (∀ z : ℝ, R < z → deriv f z = 0) := by
  constructor
  · intro z hz
    have hmem : Set.Iio δ ∈ 𝓝 z := Iio_mem_nhds hz
    have hev : f =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hmem] with y hy
      show f y = 0
      exact hfδ y hy
    rw [hev.deriv_eq]
    simpa using deriv_const z (0 : ℝ)
  · intro z hz
    have hmem : Set.Ioi R ∈ 𝓝 z := Ioi_mem_nhds hz
    have hev : f =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hmem] with y hy
      show f y = 0
      exact hfR y hy
    rw [hev.deriv_eq]
    simpa using deriv_const z (0 : ℝ)


/-! ## 4. A.e. facts about the product measure -/

private theorem ae_restrict_Iz_Ioi :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
  have h : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
  have hmem := MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume)
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
  rwa [h] at hmem


private theorem ae_prod_fst_pos :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 :=
  (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (measurableSet_Ioi.preimage measurable_fst)).mpr
    (ae_restrict_Iz_Ioi.mono fun x hx => Filter.Eventually.of_forall fun _ => hx)





/-! ## 5. Joint integrability of the level-`0` integrand from `HkMem` -/


/-! ## 6. Smoothness certificates on the open quadrant -/

private theorem slice_contDiffOn {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffOn ℝ 2 (fun z : ℝ => u z θ) (Set.Ioi 0) := by
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun z hz => ⟨hz, hθ⟩
  exact (hsm 2).comp (by fun_prop) hmap

private theorem smoothOpen_Lzero {u : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen u) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero u) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hso 2))
        (Work.FTS.EllipticEst.SmoothOpen.pth
          (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
            Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hso)))
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hso))
    (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])


/-! ## 7. Joint integrability of the five integrands -/


/-! ## 8. The identity on one angular slice -/

private theorem slice_ident (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hsupp : HasCompactSupport W)
    (hvan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → W z = 0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi 0, W z * (Work.Spaces.w z) ^ 2 * (G z θ * u z θ))
      = α ^ 2 * (∫ z in Set.Ioi 0,
            W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
        + (∫ z in Set.Ioi 0,
            W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (u z θ) ^ 2)
        + (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
  obtain ⟨δ, hδpos, hδW⟩ := hvan
  obtain ⟨R, hRpos, hRW⟩ := W_eq_zero_of_large W hsupp
  let φ : ℝ → ℝ := fun z => u z θ
  let σ : ℝ → ℝ := fun z => W z * (Work.Spaces.w z) ^ 2
  have hσ2 : ContDiffOn ℝ 2 σ (Set.Ioi 0) := contDiffOn_sigma W hW
  have hφ2 : ContDiffOn ℝ 2 φ (Set.Ioi 0) := slice_contDiffOn h.smooth hθ
  have hσδ : ∀ z : ℝ, z < δ → σ z = 0 := fun z hz => by
    show W z * (Work.Spaces.w z) ^ 2 = 0
    rw [hδW z (le_of_lt hz), zero_mul]
  have hσR : ∀ z : ℝ, R < z → σ z = 0 := fun z hz => by
    show W z * (Work.Spaces.w z) ^ 2 = 0
    have h1 : W z = 0 := hRW z (by rw [abs_of_pos (lt_trans hRpos hz)]; linarith)
    rw [h1, zero_mul]
  have hσc : ContinuousOn σ (Set.Ioi 0) := hσ2.continuousOn
  have hφc : ContinuousOn φ (Set.Ioi 0) := hφ2.continuousOn
  have hφ1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) := hφ2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hφ1c : ContinuousOn (deriv φ) (Set.Ioi 0) := hφ1.continuousOn
  have hφ2c : ContinuousOn (deriv (deriv φ)) (Set.Ioi 0) :=
    hφ1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hA2 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * σ z) (Set.Ioi 0) :=
    ((contDiffOn_id : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi 0)).pow 2).mul hσ2
  have hA1 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => z ^ 2 * σ z)) (Set.Ioi 0) :=
    hA2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hAc : ContinuousOn (fun z : ℝ => z ^ 2 * σ z) (Set.Ioi 0) := hA2.continuousOn
  have hA1c : ContinuousOn (deriv (fun z : ℝ => z ^ 2 * σ z)) (Set.Ioi 0) := hA1.continuousOn
  have hA2c : ContinuousOn (deriv (deriv (fun z : ℝ => z ^ 2 * σ z))) (Set.Ioi 0) :=
    hA1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hB2 : ContDiffOn ℝ 2 (fun z : ℝ => z * σ z) (Set.Ioi 0) :=
    (contDiffOn_id : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi 0)).mul hσ2
  have hBc : ContinuousOn (fun z : ℝ => z * σ z) (Set.Ioi 0) := hB2.continuousOn
  have hB1c : ContinuousOn (deriv (fun z : ℝ => z * σ z)) (Set.Ioi 0) :=
    hB2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hLc : ContinuousOn (fun z : ℝ => Work.Elliptic.Lzero u z θ) (Set.Ioi 0) :=
    (smoothOpen_Lzero (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)).curry_z hθ
      |>.continuousOn
  have hAσδ : ∀ z : ℝ, z < δ → (fun z : ℝ => z ^ 2 * σ z) z = 0 := fun z hz => by
    show z ^ 2 * σ z = 0
    rw [hσδ z hz]; ring
  have hAσR : ∀ z : ℝ, R < z → (fun z : ℝ => z ^ 2 * σ z) z = 0 := fun z hz => by
    show z ^ 2 * σ z = 0
    rw [hσR z hz]; ring
  have hdA := deriv_zero_of_zero hAσδ hAσR
  have hdA2 := deriv_zero_of_zero hdA.1 hdA.2
  have hBσδ : ∀ z : ℝ, z < δ → (fun z : ℝ => z * σ z) z = 0 := fun z hz => by
    show z * σ z = 0
    rw [hσδ z hz]; ring
  have hBσR : ∀ z : ℝ, R < z → (fun z : ℝ => z * σ z) z = 0 := fun z hz => by
    show z * σ z = 0
    rw [hσR z hz]; ring
  have hdB := deriv_zero_of_zero hBσδ hBσR
  -- integrability of the seven pieces (compact support)
  have hi1 : IntegrableOn (fun z : ℝ => z ^ 2 * σ z * φ z * deriv (deriv φ) z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (((continuousOn_id.pow 2).mul hσc).mul hφc |>.mul hφ2c)
      (fun z hz => by
        show z ^ 2 * σ z * φ z * deriv (deriv φ) z = 0
        rw [hσδ z hz]; ring)
      (fun z hz => by
        show z ^ 2 * σ z * φ z * deriv (deriv φ) z = 0
        rw [hσR z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi2 : IntegrableOn
      (fun z : ℝ => deriv (fun z : ℝ => z ^ 2 * σ z) z * φ z * deriv φ z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      ((hA1c.mul hφc).mul hφ1c)
      (fun z hz => by
        show deriv (fun z : ℝ => z ^ 2 * σ z) z * φ z * deriv φ z = 0
        rw [hdA.1 z hz]; ring)
      (fun z hz => by
        show deriv (fun z : ℝ => z ^ 2 * σ z) z * φ z * deriv φ z = 0
        rw [hdA.2 z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi3 : IntegrableOn (fun z : ℝ => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (hσc.mul ((continuousOn_id.mul hφ1c).pow 2))
      (fun z hz => by
        show σ z * (z * deriv φ z) ^ 2 = 0
        rw [hσδ z hz]; ring)
      (fun z hz => by
        show σ z * (z * deriv φ z) ^ 2 = 0
        rw [hσR z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi4 : IntegrableOn
      (fun z : ℝ => deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (hA2c.mul (hφc.pow 2))
      (fun z hz => by
        show deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2 = 0
        rw [hdA2.1 z hz]; ring)
      (fun z hz => by
        show deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2 = 0
        rw [hdA2.2 z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi5 : IntegrableOn (fun z : ℝ => z * σ z * φ z * deriv φ z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (((continuousOn_id.mul hσc).mul hφc).mul hφ1c)
      (fun z hz => by
        show z * σ z * φ z * deriv φ z = 0
        rw [hσδ z hz]; ring)
      (fun z hz => by
        show z * σ z * φ z * deriv φ z = 0
        rw [hσR z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi6 : IntegrableOn
      (fun z : ℝ => deriv (fun z : ℝ => z * σ z) z * (φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (hB1c.mul (hφc.pow 2))
      (fun z hz => by
        show deriv (fun z : ℝ => z * σ z) z * (φ z) ^ 2 = 0
        rw [hdB.1 z hz]; ring)
      (fun z hz => by
        show deriv (fun z : ℝ => z * σ z) z * (φ z) ^ 2 = 0
        rw [hdB.2 z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi7 : IntegrableOn
      (fun z : ℝ => σ z * (Work.Elliptic.Lzero u z θ * φ z)) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (hσc.mul (hLc.mul hφc))
      (fun z hz => by
        show σ z * (Work.Elliptic.Lzero u z θ * φ z) = 0
        rw [hσδ z hz]; ring)
      (fun z hz => by
        show σ z * (Work.Elliptic.Lzero u z θ * φ z) = 0
        rw [hσR z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  -- the boundary conditions of the two integrations by parts
  have hb1 : Tendsto (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hδpos] with z hz
    show (0 : ℝ) = z ^ 2 * σ z * φ z * deriv φ z
    rw [hσδ z hz.2]; ring
  have hb2 : Tendsto (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z) atTop (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (R + 1)] with z hz
    show (0 : ℝ) = z ^ 2 * σ z * φ z * deriv φ z
    rw [hσR z (by linarith)]; ring
  have hb3 : Tendsto (fun z : ℝ => deriv (fun z : ℝ => z ^ 2 * σ z) z * (φ z) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hδpos] with z hz
    show (0 : ℝ) = deriv (fun z : ℝ => z ^ 2 * σ z) z * (φ z) ^ 2
    rw [hdA.1 z hz.2]; ring
  have hb4 : Tendsto (fun z : ℝ => deriv (fun z : ℝ => z ^ 2 * σ z) z * (φ z) ^ 2)
      atTop (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (R + 1)] with z hz
    show (0 : ℝ) = deriv (fun z : ℝ => z ^ 2 * σ z) z * (φ z) ^ 2
    rw [hdA.2 z (by linarith)]; ring
  have hb5 : Tendsto (fun z : ℝ => z * σ z * (φ z) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hδpos] with z hz
    show (0 : ℝ) = z * σ z * (φ z) ^ 2
    rw [hσδ z hz.2]; ring
  have hb6 : Tendsto (fun z : ℝ => z * σ z * (φ z) ^ 2) atTop (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (R + 1)] with z hz
    show (0 : ℝ) = z * σ z * (φ z) ^ 2
    rw [hσR z (by linarith)]; ring
  -- the equation on the slice
  have hGz : ∀ z ∈ Set.Ioi (0 : ℝ), G z θ
      = -(α ^ 2 * z ^ 2) * deriv (deriv φ) z - (α * (5 + α) * z) * deriv φ z
        + Work.Elliptic.Lzero u z θ := by
    intro z hz
    have h1 := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at h1
    have e1 : Work.Spaces.pzIter 2 u z θ = deriv (deriv φ) z := by
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      rfl
    have e2 : Work.Spaces.pz u z θ = deriv φ z := by
      simp only [Work.Spaces.pz]
      rfl
    rw [e1, e2] at h1
    linarith [h1]
  have hstep1 : (∫ z in Set.Ioi 0, σ z * (G z θ * φ z))
      = ∫ z in Set.Ioi 0, σ z * ((-(α ^ 2 * z ^ 2) * deriv (deriv φ) z
          - (α * (5 + α) * z) * deriv φ z + Work.Elliptic.Lzero u z θ) * φ z) := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
    exact Filter.Eventually.of_forall (fun z hz => by rw [hGz z hz])
  have hstep2 : (∫ z in Set.Ioi 0, σ z * ((-(α ^ 2 * z ^ 2) * deriv (deriv φ) z
        - (α * (5 + α) * z) * deriv φ z + Work.Elliptic.Lzero u z θ) * φ z))
      = -(α ^ 2) * (∫ z in Set.Ioi 0, σ z * z ^ 2 * deriv (deriv φ) z * φ z)
        - (α * (5 + α)) * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) * φ z)
        + (∫ z in Set.Ioi 0, σ z * (Work.Elliptic.Lzero u z θ * φ z)) := by
    have hfun : (fun z : ℝ => σ z * ((-(α ^ 2 * z ^ 2) * deriv (deriv φ) z
          - (α * (5 + α) * z) * deriv φ z + Work.Elliptic.Lzero u z θ) * φ z))
        = fun z : ℝ => (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
          + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z)
          + σ z * (Work.Elliptic.Lzero u z θ * φ z) := by
      funext z; ring
    rw [hfun]
    have hIa : Integrable (fun z : ℝ =>
        (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (hi1.const_mul (-(α ^ 2))).congr (Filter.Eventually.of_forall fun z => by ring)
    have hIb : Integrable (fun z : ℝ =>
        (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (hi5.const_mul (-(α * (5 + α)))).congr (Filter.Eventually.of_forall fun z => by ring)
    have hIc : Integrable (fun z : ℝ => σ z * (Work.Elliptic.Lzero u z θ * φ z))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := hi7
    have hIab : Integrable (fun z : ℝ =>
        (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
          + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := hIa.add hIb
    have e1 : (∫ z in Set.Ioi 0,
          (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
            + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z)
            + σ z * (Work.Elliptic.Lzero u z θ * φ z))
        = (∫ z in Set.Ioi 0,
            (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
              + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
          + (∫ z in Set.Ioi 0, σ z * (Work.Elliptic.Lzero u z θ * φ z)) :=
      MeasureTheory.integral_add hIab hIc
    have e2 : (∫ z in Set.Ioi 0,
            (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
              + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
        = (∫ z in Set.Ioi 0, (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z))
          + (∫ z in Set.Ioi 0, (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z)) :=
      MeasureTheory.integral_add hIa hIb
    have e3 : (∫ z in Set.Ioi 0, (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z))
        = (-(α ^ 2)) * (∫ z in Set.Ioi 0, σ z * z ^ 2 * deriv (deriv φ) z * φ z) :=
      MeasureTheory.integral_const_mul (-(α ^ 2))
        (fun z : ℝ => σ z * z ^ 2 * deriv (deriv φ) z * φ z)
    have e4 : (∫ z in Set.Ioi 0, (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
        = (-(α * (5 + α))) * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) * φ z) :=
      MeasureTheory.integral_const_mul (-(α * (5 + α)))
        (fun z : ℝ => σ z * (z * deriv φ z) * φ z)
    rw [e1, e2, e3, e4]
    ring
  have hP := Work.FTS.EllipticEst.remov.ibpZZ σ φ hσ2 hφ2 hi1 hi2 hi3 hi4 hb1 hb2 hb3 hb4
  have hQ := Work.FTS.EllipticEst.remov.ibpZ σ φ hσ2 hφ2 hi5 hi6 hb5 hb6
  have eA : (∫ z in Set.Ioi 0, deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2)
      = ∫ z in Set.Ioi 0, deriv (deriv (fun z : ℝ => σ z * z ^ 2)) z * (φ z) ^ 2 := by
    have h1 : (fun z : ℝ => z ^ 2 * σ z) = fun z : ℝ => σ z * z ^ 2 := by
      funext z; ring
    rw [h1]
  have eB : (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) ^ 2)
      = ∫ z in Set.Ioi 0, σ z * z ^ 2 * (deriv φ z) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    ring
  have eC : (∫ z in Set.Ioi 0, deriv (fun z : ℝ => z * σ z) z * (φ z) ^ 2)
      = ∫ z in Set.Ioi 0, deriv (fun z : ℝ => σ z * z) z * (φ z) ^ 2 := by
    have h1 : (fun z : ℝ => z * σ z) = fun z : ℝ => σ z * z := by
      funext z; ring
    rw [h1]
  have hmain : (∫ z in Set.Ioi 0, σ z * (G z θ * φ z))
      = α ^ 2 * (∫ z in Set.Ioi 0, σ z * z ^ 2 * (deriv φ z) ^ 2)
        + (∫ z in Set.Ioi 0, σ z * (Work.Elliptic.Lzero u z θ * φ z))
        - (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun z : ℝ => σ z * z ^ 2)) z * (φ z) ^ 2)
        + (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun z : ℝ => σ z * z) z * (φ z) ^ 2) := by
    rw [hstep1, hstep2, hP, hQ, eA, eC, eB]
    ring
  exact hmain


end Work.FTS.EllipticEst.H2W.Ae
end
end
