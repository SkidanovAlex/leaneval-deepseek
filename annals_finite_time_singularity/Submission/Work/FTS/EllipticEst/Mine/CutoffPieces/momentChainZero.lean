/-
Copyright: work module for the Elgindi finite-time singularity project.

# `momentChainZero` — the two lowest radial angular moments of a level-`0` weak datum vanish

For a datum `h : EllWeakPos α 0 F Ψ` of the level-`0` weak class (Elgindi, Annals **194** (2021),
Proposition `prop:L2`), the angular moments of `∂_zΨ` and of `∂_z²Ψ` against the profile
`sinθcos²θ` vanish almost everywhere in `z`, and the two slices are honest `L¹`-functions.

## Route

* The `L¹`-honesty of the `∂_zΨ`-slice is `WeakMoment.PzSliceIntegrable` (the equation
  `α(5+α)z∂_zΨ = Lzero Ψ - α²z²∂_z²Ψ - F` on the open quadrant, together with the
  `η`-weighted `L²`-honesty of `F`, `z²∂_z²Ψ`, `∂_θθΨ`).
* The `L¹`-honesty of the `∂_z²Ψ`-slice is the absorption
  `|g·sinθcos²θ| ≤ (g·w/sin(2θ)^{η/2})² + 1` applied to the `memA`-slot.
* The *vanishing* of the first moment is `pzSliceFubiniZero`: it gives
  `∫_r^{z₁} (∫_θ ∂_zΨ(z,θ)sinθcos²θ) dz = 0` for all `0 < r < z₁`; since
  `z ↦ ∫_θ ∂_zΨ(z,θ)sinθcos²θ` is locally integrable, the Lebesgue differentiation theorem
  (`LocallyIntegrable.ae_hasDerivAt_integral`) upgrades this to a.e.-vanishing.
* The *vanishing* of the second moment is the same argument one order up:
  `moment_relation` applied to `u := ∂_zΨ` gives
  `(∫_θ ∂_zΨ(b,θ)sinθcos²θ) - (∫_θ ∂_zΨ(a,θ)sinθcos²θ) = ∫_a^b (∫_θ ∂_z²Ψ(s,θ)sinθcos²θ) ds`
  for all `0 < a < b`; with the first moment vanishing a.e. this makes the primitive of the second
  moment constant on a dense set, hence constant, hence the second moment vanishes a.e.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.WeakMoment.PzSliceIntegrable
import Submission.Work.FTS.EllipticEst.remov.pzSinCos2_rectIntegrable
import Submission.Work.FTS.EllipticEst.remov.pzSliceFubiniZero
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.integrableOn_box_of_slice
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine.CutoffPieces

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary angular helpers -/

/-- The angular profile `sinθcos²θ` is a.e. strongly measurable on `Iθ`. -/
private lemma aesm_sinCos2 :
    MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  show MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) _
  fun_prop

/-- Multiplication by the angular profile preserves a.e. strong measurability. -/
private lemma aesm_mul_sinCos2 {g : ℝ → ℝ}
    (hg : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  hg.mul aesm_sinCos2

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
private lemma sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  rw [Work.Elliptic.sinCos2]
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h1, Real.pi_pos]⟩
  positivity

/-- The angular profile is continuous. -/
private lemma continuous_sinCos2 : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  fun_prop

/-- The level-`0` `HkIntegrand` is the single weighted square. -/
private lemma HkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.DzIter_zero]

/-- `sEta` is nonnegative on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-- A slice a.e. strongly measurable and bounded by `C` against `sinθcos²θ` on the open interval
is integrable on `Iθ` (`Iθ` has finite measure). -/
private lemma integrableOn_mul_sinCos2_of_norm_bound {g : ℝ → ℝ} {C : ℝ}
    (hg : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |g θ * Work.Elliptic.sinCos2 θ| ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => g θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := C) (μ := MeasureTheory.volume)
      (s := Work.Spaces.Iθ) (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (by simp)) (aesm_mul_sinCos2 hg) ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs]
  exact hb θ hθ

/-! ## The `Ψ`-slice is `L¹` against the angular profile -/

/-- For a level-`0` weak datum and every `z > 0`, the slice `θ ↦ Ψ z θ sinθcos²θ` is integrable.
Only the `∂_θθΨ`-slot (`memB`) of the class and the smoothness on the open quadrant are used:
`abs_le_of_sq_mul_sEta` bounds the slice by `C` on `(0,π/2)`. -/
theorem psi_slice_L1 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hΨ.pth).pth
  have hE : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hB h.memB 0 (le_refl 0) hz
  have hsm : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hΨ hz
  obtain ⟨C, -, hC⟩ := Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta hsm
    (by simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
        using hE)
  refine integrableOn_mul_sinCos2_of_norm_bound
    (Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ hz) (C := C) (fun θ hθ => ?_)
  rw [abs_mul]
  calc |Ψ z θ| * |Work.Elliptic.sinCos2 θ|
      ≤ |Ψ z θ| * 1 := mul_le_mul_of_nonneg_left
          (Work.FTS.EllipticEst.abs_sinCos2_le_one ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
          (abs_nonneg _)
    _ = |Ψ z θ| := by ring
    _ ≤ C := (hC θ hθ).2

/-! ## The `∂_z²Ψ`-integrand: slice and box integrability -/

/-- The `η`-weighted square of `∂_z²Ψ` is slice-integrable: the `memA`-slot, rescaled by the
constant `(z⁴ w(z)²)⁻¹`. -/
private theorem pzIter2_sq_sEta_slice (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  intro z hz
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hΨ
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_zSummand α 0 hA h.memA 0 (le_refl 0) hzI
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  refine (h1.const_mul ((z ^ 4 * (Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    (Work.Spaces.w z) hθ]
  rw [Work.FTS.EllipticEst.sEta]
  have hz4w : z ^ 4 * (Work.Spaces.w z) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 (ne_of_gt hz)) (pow_ne_zero 2 hw)
  field_simp

/-- The slicewise `L¹`-integrability of `∂_z²Ψ` against `sinθcos²θ`. -/
private theorem pzIter2_abs_slice (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hsigned := (Work.FTS.EllipticEst.remov.ws_absMoment
    (Work.FTS.EllipticEst.remov.ws_aesm_slice (hΨ.pzIter 2) hz)
    (pzIter2_sq_sEta_slice α F Ψ h z hz)).1
  refine (hsigned.norm).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_of_mem_Iθ hθ)]

/-- The `θ`-integral of the `memA`-slot is radially integrable on compacts: the `memA`-second
half, rescaled by the bounded factor `s ↦ (s⁴ w(s)²)⁻¹`. -/
private theorem pzIter2_sq_sEta_integrableOn (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Icc a b) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hΨ
  -- the source integrability of the `HkIntegrand`-slot
  have hF : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      ((s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ)
        * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (Set.Icc a b) := by
    refine (h.memA.2.mono_set ?_).congr ?_
    · intro x hx
      exact Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s _
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (HkIntegrand_zero_eq' α _ s))
  -- `F = s⁴ w(s)² · G` pointwise on `Icc a b`
  have hG : ∀ s ∈ Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = (s ^ 4 * (Work.Spaces.w s) ^ 2)⁻¹ * (∫ θ in Work.Spaces.Iθ,
          ((s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ)
            * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq (s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ)
      (Work.Spaces.w s) hθ]
    rw [Work.FTS.EllipticEst.sEta]
    have hw : Work.Spaces.w s ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hs0))
    have hs4w : s ^ 4 * (Work.Spaces.w s) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 4 (ne_of_gt hs0)) (pow_ne_zero 2 hw)
    field_simp
  -- the factor `s ↦ (s⁴ w(s)²)⁻¹` is bounded on `[a,b]`
  have hcont : ContinuousOn (fun s : ℝ => (s ^ 4 * (Work.Spaces.w s) ^ 2)⁻¹)
      (Set.Icc a b) := by
    refine ContinuousOn.inv₀ ?_ ?_
    · refine ContinuousOn.mul (ContinuousOn.pow continuousOn_id 4) (ContinuousOn.pow ?_ 2)
      rw [show Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 from rfl]
      exact (continuousOn_const.add continuousOn_id).pow 2 |>.div
        (continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hx.1)))
    · intro x hx
      exact mul_ne_zero (pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le ha hx.1)))
        (pow_ne_zero 2 (by
          rw [Work.Spaces.w]
          exact div_ne_zero (pow_ne_zero 2 (by linarith [lt_of_lt_of_le ha hx.1]))
            (pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hx.1)))))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hcont
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    ((hcont.aestronglyMeasurable measurableSet_Icc).mul hF.aestronglyMeasurable).congr
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
        exact (hG s hs).symm)
  refine MeasureTheory.Integrable.mono' (hF.norm.const_mul C) haesm ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    rw [hG s hs, Real.norm_eq_abs, abs_mul]
    have hb : |(s ^ 4 * (Work.Spaces.w s) ^ 2)⁻¹| ≤ C := by simpa using hC s hs
    have h2 : |(s ^ 4 * (Work.Spaces.w s) ^ 2)⁻¹| * |∫ θ in Work.Spaces.Iθ,
        ((s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ)
          * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2| ≤ C * ‖∫ θ in Work.Spaces.Iθ,
        ((s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ)
          * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2‖ := by
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    exact h2

/-- **The radial integrability of `∫_θ |∂_z²Ψ| sinθcos²θ`.**

The slice bound `∫_θ |g| sinθcos²θ ≤ π/2 + ∫_θ g² sin(2θ)^{-η}` (`ws_absMoment`) dominates the
integrand by an integrable function `s ↦ π/2 + φ(s)` (`φ` is the `θ`-integral of the `memA`-slot);
Tonelli in its `∫⁻`-form (`MeasureTheory.lintegral_prod`) then upgrades the finite *iterated*
integral to joint integrability, and Fubini (`Integrable.integral_prod_left`) gives the radial
integrability. -/
private theorem pzIter2_abs_outer (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {r z₁ : ℝ} (hr : 0 < r) (hrz : r < z₁) :
    MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) (Set.Icc r z₁) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  haveI hfinμ : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Icc r z₁)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc r z₁) with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hν
  set G : ℝ → ℝ → ℝ := fun s θ =>
    |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ with hG
  set φ : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hφ
  -- the dominator is integrable and nonnegative
  have hφint : MeasureTheory.Integrable φ μ := by
    rw [hφ, hμ]
    exact pzIter2_sq_sEta_integrableOn α F Ψ hα h hr hrz
  have hφnn : 0 ≤ᵐ[μ] φ := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    rw [hφ]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ)
  -- the pointwise slice bound
  have hslice_bound : ∀ s ∈ Set.Icc r z₁, ∫ θ in Work.Spaces.Iθ, G s θ
      ≤ Real.pi / 2 + φ s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr hs.1
    rw [hG, hφ]
    exact (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice (hΨ.pzIter 2) hs0)
      (pzIter2_sq_sEta_slice α F Ψ h s hs0)).2
  -- `G s` is `ν`-integrable and nonnegative
  have hslice (s : ℝ) (hs : s ∈ Set.Icc r z₁) : MeasureTheory.Integrable (G s) ν := by
    rw [hG, hν]
    exact pzIter2_abs_slice α F Ψ h s (lt_of_lt_of_le hr hs.1)
  have hGnn : ∀ s : ℝ, ∀ᵐ θ ∂ν, 0 ≤ G s θ := by
    intro s
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hG]
    exact mul_nonneg (abs_nonneg _) (sinCos2_nonneg_of_mem_Iθ hθ)
  -- the measure comparison with the closed quadrant
  have hle : μ.prod ν ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hμ, hν]
    refine MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono ?_ le_rfl) le_rfl
    intro x hx
    exact Set.mem_Ici.mpr (le_trans (le_of_lt hr) hx.1)
  -- the iterated `∫⁻` is finite
  have hkey : ∫⁻ s, (∫⁻ θ, ENNReal.ofReal (G s θ) ∂ν) ∂μ < ⊤ := by
    have h1 : (fun s : ℝ => ∫⁻ θ, ENNReal.ofReal (G s θ) ∂ν)
        =ᵐ[μ] (fun s : ℝ => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, G s θ)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
      rw [hν]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hslice s hs) (hGnn s)).symm
    calc ∫⁻ s, (∫⁻ θ, ENNReal.ofReal (G s θ) ∂ν) ∂μ
        = ∫⁻ s, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, G s θ) ∂μ :=
          MeasureTheory.lintegral_congr_ae h1
      _ ≤ ∫⁻ s, ENNReal.ofReal (Real.pi / 2 + φ s) ∂μ := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
          exact ENNReal.ofReal_le_ofReal (hslice_bound s hs)
      _ = ENNReal.ofReal (∫ s : ℝ, (Real.pi / 2 + φ s) ∂μ) := by
          refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            ((MeasureTheory.integrable_const (Real.pi / 2)).add hφint) ?_).symm
          filter_upwards [hφnn] with s hs
          have hp : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
          exact add_nonneg hp hs
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- the positivity of `G` a.e. on the product
  have hae_prod : ∀ᵐ p ∂(μ.prod ν), 0 ≤ G p.1 p.2 := by
    rw [hμ, hν, MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    rw [hG]
    exact mul_nonneg (abs_nonneg _) (sinCos2_nonneg_of_mem_Iθ hp.2)
  -- Tonelli: the joint lintegral of the norm is finite
  have hcontG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    rw [hG]
    exact ((hΨ.pzIter 2).continuousOn.abs).mul
      ((continuous_sinCos2.comp continuous_snd).continuousOn)
  have hmeasG : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (G p.1 p.2)) (μ.prod ν) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((Work.Spaces.aesm_of_continuousOn_Qd _ hcontG).mono_measure hle).aemeasurable)
  have hprod : ∫⁻ p, ENNReal.ofReal ‖(Function.uncurry G) p‖ ∂(μ.prod ν) < ⊤ := by
    calc ∫⁻ p, ENNReal.ofReal ‖(Function.uncurry G) p‖ ∂(μ.prod ν)
        = ∫⁻ p, ENNReal.ofReal (G p.1 p.2) ∂(μ.prod ν) := by
          refine MeasureTheory.lintegral_congr_ae ?_
          filter_upwards [hae_prod] with p hp
          rw [show (Function.uncurry G) p = G p.1 p.2 from rfl, Real.norm_of_nonneg hp]
      _ = ∫⁻ s, (∫⁻ θ, ENNReal.ofReal (G s θ) ∂ν) ∂μ :=
          MeasureTheory.lintegral_prod _ hmeasG
      _ < ⊤ := hkey
  -- joint integrability, then Fubini
  have hfin : MeasureTheory.HasFiniteIntegral (Function.uncurry G) (μ.prod ν) :=
    (MeasureTheory.hasFiniteIntegral_iff_norm (Function.uncurry G)).mpr hprod
  have hjoint : MeasureTheory.Integrable (Function.uncurry G) (μ.prod ν) := by
    refine ⟨?_, hfin⟩
    rw [hG]
    exact (Work.Spaces.aesm_of_continuousOn_Qd _
      (((hΨ.pzIter 2).continuousOn.abs).mul
        ((continuous_sinCos2.comp continuous_snd).continuousOn))).mono_measure hle
  have hout := hjoint.integral_prod_left
  rw [hμ, hν] at hout
  rw [hG] at hout
  simpa only [MeasureTheory.IntegrableOn, Function.uncurry_apply_pair] using hout

/-- **The `η`-weighted box integrability of `∂_z²Ψ`.** -/
private theorem pzIter2_sigma_box (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab ?_ ?_ ?_ ?_
  · refine ((hΨ.pzIter 2).continuousOn.pow 2).mul ?_
    show ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro p hp
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])))
  · intro z _ θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ)
  · intro s hs
    exact pzIter2_sq_sEta_slice α F Ψ h s (lt_of_lt_of_le ha hs.1)
  · exact pzIter2_sq_sEta_integrableOn α F Ψ hα h ha hab

/-! ## The first moment: rectangle integrability and vanishing of its interval integrals -/

/-- The uncurried `(z,θ) ↦ ∂_zΨ(z,θ) sinθcos²θ` is integrable on the box `(r,z₁] × Iθ`. -/
theorem rectIntegrable_pzΨ {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {r z₁ : ℝ} (hr : 0 < r) (hrz : r < z₁) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ : ℝ =>
        Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.FTS.EllipticEst.remov.pzSinCos2_rectIntegrable
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) hr hrz
    (Work.FTS.EllipticEst.WeakMoment.PzSliceIntegrable α F Ψ hα h r hr)
    (fun z hz => pzIter2_abs_slice α F Ψ h z (lt_of_lt_of_le hr hz.1))
    (pzIter2_abs_outer α F Ψ hα h hr hrz)

/-- The interval integral of the first moment vanishes: `∫_r^{z₁} ∫_θ ∂_zΨ sinθcos²θ = 0`. -/
theorem intervalIntegral_M1_eq_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {r z₁ : ℝ} (hr : 0 < r) (hrz : r < z₁) :
    (∫ z in r..z₁, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 :=
  (Work.FTS.EllipticEst.remov.pzSliceFubiniZero
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) hr hrz
    (psi_slice_L1 h hr) (psi_slice_L1 h (lt_trans hr hrz)) (h.orthPsi r hr)
    (h.orthPsi z₁ (lt_trans hr hrz)) (rectIntegrable_pzΨ hα hα4 h hr hrz)).1.trans
  (Work.FTS.EllipticEst.remov.pzSliceFubiniZero
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) hr hrz
    (psi_slice_L1 h hr) (psi_slice_L1 h (lt_trans hr hrz)) (h.orthPsi r hr)
    (h.orthPsi z₁ (lt_trans hr hrz)) (rectIntegrable_pzΨ hα hα4 h hr hrz)).2

/-- The first moment `z ↦ ∫_θ ∂_zΨ(z,θ) sinθcos²θ` is interval integrable. -/
theorem intervalIntegrable_M1 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {r z₁ : ℝ} (hr : 0 < r) (hrz : r < z₁) :
    IntervalIntegrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) MeasureTheory.volume r z₁ := by
  have hInt : MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict (Set.Ioc r z₁)) := by
    have := (rectIntegrable_pzΨ hα hα4 h hr hrz).integral_prod_left
    simpa only [Function.uncurry_apply_pair] using this
  have hInt' : MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict (Set.Icc r z₁)) := by
    rwa [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc] at hInt
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hrz.le]
  exact hInt'

/-! ## An interval-vanishing criterion -/

/-- **A locally integrable function whose integrals over every interval `[a,b]` (`0 < a < b`)
vanish is a.e. zero on `(0,∞)`.**  The Lebesgue differentiation theorem
(`IntervalIntegrable.ae_hasDerivAt_integral`) identifies `f` a.e. with the derivative of its
primitive `x ↦ ∫_a^x f`, which is identically zero on `(a,∞)`. -/
theorem ae_zero_of_intervalIntegral_zero {f : ℝ → ℝ}
    (hint : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable f MeasureTheory.volume a b)
    (hzero : ∀ a b : ℝ, 0 < a → a < b → ∫ t in a..b, f t = 0) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), f z = 0 := by
  have hstep : ∀ a b : ℝ, 0 < a → a < b →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc a b)), f x = 0 := by
    intro a b ha hab
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral (hint a b ha hab)
    rw [Set.uIcc_of_le hab.le] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have hne : ∀ᵐ x : ℝ, x ≠ a := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hldt, hne] with x hx hxne hxmem
    have hxa : a < x := lt_of_le_of_ne hxmem.1 (Ne.symm hxne)
    have hder := hx hxmem a ⟨le_rfl, hab.le⟩
    have hfun : (fun y : ℝ => ∫ t in a..y, f t) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hxa] with y hy
      exact hzero a y ha hy
    have hder0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (f x) x :=
      hder.congr_of_eventuallyEq hfun.symm
    exact hder0.unique (hasDerivAt_const x 0)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  have hbad : MeasureTheory.volume {z : ℝ | 0 < z ∧ f z ≠ 0} = 0 := by
    have hsub : {z : ℝ | 0 < z ∧ f z ≠ 0} ⊆ ⋃ n : ℕ,
        ({z : ℝ | f z ≠ 0} ∩ Set.Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 1)) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_ge (max (1 / z) z)
      refine Set.mem_iUnion.mpr ⟨n, hz.2, ?_, ?_⟩
      · have hn' : (1 : ℝ) / z ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
        have hn'' : (1 : ℝ) / z ≤ (n : ℝ) + 2 := by linarith
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
        rw [div_le_iff₀ hz.1] at hn''
        linarith
      · have hz' : z ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
        linarith
    refine le_antisymm ?_ bot_le
    calc MeasureTheory.volume {z : ℝ | 0 < z ∧ f z ≠ 0}
        ≤ MeasureTheory.volume (⋃ n : ℕ, ({z : ℝ | f z ≠ 0}
            ∩ Set.Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 1))) :=
          MeasureTheory.measure_mono hsub
      _ ≤ ∑' n : ℕ, MeasureTheory.volume ({z : ℝ | f z ≠ 0}
            ∩ Set.Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 1)) :=
          MeasureTheory.measure_iUnion_le _
      _ = 0 := by
          have hzero' : ∀ n : ℕ, MeasureTheory.volume ({z : ℝ | f z ≠ 0}
              ∩ Set.Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 1)) = 0 := by
            intro n
            have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
            have hlt : 1 / ((n : ℝ) + 2) < (n : ℝ) + 1 := by
              have h1 : 1 / ((n : ℝ) + 2) < 1 := by
                rw [div_lt_one (by positivity)]
                have : (0 : ℝ) ≤ (n : ℝ) := by positivity
                linarith
              have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
                have : (0 : ℝ) ≤ (n : ℝ) := by positivity
                linarith
              linarith
            have h := hstep (1 / ((n : ℝ) + 2)) ((n : ℝ) + 1) hpos hlt
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at h
            convert h using 2
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, not_imp]
            tauto
          exact ENNReal.tsum_eq_zero.mpr hzero'
  have hset : {z : ℝ | ¬(z ∈ Set.Ioi 0 → f z = 0)} = {z : ℝ | 0 < z ∧ f z ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_imp]
  rw [hset]
  exact hbad

/-- **The first moment vanishes a.e.** -/
theorem M1_ae_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 :=
  ae_zero_of_intervalIntegral_zero
    (fun a b ha hab => intervalIntegrable_M1 hα hα4 h ha hab)
    (fun a b ha hab => intervalIntegral_M1_eq_zero hα hα4 h ha hab)

/-! ## The second moment -/

/-- **The primitive relation for the second moment**: for `0 < a < b`,
`M₁(b) - M₁(a) = ∫_a^b M₂`, where `M_j(z) = ∫_θ ∂_z^jΨ(z,θ) sinθcos²θ`. -/
theorem M2_relation {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ b θ * Work.Elliptic.sinCos2 θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ a θ * Work.Elliptic.sinCos2 θ)
        + ∫ s in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hbox : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz (Work.Spaces.pz Ψ) s θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
    intro a b ha hab
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero,
      Work.FTS.EllipticEst.sEta] using pzIter2_sigma_box α F Ψ hα h a b ha hab
  have hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.EllipticEst.WeakMoment.PzSliceIntegrable α F Ψ hα h z hz
  have hrel := Work.FTS.EllipticEst.moment_relation (fun z θ => Work.Spaces.pz Ψ z θ)
    (Work.FTS.EllipticEst.SmoothOpen.pz hΨ) hbox hsl ha hab
  simpa only [Work.Elliptic.Fstar, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hrel

/-- **`M₂` is locally integrable.**  The `η`-weighted box integrability of `∂_z²Ψ`
(conjunct 3 of `PzIter2SliceDom`), Fubini, and the domination
`|g sinθcos²θ| ≤ |g| sinθcos²θ` give the integrability of `s ↦ ∫_θ ∂_z²Ψ(s,θ) sinθcos²θ`. -/
theorem integrableOn_M2 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ)
      (Set.Icc a b) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- (i) the absolute-value integrand is jointly integrable on the box
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  have hle : (MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl
  have habs : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ => |Work.Spaces.pzIter 2 Ψ s θ|
        * Work.Elliptic.sinCos2 θ))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab
      (((hΨ.pzIter 2).continuousOn.abs).mul
        ((continuous_sinCos2.comp continuous_snd).continuousOn))
      (fun z _ θ hθ => mul_nonneg (abs_nonneg _) (sinCos2_nonneg_of_mem_Iθ hθ))
      (fun s hs => pzIter2_abs_slice α F Ψ h s (lt_of_lt_of_le ha hs.1))
      (pzIter2_abs_outer α F Ψ hα h ha hab)
  have hboxEq : ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  have habs' : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ => |Work.Spaces.pzIter 2 Ψ s θ|
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hboxEq]
    exact habs
  -- (ii) the signed integrand is jointly integrable: same norm, a.e. strongly measurable
  have hcont : ContinuousOn (Function.uncurry (fun s θ : ℝ => Work.Spaces.pzIter 2 Ψ s θ
      * Work.Elliptic.sinCos2 θ)) Work.FTS.EllipticEst.Q0 :=
    ((hΨ.pzIter 2).continuousOn.mul
      ((continuous_sinCos2.comp continuous_snd).continuousOn))
  have hsign : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pzIter 2 Ψ s θ
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine habs'.mono'
      ((Work.Spaces.aesm_of_continuousOn_Qd _ hcont).mono_measure hle) ?_
    have hmem : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p ∈ Set.Icc a b ×ˢ Work.Spaces.Iθ := by
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      exact MeasureTheory.self_mem_ae_restrict (measurableSet_Icc.prod measurableSet_Icc)
    filter_upwards [hmem] with p hp
    rw [Real.norm_eq_abs]
    change |(fun s θ : ℝ => Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ) p.1 p.2|
      ≤ (fun s θ : ℝ => |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) p.1 p.2
    exact le_of_eq (by rw [abs_mul, abs_of_nonneg (sinCos2_nonneg_of_mem_Iθ hp.2)])
  -- (iii) Fubini
  have hfin := hsign.integral_prod_left
  simpa only [MeasureTheory.IntegrableOn, Function.uncurry_apply_pair] using hfin

/-- **A primitive-constancy criterion.**  If `g` vanishes a.e. on `(z₀,∞)`, `f` is locally
integrable there and `∫_a^b f = g b - g a` for all `z₀ ≤ a < b`, then `f` vanishes a.e. on
`(z₀,∞)`: its primitive `Q(z) = ∫_{z₀}^z f` is a.e. equal to the constant `-g z₀`, hence (being
continuous) identically equal to it, so `f = Q' = 0` a.e. by the Lebesgue differentiation
theorem. -/
theorem ae_zero_of_primitive_const {f g : ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hint : ∀ a b : ℝ, z₀ ≤ a → a < b → IntervalIntegrable f MeasureTheory.volume a b)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi z₀)), g z = 0)
    (hrel : ∀ a b : ℝ, z₀ ≤ a → a < b → ∫ t in a..b, f t = g b - g a) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi z₀)), f z = 0 := by
  set Q : ℝ → ℝ := fun z => ∫ t in z₀..z, f t with hQ
  -- `Q` is constant on `[z₀,∞)`
  have hQconst : ∀ z : ℝ, z₀ ≤ z → Q z = -g z₀ := by
    intro z hz
    have hy : z₀ < max z (z₀ + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hzy : z ∈ Set.Icc z₀ (max z (z₀ + 1)) := ⟨hz, le_max_left _ _⟩
    have hIntv : MeasureTheory.IntegrableOn f (Set.Icc z₀ (max z (z₀ + 1))) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hy.le).mp (hint z₀ _ le_rfl hy)
    have hcont : ContinuousOn Q (Set.Icc z₀ (max z (z₀ + 1))) := by
      have h2 : Set.uIcc z₀ (max z (z₀ + 1)) = Set.Icc z₀ (max z (z₀ + 1)) :=
        Set.uIcc_of_le hy.le
      have h3 : MeasureTheory.IntegrableOn f (Set.uIcc z₀ (max z (z₀ + 1))) := by
        rw [h2]; exact hIntv
      simpa only [h2] using intervalIntegral.continuousOn_primitive_interval h3
    have hae' : Q =ᵐ[MeasureTheory.volume.restrict (Set.Icc z₀ (max z (z₀ + 1)))]
        (fun _ => -g z₀) := by
      have hg : ∀ᵐ w ∂(MeasureTheory.volume.restrict
          (Set.Icc z₀ (max z (z₀ + 1)))), g w = 0 := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hae
        have hne : ∀ᵐ w : ℝ, w ≠ z₀ := by rw [MeasureTheory.ae_iff]; simp
        filter_upwards [hae, hne] with w hw hwne hwmem
        exact hw (lt_of_le_of_ne hwmem.1 (Ne.symm hwne))
      filter_upwards [hg, MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with w hw hwmem
      rcases eq_or_lt_of_le hwmem.1 with h | h
      · rw [← h] at hw ⊢
        show ∫ t in z₀..z₀, f t = -g z₀
        rw [intervalIntegral.integral_same, hw]; ring
      · show ∫ t in z₀..w, f t = -g z₀
        rw [hrel z₀ w le_rfl h, hw]; ring
    have hEq := MeasureTheory.Measure.eqOn_of_ae_eq hae' hcont
      (continuousOn_const : ContinuousOn (fun _ : ℝ => -g z₀) _)
      (fun x hx => by
        rw [interior_Icc, closure_Ioo (ne_of_lt hy)]
        exact hx)
    exact hEq hzy
  -- the Lebesgue differentiation theorem identifies `f` with `Q'`
  have hstep : ∀ y : ℝ, z₀ < y →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc z₀ y)), f x = 0 := by
    intro y hy
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral (hint z₀ y le_rfl hy)
    rw [Set.uIcc_of_le hy.le] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have hne : ∀ᵐ x : ℝ, x ≠ z₀ := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hldt, hne] with x hx hxne hxmem
    have hxz : z₀ < x := lt_of_le_of_ne hxmem.1 (Ne.symm hxne)
    have hder : HasDerivAt Q (f x) x := hx hxmem z₀ ⟨le_rfl, hy.le⟩
    have hfun : (fun _ : ℝ => -g z₀) =ᶠ[𝓝 x] Q := by
      filter_upwards [isOpen_Ioi.mem_nhds hxz] with y' hy'
      exact (hQconst y' hy'.le).symm
    have hder0 : HasDerivAt (fun _ : ℝ => -g z₀) (f x) x :=
      hder.congr_of_eventuallyEq hfun
    exact hder0.unique (hasDerivAt_const x (-g z₀))
  -- cover `(z₀,∞)` by the intervals `[z₀, z₀+n+1]`
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  have hbad : MeasureTheory.volume {z : ℝ | z₀ < z ∧ f z ≠ 0} = 0 := by
    have hsub : {z : ℝ | z₀ < z ∧ f z ≠ 0} ⊆ ⋃ n : ℕ,
        ({z : ℝ | f z ≠ 0} ∩ Set.Icc z₀ (z₀ + (n : ℝ) + 1)) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_ge (z - z₀)
      exact Set.mem_iUnion.mpr ⟨n, hz.2, le_of_lt hz.1, by linarith⟩
    refine le_antisymm ?_ bot_le
    calc MeasureTheory.volume {z : ℝ | z₀ < z ∧ f z ≠ 0}
        ≤ MeasureTheory.volume (⋃ n : ℕ,
            ({z : ℝ | f z ≠ 0} ∩ Set.Icc z₀ (z₀ + (n : ℝ) + 1))) :=
          MeasureTheory.measure_mono hsub
      _ ≤ ∑' n : ℕ, MeasureTheory.volume ({z : ℝ | f z ≠ 0}
            ∩ Set.Icc z₀ (z₀ + (n : ℝ) + 1)) := MeasureTheory.measure_iUnion_le _
      _ = 0 := by
          refine ENNReal.tsum_eq_zero.mpr (fun n => ?_)
          have hy : z₀ < z₀ + (n : ℝ) + 1 := by
            have : (0 : ℝ) ≤ (n : ℝ) := by positivity
            linarith
          have h := hstep (z₀ + (n : ℝ) + 1) hy
          rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at h
          convert h using 2
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, not_imp]
          tauto
  have hset : {z : ℝ | ¬(z ∈ Set.Ioi z₀ → f z = 0)} = {z : ℝ | z₀ < z ∧ f z ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_imp]
  rw [hset]
  exact hbad

/-- **`M₂` vanishes a.e.** -/
theorem M2_ae_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hM1 := M1_ae_zero hα hα4 h
  -- the criterion on `(1/(n+2), ∞)` for every `n`
  have hkey : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Ioi (1 / ((n : ℝ) + 2)))),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 := by
    intro n
    have hz₀ : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    refine ae_zero_of_primitive_const
      (f := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      (g := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      (z₀ := 1 / ((n : ℝ) + 2)) hz₀ ?_ ?_ ?_
    · intro a b ha hab
      refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab.le]
      exact integrableOn_M2 hα hα4 h (lt_of_lt_of_le hz₀ ha) hab
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hM1 ⊢
      filter_upwards [hM1] with z hz hzmem
      exact hz (lt_trans hz₀ hzmem)
    · intro a b ha hab
      have hrel := M2_relation hα hα4 h (lt_of_lt_of_le hz₀ ha) hab
      have hbridge : (∫ t in a..b, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pzIter 2 Ψ t θ * Work.Elliptic.sinCos2 θ)
          = ∫ s in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ := by
        rw [intervalIntegral.integral_of_le hab.le]
        exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
      rw [hbridge]
      linarith
  -- cover `(0,∞)`
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  have hbad : MeasureTheory.volume {z : ℝ | 0 < z ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) ≠ 0} = 0 := by
    have hsub : {z : ℝ | 0 < z ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) ≠ 0}
        ⊆ ⋃ n : ℕ, {z : ℝ | (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) ≠ 0
            ∧ 1 / ((n : ℝ) + 2) < z} := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_ge (1 / z)
      refine Set.mem_iUnion.mpr ⟨n, hz.2, ?_⟩
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
      have : (1 : ℝ) / z ≤ (n : ℝ) := hn
      rw [div_le_iff₀ hz.1] at this
      nlinarith [hz.1, this]
    refine le_antisymm ?_ bot_le
    calc MeasureTheory.volume {z : ℝ | 0 < z ∧
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) ≠ 0}
        ≤ MeasureTheory.volume (⋃ n : ℕ, {z : ℝ | (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) ≠ 0
            ∧ 1 / ((n : ℝ) + 2) < z}) := MeasureTheory.measure_mono hsub
      _ ≤ ∑' n : ℕ, MeasureTheory.volume ({z : ℝ | (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) ≠ 0
            ∧ 1 / ((n : ℝ) + 2) < z}) := MeasureTheory.measure_iUnion_le _
      _ = 0 := by
          refine ENNReal.tsum_eq_zero.mpr (fun n => ?_)
          have h := hkey n
          rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff] at h
          convert h using 2
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_imp]
          constructor
          · rintro ⟨hne, hlt⟩; exact ⟨hlt, hne⟩
          · rintro ⟨hlt, hne⟩; exact ⟨hne, hlt⟩
  have hset : {z : ℝ | ¬(z ∈ Set.Ioi 0 → (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) = 0)}
      = {z : ℝ | 0 < z ∧ (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_imp]
  rw [hset]
  exact hbad

theorem momentChainZero (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) = 0) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmem : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), z ∈ Set.Ioi (0 : ℝ) :=
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi
  constructor
  · filter_upwards [M1_ae_zero hα hα4 h, hmem] with z hz hzpos
    exact ⟨Work.FTS.EllipticEst.WeakMoment.PzSliceIntegrable α F Ψ hα h z hzpos, hz⟩
  · filter_upwards [M2_ae_zero hα hα4 h, hmem] with z hz hzpos
    refine ⟨?_, hz⟩
    refine (pzIter2_abs_slice α F Ψ h z hzpos).mono'
      (aesm_mul_sinCos2
        (Work.FTS.EllipticEst.remov.ws_aesm_slice (hΨ.pzIter 2) hzpos)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact le_of_eq (by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_of_mem_Iθ hθ)])

end Work.FTS.EllipticEst.Mine.CutoffPieces
