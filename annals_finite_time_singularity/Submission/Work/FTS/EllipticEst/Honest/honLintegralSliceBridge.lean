import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## Helpers: the level-`0` slice and its `∫⁻`-form -/

/-- **The level-`0` `HkIntegrand` as a product on `Iθ`**, in the angular weight
`σ θ = AngSecond.sig θ = sin(2θ)^{-η}` used by the `∫⁻`-hypothesis `hC`. -/
theorem HkIntegrand_zero_eq_sig {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (g : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  rw [HkIntegrand_zero_eq, sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- **The bare `θ`-slice is integrable** as soon as the level-`0` `HkIntegrand` slice is:
the two differ by the non-zero constant factor `(w z)²` (`z > 0`). -/
theorem integrableOn_sq_sig_of_HkIntegrand_slice {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : 0 < z)
    (hslz : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  have hH : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) :=
    fun θ hθ => HkIntegrand_zero_eq_sig hθ g z
  have hIntprod : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2
        * ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
    hslz.congr_fun hH measurableSet_Icc
  have h1 := hIntprod.const_mul ((Work.Spaces.w z) ^ 2)⁻¹
  have h3 : (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * ((Work.Spaces.w z) ^ 2
          * ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)))
      = fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    funext θ
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (w_ne_zero hz)), one_mul]
  rwa [h3] at h1

/-- **The `∫⁻`-form of the level-`0` slice**, for `z > 0`: in terms of the angular weight
`σ = AngSecond.sig` the radial factor `(w z)²` comes out of both the Bochner integral and the
`ofReal`. -/
theorem ofReal_slice_HkIntegrand_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hslz : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iθ) :
    ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)) := by
  have hIntF : MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
    integrableOn_sq_sig_of_HkIntegrand_slice hz hslz
  have hofF : ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntF
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)))
  have hIntEq : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [MeasureTheory.setIntegral_congr_fun (μ := MeasureTheory.volume)
        (s := Work.Spaces.Iθ)
        (show MeasurableSet Work.Spaces.Iθ from by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
        (fun θ hθ => HkIntegrand_zero_eq_sig hθ g z),
      MeasureTheory.integral_const_mul]
  rw [hIntEq, ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z)), hofF]

/-- **The partial `θ`-integral of the level-`0` integrand is a.e. strongly measurable** in `z`,
as soon as the uncurried integrand is continuous on the open quadrant. -/
theorem aesm_partial_HkIntegrand_zero {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

/-- **The `∫⁻`-bound along the slices implies the `∫⁻`-bound of the `ofReal`-integral.** -/
theorem lintegral_le_ofReal_of_slice_eq {α : ℝ} {g : ℝ → ℝ → ℝ} {C : ℝ}
    (hsl : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
        Work.Spaces.Iθ)
    (hC : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)))
      ≤ ENNReal.ofReal C) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)) ≤ ENNReal.ofReal C := by
  have hslice_eq : ∀ z : ℝ, 0 < z → ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)) :=
    fun z hz => ofReal_slice_HkIntegrand_eq α g hz
      (hsl z (Set.mem_Ici.mpr (le_of_lt hz)))
  have hz_eq : (MeasureTheory.volume.restrict Work.Spaces.Iz)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [hz_eq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hae : (fun z => ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ))
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))) := by
    filter_upwards [hpos] with z hz
    exact le_of_eq (hslice_eq z hz)
  exact (MeasureTheory.lintegral_mono_ae hae).trans hC

/-- **The `∫⁻`-to-`HkMem`/`HkSq` bridge for the level-`0` norm.**

Suppose `g` is `C^∞` on the open quadrant, every `θ`-slice of its level-`0` `HkIntegrand` is
integrable on `Iθ` (`hsl`), and the *doubled* `∫⁻`-integral
`∫⁻_z (w z)² · ∫⁻_θ (g z θ)² σ θ` (`σ θ = sin(2θ)^{-η}`) is bounded by `ofReal C` with
`0 ≤ C`.  Then `g ∈ HkMem α 0` and `HkSq α 0 g ≤ C`.

Route.  The slice identity `HkIntegrand α 0 g z θ = (w z)² · (g z θ)² σ θ` holds on `Iθ` for
every `z` (`HkIntegrand_zero_eq` together with `sq_profile_eq`, both from
`Honest.Basic`: `HkIntegrand α 0 g z θ = (g z θ · (w z / sin(2θ)^{η/2}))²`), so
`ofReal (∫_θ HkIntegrand α 0 g z θ) ≤ ofReal ((w z)²) · ∫⁻_θ ofReal ((g z θ)² σ θ)`:
for `z = 0` both sides vanish (the factor `w 0 = 0`), and for `z > 0` this is the identity
`ofReal (∫_θ f) = ∫⁻_θ ofReal f` for the nonnegative integrable slice `f = (g z ·)² σ`
(`hsl` gives its integrability via the slice identity,
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`).  Hence
`∫⁻_z ofReal (∫_θ HkIntegrand α 0 g z θ) ≤ ofReal C < ⊤` by `lintegral_mono_ae`, and
`MeasureTheory.lintegral_ofReal_ne_top_iff_integrable` turns this into the second conjunct of
`HkMem α 0 g` (the first one is `hsl`); its AEMeasurability input is
`AEStronglyMeasurable.integral_prod_right'` applied to the joint a.e. strong measurability of
the uncurried integrand, which follows from its continuity on the open quadrant
(`hsm 0` for `g`, continuity of the weights there) and `Work.Spaces.aesm_of_continuousOn_Qd`.
Finally `HkSq_eq_lintegral` identifies `HkSq α 0 g` with the `toReal` of that outer
`∫⁻`-integral, and `ENNReal.toReal_mono (ENNReal.ofReal_ne_top _)`
together with `ENNReal.toReal_ofReal hC0` gives `HkSq α 0 g ≤ C`. -/
theorem honLintegralSliceBridge {α : ℝ} {g : ℝ → ℝ → ℝ} {C : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsl : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
        Work.Spaces.Iθ)
    (hC : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)))
      ≤ ENNReal.ofReal C)
    (hC0 : 0 ≤ C) :
    Work.Spaces.HkMem α 0 g ∧ Work.Spaces.HkSq α 0 g ≤ C := by
  -- The uncurried level-`0` integrand is continuous on the open quadrant.
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall hsm).continuousOn_HkIntegrand α 0
  -- Hence its partial `θ`-integral is a.e. strongly measurable in `z`.
  have haesm_par := aesm_partial_HkIntegrand_zero (α := α) (g := g) hcont
  -- The outer `∫⁻`-integral is bounded by `ofReal C`.
  have hbound : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)) ≤ ENNReal.ofReal C :=
    lintegral_le_ofReal_of_slice_eq (α := α) (g := g) (C := C) hsl hC
  -- Honesty of the partial `θ`-integral in `z`.
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) :=
    Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ => HkIntegrand_nonneg α 0 g z θ
  have hIntZ : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iz :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm_par hnn).mp
      (ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top))
  refine ⟨⟨hsl, hIntZ⟩, ?_⟩
  rw [Work.FTS.EllipticEst.HkSq_eq_lintegral α 0 g hsm]
  calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)).toReal
      ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = C := ENNReal.toReal_ofReal hC0

end Work.FTS.EllipticEst.Honest
