import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3LocReduction
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.H2W.integralAbsLeSqrtMulSqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/SliceB/pzSecGrowthLoc` — the locally uniform pole bound from the *honest second-derivative
slots*

Target of the node `Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3Loc`: for a datum
`WeakPos2 α F Ψ` (`0 < α ≤ 1/4`) and for almost every `z₀ > 0` there are `ε ∈ (0, z₀)` and a
*single* `C ≥ 0` with

  `|D_z^j Ψ(z,θ)| ≤ C·(θ⁻¹ + (π/2-θ)⁻¹)`   for all `j ≤ 3`, `z ∈ (z₀-ε, z₀+ε)`,
  `θ ∈ (0,π/2)`.

This file proves a **second, independent reduction** of that target, resting on the *honest slot*
of the paper's class rather than on the source-mass bound
(`H2W/pzIterSliceGrowth3LocReduction.lean`):

> if the *second angular derivative* of each of the four slices `D_z^mΨ` (`m ≤ 3`) is bounded in
> the `sin(2θ)^{-η}`-weighted `L²`-sense, **locally uniformly in `z`** (`LocSecBound Ψ` below),
> then the target holds.

Two remarks on the shape of the hypothesis.

* The class `WeakPos2` supplies `HkMem α 2 F` for the *source* only; the *left-hand side* slots
  (`∂_θθΦ`, `z²∂_zzΦ`) are not required to be honest.  Adding their honesty is exactly the
  strengthening recommended in `H2W/WeakPureAux/NOTES_weakPzPoleBound.md` §5.
* The **local uniformity** is the essential part of the shape of the hypothesis, and it is *not
  automatic*: Fatou only gives that `z ↦ ∫_θ (∂_θθ(u)(z,·))² σ` is *lower* semicontinuous, and a
  lower semicontinuous function that is finite a.e. need not be locally bounded a.e.
  (The joint — `HkMem`-style — honesty of a slot gives exactly the a.e. finiteness of this
  function, so the *naive* route from a joint honesty hypothesis to the uniform conclusion fails.
  Whether the extra smoothness of the present situation forces local boundedness anyway is
  **not known**; see §2 of `NOTES_pzSecGrowthLoc.md` beside this file, where the natural
  "concentrating spike" constructions are examined and blocked by smoothness.  The locally
  uniform form below is the hypothesis the proof here actually consumes.)

## The mathematics (elementary, and *quantitative*)

For a single slice `u = D_z^mΨ(z,·)` the second-derivative control gives boundedness with an
**explicit constant**.  Writing `B := |u'(π/4)| + ∫_{Iθ}|u''|`, the fundamental theorem of
calculus on `(π/4, θ)` gives `|u'(θ)| ≤ B` and `|u(θ)| ≤ |u(π/4)| + B·(π/2)`; and since
`σ = sin(2θ)^{-η} ≥ 1` on `(0,π/2)`, Cauchy–Schwarz (`H2W.integralAbsLeSqrtMulSqrt`) gives

  `∫_{Iθ}|u''| ≤ √(∫_{Iθ}(u'')²σ)·√(π/2) ≤ K + π/2`  whenever `∫_{Iθ}(u'')²σ ≤ K`.

Hence `|u(θ)| ≤ U + (π/2)·(U + K + π/2)`, where `U` bounds the data
`|u(π/4)| + |u'(π/4)|`.  The data term is *continuous in `z`* (hence locally bounded —
`H2W.exists_sliceData_bound_single`) and `K` is bounded on the `z`-neighbourhood by hypothesis,
so a *single* constant works on `(z₀-ε, z₀+ε)`, which is the target.  This is the same pattern as
the source-mass reduction: the qualitative sibling `Honest.slice_bdd_of_sq_mul_sEta` (an `∃ C`)
is replaced here by a *quantitative* form, which is what makes the constant uniform in `z`. -/

namespace Work.FTS.EllipticEst.H2W.SliceB

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Facts about `sEta` on the open interval -/

theorem sEta_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.FTS.EllipticEst.sEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact Real.rpow_pos_of_pos hpos (-(Work.Spaces.eta))

/-- `1 ≤ sEta θ` on the open interval: `sin(2θ) ∈ (0,1]` and `sEta = sin(2θ)^{-η}`. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : 0 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hpow : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 := Real.rpow_le_one hpos.le hle hη
  have hpowpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hpos _
  rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hpos.le]
  exact (one_le_inv₀ hpowpos).mpr hpow

/-- The restriction of `volume` to `Iθ` agrees with the restriction to the open interval. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc

/-- Almost every point of `Iθ` lies in the open interval: the two endpoints are null. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The set integral over `Iθ` is the interval integral over `[0, π/2]`. -/
theorem integral_Iθ_eq_intervalIntegral (h : ℝ → ℝ) :
    (∫ x in Work.Spaces.Iθ, h x) = ∫ x in (0 : ℝ)..(Real.pi / 2), h x := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-! ## The quantitative slice bound from the honest second-derivative slot -/

/-- **The quantitative slice bound.**  If `u` is `C²` on `(0,π/2)`, `∫_{Iθ}(u'')²σ ≤ K` and the
data at `π/4` satisfies `|u(π/4)| + |u'(π/4)| ≤ U`, then

  `|u θ| ≤ U + (π/2)·(U + K + π/2)`   for all `θ ∈ (0,π/2)`.

The constant is *explicit*, which is what makes it uniform in a `z`-neighbourhood. -/
theorem slice_abs_le_of_secSq {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {K U : ℝ} (hU : 0 ≤ U)
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hbound : (∫ θ in Work.Spaces.Iθ, (deriv (fun t : ℝ => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) ≤ K)
    (hdata : |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| ≤ U) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ U + (Real.pi / 2) * (U + (K + Real.pi / 2)) := by
  have hpi4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hpipos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont2 : ContinuousOn (fun θ : ℝ => deriv (fun t : ℝ => deriv u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 : ContDiffOn ℝ 0 (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h2.continuousOn
  have hmeasIoo : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hf_meas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => deriv (fun t : ℝ => deriv u t) θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hcont2.aestronglyMeasurable hmeasIoo
  -- the pointwise domination of `(u'')²` by `(u'')²σ`, a.e. on `Iθ` (`σ ≥ 1` on the interior)
  have hae_le : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (deriv (fun t : ℝ => deriv u t) θ) ^ 2
        ≤ (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    ae_mem_Ioo_Iθ.mono fun θ hθ => by
      have h1 := one_le_sEta hθ
      nlinarith [sq_nonneg (deriv (fun t : ℝ => deriv u t) θ)]
  -- integrability of `(u'')²` from the `σ`-weighted one
  have hsq_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hint (hf_meas.pow 2)
      (hae_le.mono fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hθ)
  have hsq_bnd : (∫ θ in Work.Spaces.Iθ, (deriv (fun t : ℝ => deriv u t) θ) ^ 2) ≤ K :=
    le_trans (MeasureTheory.integral_mono_ae hsq_int hint hae_le) hbound
  have hK0 : 0 ≤ K := le_trans (integral_nonneg fun θ => sq_nonneg _) hsq_bnd
  -- `∫|u''| ≤ K + π/2`
  have habs_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hcont2 hint
  have hIocsub : Set.Ioc (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact Set.Ioc_subset_Icc_self
  have hf_meas_Ioc : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => deriv (fun t : ℝ => deriv u t) θ)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2))) := by
    rw [← MeasureTheory.Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
      (s := Set.Ioc (0 : ℝ) (Real.pi / 2)) (t := Work.Spaces.Iθ) hIocsub]
    exact hf_meas.restrict
  have hf_Ioc : MeasureTheory.IntegrableOn
      (fun θ : ℝ => deriv (fun t : ℝ => deriv u t) θ) (Set.Ioc (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' (habs_int.mono_set hIocsub) hf_meas_Ioc
      (Filter.Eventually.of_forall fun x => le_of_eq (Real.norm_eq_abs (deriv (fun t : ℝ => deriv u t) x)))
  have hf2_Ioc : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      (Set.Ioc (0 : ℝ) (Real.pi / 2)) := hsq_int.mono_set hIocsub
  have hf_int : IntervalIntegrable
      (fun θ : ℝ => deriv (fun t : ℝ => deriv u t) θ) MeasureTheory.volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpipos.le).mpr hf_Ioc
  have hf2_int : IntervalIntegrable
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpipos.le).mpr hf2_Ioc
  have hCS := Work.FTS.EllipticEst.H2W.integralAbsLeSqrtMulSqrt (a := 0) (b := Real.pi / 2)
    hpipos hf_int hf2_int
  have hconv1 := integral_Iθ_eq_intervalIntegral (fun θ => |deriv (fun t : ℝ => deriv u t) θ|)
  have hconv2 := integral_Iθ_eq_intervalIntegral
    (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
  have hInt_abs : (∫ θ in Work.Spaces.Iθ, |deriv (fun t : ℝ => deriv u t) θ|)
      ≤ Real.sqrt (K * (Real.pi / 2)) := by
    rw [hconv1]
    calc (∫ x in (0 : ℝ)..(Real.pi / 2), |deriv (fun t : ℝ => deriv u t) x|)
        ≤ Real.sqrt (Real.pi / 2 - 0)
            * Real.sqrt (∫ x in (0 : ℝ)..(Real.pi / 2), (deriv (fun t : ℝ => deriv u t) x) ^ 2) :=
          hCS
      _ = Real.sqrt (Real.pi / 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (fun t : ℝ => deriv u t) θ) ^ 2) := by
          rw [sub_zero, hconv2]
      _ ≤ Real.sqrt (Real.pi / 2) * Real.sqrt K :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq_bnd) (Real.sqrt_nonneg _)
      _ = Real.sqrt (K * (Real.pi / 2)) := by
          rw [Real.sqrt_mul hK0, mul_comm]
  have hsqrt_le : Real.sqrt (K * (Real.pi / 2)) ≤ K + Real.pi / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith [hK0, Real.pi_pos], by nlinarith [hK0, Real.pi_pos]⟩
  have hIi : IntervalIntegrable
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|) MeasureTheory.volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
    exact habs_int.mono_set Set.Ioc_subset_Icc_self
  -- the bound `B` on `u'`
  set B : ℝ := |deriv u (Real.pi / 4)|
    + ∫ t in Work.Spaces.Iθ, |deriv (fun s : ℝ => deriv u s) t| with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h := integral_nonneg (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun t : ℝ => |deriv (fun s : ℝ => deriv u s) t|) (fun t => abs_nonneg _)
    linarith [abs_nonneg (deriv u (Real.pi / 4))]
  have hBle : B ≤ U + (K + Real.pi / 2) := by
    rw [hBdef]
    have h1 : |deriv u (Real.pi / 4)| ≤ U := by linarith [abs_nonneg (u (Real.pi / 4)), hdata]
    linarith [hInt_abs, hsqrt_le]
  have hseg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  have hpthle : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u θ| ≤ B := by
    intro θ hθ
    have hc1 : ContDiffOn ℝ 1 (fun t : ℝ => deriv u t) (Set.uIcc (Real.pi / 4) θ) :=
      (hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)).mono (hseg θ hθ)
    have hFTC : (∫ t in (Real.pi / 4)..θ, deriv (fun t : ℝ => deriv u t) t)
        = deriv u θ - deriv u (Real.pi / 4) :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc hc1
    have hval : deriv u θ = deriv u (Real.pi / 4)
        + ∫ t in (Real.pi / 4)..θ, deriv (fun t : ℝ => deriv u t) t := by
      linarith [hFTC]
    calc |deriv u θ|
        = |deriv u (Real.pi / 4)
            + ∫ t in (Real.pi / 4)..θ, deriv (fun t : ℝ => deriv u t) t| := by rw [hval]
      _ ≤ |deriv u (Real.pi / 4)|
            + |∫ t in (Real.pi / 4)..θ, deriv (fun t : ℝ => deriv u t) t| := abs_add_le _ _
      _ ≤ |deriv u (Real.pi / 4)|
            + ∫ t in Work.Spaces.Iθ, |deriv (fun t : ℝ => deriv u t) t| := by
          have := Work.FTS.EllipticEst.Honest.abs_intervalIntegral_le_setIntegral_Iθ
            (f := fun t => deriv (fun s : ℝ => deriv u s) t) hpi4 hθ hIi
          linarith
      _ = B := by rw [hBdef]
  intro θ hθ
  have hc0 : ContDiffOn ℝ 1 u (Set.uIcc (Real.pi / 4) θ) :=
    (hsm.of_le (by norm_num)).mono (hseg θ hθ)
  have hFTC : (∫ t in (Real.pi / 4)..θ, deriv u t) = u θ - u (Real.pi / 4) :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc hc0
  have hval : u θ = u (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, deriv u t := by
    linarith [hFTC]
  have hstep : |∫ t in (Real.pi / 4)..θ, deriv u t| ≤ B * (Real.pi / 2) := by
    have hbnd : ∀ x ∈ Set.uIoc (Real.pi / 4) θ, ‖deriv u x‖ ≤ B := by
      intro x hx
      rw [Set.mem_uIoc] at hx
      rw [Real.norm_eq_abs]
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hpthle x ⟨lt_of_lt_of_le hpi4.1 (le_of_lt h1), lt_of_le_of_lt h2 hθ.2⟩
      · exact hpthle x ⟨lt_of_lt_of_le hθ.1 (le_of_lt h1), lt_of_le_of_lt h2 hpi4.2⟩
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rw [Real.norm_eq_abs] at h
    have hlen : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hθ.2, Real.pi_pos], by linarith [hθ.1, Real.pi_pos]⟩
    calc |∫ t in (Real.pi / 4)..θ, deriv u t| ≤ B * |θ - Real.pi / 4| := h
      _ ≤ B * (Real.pi / 2) := mul_le_mul_of_nonneg_left hlen hB0
  have h1 : |u (Real.pi / 4)| ≤ U := by
    linarith [abs_nonneg (deriv u (Real.pi / 4)), hdata]
  calc |u θ| = |u (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, deriv u t| := by rw [hval]
    _ ≤ |u (Real.pi / 4)| + |∫ t in (Real.pi / 4)..θ, deriv u t| := abs_add_le _ _
    _ ≤ U + B * (Real.pi / 2) := by linarith [hstep]
    _ ≤ U + (U + (K + Real.pi / 2)) * (Real.pi / 2) := by
        have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have hm := mul_le_mul_of_nonneg_right hBle hpi
        linarith
    _ = U + (Real.pi / 2) * (U + (K + Real.pi / 2)) := by ring

/-! ## The hypothesis, and the reduction of the target -/

/-- **The locally uniform honest second-derivative slot.**  For a.e. centre `z₀ > 0` there is a
neighbourhood on which, with a *single* constant `C`, the second angular derivative of each of the
four slices `D_z^mΨ` (`m ≤ 3`) is integrable against the weight `sin(2θ)^{-η}` with *integrated*
bound `C`.

This is the *locally uniform* form of the honest left-hand-side slot recommended in
`H2W/WeakPureAux/NOTES_weakPzPoleBound.md` §5; the local uniformity is not implied by the joint
(`HkMem`-style) honesty (see the module docstring). -/
def LocSecBound (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
    ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
        MeasureTheory.IntegrableOn
            (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.pzIter m Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ
          ∧ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pzIter m Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) ≤ C

/-- **The reduction of `pzIterSliceGrowth3Loc` to the locally uniform honest second-derivative
slot.**  For a datum of the weak class and a locally uniform `sin(2θ)^{-η}`-weighted `L²`-bound on
the second angular derivatives of the four slices `D_z^mΨ` (`m ≤ 3`), the locally uniform pole
bound follows, with the *explicit* constant `U + (π/2)·(U + C + π/2)` built from the data bound
`U` on `[z₀-ε, z₀+ε]` and the slot bound `C` (`slice_abs_le_of_secSq`). -/
theorem pzIterSliceGrowth3Loc_of_locSecBound {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) (hs : LocSecBound Ψ) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.Spaces.pzIter j Ψ z θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  have hsm_raw : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.2.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm_raw
  filter_upwards [hs, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z₀ hs₀ _hz₀
  obtain ⟨ε, hεpos, hεz, K, hK0, hbound⟩ := hs₀
  have ha : 0 < z₀ - ε := by linarith
  have hab : z₀ - ε ≤ z₀ + ε := by linarith
  obtain ⟨M0, hM0, hbd0⟩ :=
    Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε)
      ha hab 0
  obtain ⟨M1, hM1, hbd1⟩ :=
    Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε)
      ha hab 1
  obtain ⟨M2, hM2, hbd2⟩ :=
    Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε)
      ha hab 2
  obtain ⟨M3, hM3, hbd3⟩ :=
    Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε)
      ha hab 3
  set U : ℝ := max (max M0 M1) (max M2 M3) with hUdef
  have hM0U : M0 ≤ U := by
    rw [hUdef]
    exact le_trans (le_max_left M0 M1) (le_max_left (max M0 M1) (max M2 M3))
  have hM1U : M1 ≤ U := by
    rw [hUdef]
    exact le_trans (le_max_right M0 M1) (le_max_left (max M0 M1) (max M2 M3))
  have hM2U : M2 ≤ U := by
    rw [hUdef]
    exact le_trans (le_max_left M2 M3) (le_max_right (max M0 M1) (max M2 M3))
  have hM3U : M3 ≤ U := by
    rw [hUdef]
    exact le_trans (le_max_right M2 M3) (le_max_right (max M0 M1) (max M2 M3))
  have hU0 : 0 ≤ U := le_trans hM0 hM0U
  have hMd : ∀ z ∈ Set.Icc (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
      |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
        + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)| ≤ U := by
    intro z hz m hm
    interval_cases m
    · exact le_trans (hbd0 z hz) hM0U
    · exact le_trans (hbd1 z hz) hM1U
    · exact le_trans (hbd2 z hz) hM2U
    · exact le_trans (hbd3 z hz) hM3U
  refine ⟨ε, hεpos, hεz, U + (Real.pi / 2) * (U + (K + Real.pi / 2)), ?_, ?_⟩
  · have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
    nlinarith [hU0, hK0, hpi]
  intro j hj z hz θ hθ
  have hzpos : 0 < z := by linarith [hz.1, hεz]
  have hzmem : z ∈ Set.Icc (z₀ - ε) (z₀ + ε) := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  obtain ⟨hint, hbnd⟩ := hbound z hz j hj
  have hsmj : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.H2W.contDiffOn_slice_pzIter hsm_raw hzpos j 2
  have hbnd' : (∫ θ' in Work.Spaces.Iθ,
      (deriv (fun t : ℝ => deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') t) θ') ^ 2
        * Work.FTS.EllipticEst.sEta θ') ≤ K := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hbnd
  have hint' : MeasureTheory.IntegrableOn
      (fun θ' : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') t) θ') ^ 2
        * Work.FTS.EllipticEst.sEta θ') Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hint
  have hdata : |Work.Spaces.pzIter j Ψ z (Real.pi / 4)|
      + |deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') (Real.pi / 4)| ≤ U := by
    simpa only [Work.Spaces.pth] using hMd z hzmem j hj
  have hslice := slice_abs_le_of_secSq hsmj (K := K) (U := U) hU0 hint' hbnd' hdata θ hθ
  have hρ : 1 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := by
    have h1 : 2 / Real.pi ≤ θ⁻¹ := by
      have h := one_div_le_one_div_of_le hθ.1 (le_of_lt hθ.2)
      have e : (2 : ℝ) / Real.pi = 1 / (Real.pi / 2) := by ring
      rw [e]
      simpa only [one_div] using h
    have h2 : 2 / Real.pi ≤ (Real.pi / 2 - θ)⁻¹ := by
      have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      have hab : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
      have h := one_div_le_one_div_of_le hpos hab
      have e : (2 : ℝ) / Real.pi = 1 / (Real.pi / 2) := by ring
      rw [e]
      simpa only [one_div] using h
    have hπ : (1 : ℝ) < 4 / Real.pi := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
      linarith [Real.pi_lt_four]
    have hsum : 4 / Real.pi ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := by
      have h := add_le_add h1 h2
      have e : 2 / Real.pi + 2 / Real.pi = 4 / Real.pi := by ring
      linarith [h, e]
    linarith [hsum, hπ]
  calc |Work.Spaces.pzIter j Ψ z θ|
      ≤ U + (Real.pi / 2) * (U + (K + Real.pi / 2)) := hslice
    _ = (U + (Real.pi / 2) * (U + (K + Real.pi / 2))) * 1 := by ring
    _ ≤ (U + (Real.pi / 2) * (U + (K + Real.pi / 2))) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_left hρ (by positivity)

/-! ## The same conclusion from the *first*-derivative slot (a strictly weaker hypothesis)

The second-derivative slot above is the paper's honest slot.  It can be weakened: the fundamental
theorem of calculus anchored at the interior point `π/4` gives `|u θ| ≤ |u(π/4)| + ∫_{Iθ}|u'|`,
and Cauchy–Schwarz bounds `∫_{Iθ}|u'|` by `√(∫_{Iθ}(u')²σ)·√(π/2)`.  So the *first* angular
derivative, in the same `σ`-weighted `L²`-sense, already suffices — and `|u(π/4)|` is part of the
locally bounded data term. -/

/-- **The quantitative slice bound from the honest first-derivative slot.** -/
theorem slice_abs_le_of_gradSq {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    {K : ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hbound : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) ≤ K) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ |u (Real.pi / 4)| + Real.sqrt (K * (Real.pi / 2)) := by
  have hpi4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hpipos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont1 : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)).continuousOn
  have hf_meas : MeasureTheory.AEStronglyMeasurable (deriv u)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hcont1.aestronglyMeasurable measurableSet_Ioo
  have hae_le : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (deriv u θ) ^ 2 ≤ (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    ae_mem_Ioo_Iθ.mono fun θ hθ => by
      have h1 := one_le_sEta hθ
      nlinarith [sq_nonneg (deriv u θ)]
  have hsq_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv u θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hint (hf_meas.pow 2)
      (hae_le.mono fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hθ)
  have hsq_bnd : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) ≤ K :=
    le_trans (MeasureTheory.integral_mono_ae hsq_int hint hae_le) hbound
  have hK0 : 0 ≤ K := le_trans (integral_nonneg fun θ => sq_nonneg _) hsq_bnd
  have habs_le_sq_add_one : ∀ x : ℝ, |x| ≤ x ^ 2 + 1 := by
    intro x
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]
  have habs_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv u θ|) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (hsq_int.add (MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)))
      ?_ (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs, abs_abs]
        exact habs_le_sq_add_one (deriv u θ))
    rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hcont1.abs.aestronglyMeasurable measurableSet_Ioo
  have hIocsub : Set.Ioc (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact Set.Ioc_subset_Icc_self
  have hf_meas_Ioc : MeasureTheory.AEStronglyMeasurable (deriv u)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2))) := by
    rw [← MeasureTheory.Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
      (s := Set.Ioc (0 : ℝ) (Real.pi / 2)) (t := Work.Spaces.Iθ) hIocsub]
    exact hf_meas.restrict
  have hf_Ioc : MeasureTheory.IntegrableOn (deriv u) (Set.Ioc (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' (habs_int.mono_set hIocsub) hf_meas_Ioc
      (Filter.Eventually.of_forall fun x => le_of_eq (Real.norm_eq_abs (deriv u x)))
  have hf2_Ioc : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2)
      (Set.Ioc (0 : ℝ) (Real.pi / 2)) := hsq_int.mono_set hIocsub
  have hf_int : IntervalIntegrable (deriv u) MeasureTheory.volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpipos.le).mpr hf_Ioc
  have hf2_int : IntervalIntegrable (fun θ : ℝ => (deriv u θ) ^ 2)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpipos.le).mpr hf2_Ioc
  have hCS := Work.FTS.EllipticEst.H2W.integralAbsLeSqrtMulSqrt (a := 0) (b := Real.pi / 2)
    hpipos hf_int hf2_int
  have hconv1 := integral_Iθ_eq_intervalIntegral (fun θ => |deriv u θ|)
  have hconv2 := integral_Iθ_eq_intervalIntegral (fun θ => (deriv u θ) ^ 2)
  have hInt_abs : (∫ θ in Work.Spaces.Iθ, |deriv u θ|) ≤ Real.sqrt (K * (Real.pi / 2)) := by
    rw [hconv1]
    calc (∫ x in (0 : ℝ)..(Real.pi / 2), |deriv u x|)
        ≤ Real.sqrt (Real.pi / 2 - 0)
            * Real.sqrt (∫ x in (0 : ℝ)..(Real.pi / 2), (deriv u x) ^ 2) := hCS
      _ = Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) := by
          rw [sub_zero, hconv2]
      _ ≤ Real.sqrt (Real.pi / 2) * Real.sqrt K :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq_bnd) (Real.sqrt_nonneg _)
      _ = Real.sqrt (K * (Real.pi / 2)) := by
          rw [Real.sqrt_mul hK0, mul_comm]
  have hIi : IntervalIntegrable (fun θ : ℝ => |deriv u θ|) MeasureTheory.volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
    exact habs_int.mono_set Set.Ioc_subset_Icc_self
  intro θ hθ
  have hseg : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  have hc0 : ContDiffOn ℝ 1 u (Set.uIcc (Real.pi / 4) θ) := hsm.mono hseg
  have hFTC : (∫ t in (Real.pi / 4)..θ, deriv u t) = u θ - u (Real.pi / 4) :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc hc0
  have hval : u θ = u (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, deriv u t := by
    linarith [hFTC]
  calc |u θ| = |u (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, deriv u t| := by rw [hval]
    _ ≤ |u (Real.pi / 4)| + |∫ t in (Real.pi / 4)..θ, deriv u t| := abs_add_le _ _
    _ ≤ |u (Real.pi / 4)| + ∫ t in Work.Spaces.Iθ, |deriv u t| := by
        have := Work.FTS.EllipticEst.Honest.abs_intervalIntegral_le_setIntegral_Iθ
          (f := fun t => deriv u t) hpi4 hθ hIi
        linarith
    _ ≤ |u (Real.pi / 4)| + Real.sqrt (K * (Real.pi / 2)) := by linarith [hInt_abs]

/-- **The locally uniform honest *first*-derivative slot.**  Same shape as `LocSecBound`, but the
slot is `∂_θ (D_z^mΨ)` (`m ≤ 3`) rather than `∂_θθ (D_z^mΨ)`; `slice_abs_le_of_gradSq` consumes it
in place of `slice_abs_le_of_secSq`, so this is a *weaker* hypothesis for the same conclusion. -/
def LocGradBound (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
    ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
        MeasureTheory.IntegrableOn
            (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ
          ∧ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) ≤ C

/-- **The reduction of `pzIterSliceGrowth3Loc` to the locally uniform honest first-derivative
slot.**  Same conclusion as `pzIterSliceGrowth3Loc_of_locSecBound`, with the weaker hypothesis
`LocGradBound Ψ`: the constant is `U + √(C·(π/2))`, where `U` bounds the data
`|D_z^mΨ(z,π/4)|` on the neighbourhood and `C` the slot. -/
theorem pzIterSliceGrowth3Loc_of_locGradBound {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) (hs : LocGradBound Ψ) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.Spaces.pzIter j Ψ z θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  have hsm_raw : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.2.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm_raw
  filter_upwards [hs, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z₀ hs₀ _hz₀
  obtain ⟨ε, hεpos, hεz, K, hK0, hbound⟩ := hs₀
  have ha : 0 < z₀ - ε := by linarith
  have hab : z₀ - ε ≤ z₀ + ε := by linarith
  obtain ⟨M0, hM0, hbd0⟩ :=
    Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε)
      ha hab 0
  obtain ⟨M1, hM1, hbd1⟩ :=
    Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε)
      ha hab 1
  obtain ⟨M2, hM2, hbd2⟩ :=
    Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε)
      ha hab 2
  obtain ⟨M3, hM3, hbd3⟩ :=
    Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε)
      ha hab 3
  set U : ℝ := max (max M0 M1) (max M2 M3) with hUdef
  have hM0U : M0 ≤ U := by
    rw [hUdef]
    exact le_trans (le_max_left M0 M1) (le_max_left (max M0 M1) (max M2 M3))
  have hM1U : M1 ≤ U := by
    rw [hUdef]
    exact le_trans (le_max_right M0 M1) (le_max_left (max M0 M1) (max M2 M3))
  have hM2U : M2 ≤ U := by
    rw [hUdef]
    exact le_trans (le_max_left M2 M3) (le_max_right (max M0 M1) (max M2 M3))
  have hM3U : M3 ≤ U := by
    rw [hUdef]
    exact le_trans (le_max_right M2 M3) (le_max_right (max M0 M1) (max M2 M3))
  have hU0 : 0 ≤ U := le_trans hM0 hM0U
  have hMd : ∀ z ∈ Set.Icc (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
      |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
        + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)| ≤ U := by
    intro z hz m hm
    interval_cases m
    · exact le_trans (hbd0 z hz) hM0U
    · exact le_trans (hbd1 z hz) hM1U
    · exact le_trans (hbd2 z hz) hM2U
    · exact le_trans (hbd3 z hz) hM3U
  refine ⟨ε, hεpos, hεz, U + Real.sqrt (K * (Real.pi / 2)), ?_, ?_⟩
  · have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
    have : 0 ≤ K * (Real.pi / 2) := mul_nonneg hK0 hpi.le
    linarith [Real.sqrt_nonneg (K * (Real.pi / 2))]
  intro j hj z hz θ hθ
  obtain ⟨hint, hbnd⟩ := hbound z hz j hj
  have hsmj : ContDiffOn ℝ 1 (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.H2W.contDiffOn_slice_pzIter hsm_raw (by linarith [hz.1, hεz]) j 1
  have hbnd' : (∫ θ' in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') θ') ^ 2
        * Work.FTS.EllipticEst.sEta θ') ≤ K := by
    simpa only [Work.Spaces.pth] using hbnd
  have hint' : MeasureTheory.IntegrableOn
      (fun θ' : ℝ => (deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') θ') ^ 2
        * Work.FTS.EllipticEst.sEta θ') Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pth] using hint
  have hdata : |Work.Spaces.pzIter j Ψ z (Real.pi / 4)| ≤ U := by
    have h1 := hMd z ⟨le_of_lt hz.1, le_of_lt hz.2⟩ j hj
    linarith [abs_nonneg (Work.Spaces.pth (Work.Spaces.pzIter j Ψ) z (Real.pi / 4))]
  have hslice := slice_abs_le_of_gradSq hsmj (K := K) hint' hbnd' θ hθ
  have hρ : 1 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := by
    have h1 : 2 / Real.pi ≤ θ⁻¹ := by
      have h := one_div_le_one_div_of_le hθ.1 (le_of_lt hθ.2)
      have e : (2 : ℝ) / Real.pi = 1 / (Real.pi / 2) := by ring
      rw [e]
      simpa only [one_div] using h
    have h2 : 2 / Real.pi ≤ (Real.pi / 2 - θ)⁻¹ := by
      have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      have hab2 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
      have h := one_div_le_one_div_of_le hpos hab2
      have e : (2 : ℝ) / Real.pi = 1 / (Real.pi / 2) := by ring
      rw [e]
      simpa only [one_div] using h
    have hπ : (1 : ℝ) < 4 / Real.pi := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
      linarith [Real.pi_lt_four]
    have hsum : 4 / Real.pi ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := by
      have h := add_le_add h1 h2
      have e : 2 / Real.pi + 2 / Real.pi = 4 / Real.pi := by ring
      linarith [h, e]
    linarith [hsum, hπ]
  calc |Work.Spaces.pzIter j Ψ z θ|
      ≤ |Work.Spaces.pzIter j Ψ z (Real.pi / 4)| + Real.sqrt (K * (Real.pi / 2)) := hslice
    _ ≤ U + Real.sqrt (K * (Real.pi / 2)) := by linarith [hdata]
    _ = (U + Real.sqrt (K * (Real.pi / 2))) * 1 := by ring
    _ ≤ (U + Real.sqrt (K * (Real.pi / 2))) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_left hρ (by positivity)

end

end Work.FTS.EllipticEst.H2W.SliceB
