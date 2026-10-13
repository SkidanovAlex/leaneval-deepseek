/-
Copyright: work module for the Elgindi finite-time singularity project.

# Continuity of the mode coefficients `cmode m F` on `(0,∞)`

`Work.FTS.PhiStar.Series.cmode m F z` is the `e_m`-coefficient of the angular slice `F z ·`
in the self-adjoint weight `cos θ dθ`:

  `cmode m F z = (∫_θ F z θ · e_m θ · cos θ) / (∫_θ e_m θ² cos θ)`,

and the aim of this file is `Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one`: the
continuity of `z ↦ cmode m F z` on `(0,∞)` from the *open-quadrant* smoothness `SmoothOpen F`
and the honest weighted first-order membership `HkMem α 1 F`.

**Why this is not immediate.**  `SmoothOpen F` only controls `F` on the *open* quadrant, so no
uniform domination of the angular slices is available; and `HkMem α 1 F` is an *integrated*
condition (`z ↦ ∫_θ HkIntegrand α 1 F z θ` is `L¹`), which by itself gives no pointwise bound
on a slice.  The argument below converts the integrated bound into a *slicewise* bound and then
into a bound on the *difference quotients*:

* the fundamental theorem of calculus in `z` gives, for `θ ∈ (0,π/2)` and `x, y > 0`,
  `|F x θ - F y θ| ≤ ∫_{uIoc y x} |∂_z F t θ| dt`;
* the `θ`-integral of `|∂_z F t ·|` is controlled by `∫_θ HkIntegrand α 1 F t θ` through
  AM–GM (`2|a|s^{η/2} ≤ a²s^{-η} + s^{η}`) and the fact that `w(t) ≥ 1`;
* the resulting double integral is exchanged by Fubini/Tonelli
  (`Work.Spaces.integrable_prod_of_iterated`), after which the shrinking `z`-interval makes the
  bound tend to `0` by continuity of the primitive of an `L¹` function.

The proof rests on the four lemmas requested in parallel (`slice_abs_integrable`,
`slice_abs_integral_le`, `aesm_uncurry_abs_pzF`, `slice_abs_diff_le_uIoc`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integrable
import Submission.Work.FTS.PhiStar.Honesty.aesm_uncurry_abs_pzF
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_diff_le_uIoc
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter Classical

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Auxiliary definitions and elementary facts -/

/-- The angular weight `e_m(θ)·cos θ` of the `m`-th mode. -/
private def phiW (m : ℕ) (θ : ℝ) : ℝ :=
  Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ

/-- The numerator of `cmode m F z`, written as a set integral over `Iθ`. -/
private def numW (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, F z θ * phiW m θ

/-- `|∂_z F|` restricted to the interval between `z0` and `x`. -/
private def pzInd (F : ℝ → ℝ → ℝ) (x z0 : ℝ) : ℝ → ℝ → ℝ :=
  fun t θ => if t ∈ Set.uIoc z0 x then |Work.Spaces.pz F t θ| else 0

/-- A weight restricted to the interval between `z0` and `x`. -/
private def WInd (W : ℝ → ℝ) (x z0 : ℝ) : ℝ → ℝ :=
  fun t => if t ∈ Set.uIoc z0 x then W t else 0

/-- The angular mode weight is continuous. -/
private theorem continuous_phiW (m : ℕ) : Continuous (phiW m) := by
  have h : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    rw [show Work.FTS.PhiStar.Gegenbauer.eFam m = fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) from rfl]
    exact Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)
  rw [show phiW m = fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ from rfl]
  exact h.mul Real.continuous_cos

/-- `cmode m F z` as the numerator divided by the explicit mode normalisation constant. -/
private theorem cmode_eq_num_div (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode m F z
      = numW m F z / (((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5)) := by
  have hden : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) :=
    Work.FTS.PhiStar.Gegenbauer.FamNormValue m
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, F z θ * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2),
      Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun θ _ => by ring)
  rw [Work.FTS.PhiStar.Series.cmode, hnum, hden]
  simp only [numW, phiW]

/-- The `z`-slice integral of the `H¹` integrand is integrable on any interval of positive
radii. -/
private theorem integrableOn_HkIntegrand_Icc {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 1 F) {a b : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ)
      (Set.Icc a b) :=
  hF.2.mono_set (fun t ht => by
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    exact le_trans ha ht.1)

/-- Almost every point of `Iθ` lies strictly inside it. -/
private theorem ae_mem_Ioo_Itheta :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ,
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The main theorem -/

theorem continuousOn_cmode_of_hkMem_one {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F) :
    ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z) (Set.Ioi 0) := by
  -- the bounded angular weight and the explicit normalisation constant
  obtain ⟨Cφ, hCφnn, hCφ⟩ := exists_bound_eFam_mul_cos m
  set D : ℝ := ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hphiW : ∀ θ ∈ Work.Spaces.Iθ, |phiW m θ| ≤ Cφ := fun θ hθ => by
    rw [phiW]; exact hCφ θ hθ
  -- the numerator is continuous
  have hNumcont : ContinuousOn (numW m F) (Set.Ioi 0) := by
    intro z0 hz0
    have hz0pos : (0 : ℝ) < z0 := hz0
    -- a symmetric neighbourhood `[a,b]` of `z0` inside `(0,∞)`
    set a : ℝ := z0 / 2 with hadef
    set b : ℝ := 3 * z0 / 2 with hbdef
    have ha : 0 < a := by rw [hadef]; linarith
    have hab : a ≤ b := by rw [hadef, hbdef]; linarith
    have haz0 : a < z0 := by rw [hadef]; linarith
    have hz0b : z0 < b := by rw [hbdef]; linarith
    have hz0ab : z0 ∈ Set.Icc a b := ⟨haz0.le, hz0b.le⟩
    -- the `z`-integrand and its dominating weight
    set HI : ℝ → ℝ := fun t => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ
      with hHIdef
    set W : ℝ → ℝ := fun t => HI t / a ^ 2 + Real.pi / 4 with hWdef
    have hHInn : ∀ t, 0 ≤ HI t := fun t =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 1 F t θ
    have hWnn : ∀ t, 0 ≤ W t := by
      intro t; rw [hWdef]
      have h1 : 0 ≤ HI t / a ^ 2 := div_nonneg (hHInn t) (by positivity)
      linarith [Real.pi_pos]
    -- integrability of the weight in `z` on `[a,b]`
    have hHIint : MeasureTheory.Integrable HI
        (MeasureTheory.volume.restrict (Set.Icc a b)) := by
      rw [hHIdef]
      exact integrableOn_HkIntegrand_Icc hF ha.le
    have hWint : MeasureTheory.Integrable W (MeasureTheory.volume.restrict (Set.Icc a b)) := by
      rw [hWdef]
      have h1 : MeasureTheory.Integrable (fun t : ℝ => (1 / a ^ 2) * HI t)
          (MeasureTheory.volume.restrict (Set.Icc a b)) := hHIint.const_mul _
      have h2 : MeasureTheory.Integrable (fun _ : ℝ => Real.pi / 4)
          (MeasureTheory.volume.restrict (Set.Icc a b)) := MeasureTheory.integrable_const _
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
      show (1 / a ^ 2) * HI t + Real.pi / 4 = HI t / a ^ 2 + Real.pi / 4
      ring
    -- the angular slices of `∂_z F`
    have hslice : ∀ t ∈ Set.Icc a b, MeasureTheory.Integrable
        (fun θ : ℝ => |Work.Spaces.pz F t θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun t ht =>
      (slice_abs_integrable hsm hF (lt_of_lt_of_le ha ht.1)).2
    have hjoint : MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|))
        ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      aesm_uncurry_abs_pzF hsm ha
    have hbound_t : ∀ t ∈ Set.Icc a b,
        (∫ θ, |Work.Spaces.pz F t θ| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ≤ W t := fun t ht => by
      rw [hWdef]
      exact (slice_abs_integral_le hsm hF ha ht.1).2
    have houter : MeasureTheory.Integrable
        (fun t : ℝ => ∫ θ, |Work.Spaces.pz F t θ| ∂(MeasureTheory.volume.restrict
          Work.Spaces.Iθ)) (MeasureTheory.volume.restrict (Set.Icc a b)) := by
      have haesm := MeasureTheory.AEStronglyMeasurable.integral_prod_right' hjoint
      refine MeasureTheory.Integrable.mono' hWint haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => abs_nonneg _)]
      exact hbound_t t ht
    -- Fubini on the box
    obtain ⟨hGint, -⟩ := Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict (Set.Icc a b))
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (G := fun t θ : ℝ => |Work.Spaces.pz F t θ|) (fun t θ => abs_nonneg _) hjoint
      (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
          exact hslice t ht)
      houter
    -- the estimate for a fixed `x ∈ [a,b]`
    have hstep : ∀ x ∈ Set.Icc a b,
        |numW m F x - numW m F z0| ≤ Cφ * ∫ t in Set.uIoc z0 x, W t := by
      intro x hx
      have hxuIoc : Set.uIoc z0 x ⊆ Set.Icc a b := by
        rcases le_total z0 x with h | h
        · rw [Set.uIoc_of_le h]
          exact Set.Ioc_subset_Icc_self.trans
            (Set.Icc_subset_Icc haz0.le hx.2)
        · rw [Set.uIoc_of_ge h]
          exact Set.Ioc_subset_Icc_self.trans
            (Set.Icc_subset_Icc hx.1 hz0b.le)
      have hpx : 0 < x := lt_of_lt_of_le ha hx.1
      -- integrability of `F y · · φ`
      have hFint : ∀ y ∈ Set.Icc a b,
          MeasureTheory.Integrable (fun θ : ℝ => F y θ * phiW m θ)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        intro y hy
        have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
        have hbase : MeasureTheory.Integrable (fun θ : ℝ => |F y θ|)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          (slice_abs_integrable hsm hF hy0).1
        refine MeasureTheory.Integrable.mono' (hbase.const_mul Cφ) ?_ ?_
        · exact ((hsm.aesm_slice_pzIter 0 hy0).mul (continuous_phiW m).aestronglyMeasurable)
        · filter_upwards [MeasureTheory.ae_restrict_mem (by
              rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with θ hθ
          rw [Real.norm_eq_abs, abs_mul]
          calc |F y θ| * |phiW m θ| ≤ |F y θ| * Cφ :=
                mul_le_mul_of_nonneg_left (hphiW θ hθ) (abs_nonneg _)
            _ = Cφ * |F y θ| := by ring
      -- the indicator function carrying the `uIoc` restriction
      have hGi_eq : Function.uncurry (pzInd F x z0)
          = (Set.uIoc z0 x ×ˢ Set.univ).indicator
              (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|)) := by
        funext p
        simp only [Function.uncurry, pzInd, Set.indicator_apply, Set.mem_prod, Set.mem_univ,
          and_true]
      have hGiint : MeasureTheory.Integrable (Function.uncurry (pzInd F x z0))
          ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [hGi_eq]
        exact hGint.indicator (measurableSet_uIoc.prod MeasurableSet.univ)
      have hpzInd_nn : ∀ t θ, 0 ≤ pzInd F x z0 t θ := by
        intro t θ
        rw [pzInd]
        by_cases h : t ∈ Set.uIoc z0 x <;> simp [h]
      -- the `t`-marginal of the indicator, rewritten as a set integral over `uIoc`
      have hGi_marg : ∀ θ : ℝ,
          (∫ t, pzInd F x z0 t θ ∂(MeasureTheory.volume.restrict (Set.Icc a b)))
            = ∫ t in Set.uIoc z0 x, |Work.Spaces.pz F t θ| := by
        intro θ
        have h1 : (fun t : ℝ => pzInd F x z0 t θ)
            = (Set.uIoc z0 x).indicator (fun t : ℝ => |Work.Spaces.pz F t θ|) := by
          funext t
          simp only [pzInd, Set.indicator_apply]
        rw [h1]
        show (∫ t in Set.Icc a b,
            (Set.uIoc z0 x).indicator (fun t : ℝ => |Work.Spaces.pz F t θ|) t) = _
        rw [MeasureTheory.setIntegral_indicator measurableSet_uIoc,
          Set.inter_eq_right.mpr hxuIoc]
      -- the marginal is integrable
      have hsecint : MeasureTheory.Integrable
          (fun θ : ℝ => ∫ t, pzInd F x z0 t θ
            ∂(MeasureTheory.volume.restrict (Set.Icc a b)))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.Integrable.integral_prod_right hGiint
      -- the `t`-integral of the marginal is bounded by the `uIoc`-integral of `W`
      have hInd_eq : (∫ t, WInd W x z0 t ∂(MeasureTheory.volume.restrict (Set.Icc a b)))
          = ∫ t in Set.uIoc z0 x, W t := by
        have h1 : (fun t : ℝ => WInd W x z0 t) = (Set.uIoc z0 x).indicator W := by
          funext t
          simp only [WInd, Set.indicator_apply]
        rw [h1]
        show (∫ t in Set.Icc a b, (Set.uIoc z0 x).indicator W t) = _
        rw [MeasureTheory.setIntegral_indicator measurableSet_uIoc,
          Set.inter_eq_right.mpr hxuIoc]
      have hWIndint : MeasureTheory.Integrable (WInd W x z0)
          (MeasureTheory.volume.restrict (Set.Icc a b)) := by
        refine MeasureTheory.Integrable.mono' hWint
          (hWint.aestronglyMeasurable.indicator measurableSet_uIoc) ?_
        filter_upwards with t
        rw [Real.norm_eq_abs]
        by_cases h : t ∈ Set.uIoc z0 x
        · rw [WInd, if_pos h, abs_of_nonneg (hWnn t)]
        · rw [WInd, if_neg h, abs_zero]
          exact hWnn t
      have htmono : (∫ t, (∫ θ, pzInd F x z0 t θ ∂(MeasureTheory.volume.restrict
            Work.Spaces.Iθ)) ∂(MeasureTheory.volume.restrict (Set.Icc a b)))
          ≤ ∫ t in Set.uIoc z0 x, W t := by
        rw [← hInd_eq]
        refine MeasureTheory.integral_mono_of_nonneg ?_ hWIndint ?_
        · filter_upwards with t
          exact MeasureTheory.integral_nonneg fun θ => hpzInd_nn t θ
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
          by_cases h : t ∈ Set.uIoc z0 x
          · have hteq : (∫ θ, pzInd F x z0 t θ ∂(MeasureTheory.volume.restrict
                Work.Spaces.Iθ)) = ∫ θ, |Work.Spaces.pz F t θ|
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
              simp only [pzInd, if_pos h]
            rw [hteq, WInd, if_pos h, hWdef]
            exact (slice_abs_integral_le hsm hF ha (hxuIoc h).1).2
          · have hteq : (∫ θ, pzInd F x z0 t θ ∂(MeasureTheory.volume.restrict
                Work.Spaces.Iθ)) = 0 := by
              simp only [pzInd, if_neg h, MeasureTheory.integral_zero]
            rw [hteq, WInd, if_neg h]
      -- Fubini
      have hswap : (∫ θ, (∫ t, pzInd F x z0 t θ ∂(MeasureTheory.volume.restrict
            (Set.Icc a b))) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = ∫ t, (∫ θ, pzInd F x z0 t θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
              ∂(MeasureTheory.volume.restrict (Set.Icc a b)) :=
        (MeasureTheory.integral_integral_swap
          (μ := MeasureTheory.volume.restrict (Set.Icc a b))
          (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hGiint).symm
      -- the `θ`-integrand is dominated a.e. by the `t`-marginal
      have hpoint : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          |F x θ - F z0 θ| * |phiW m θ|
            ≤ Cφ * ∫ t, pzInd F x z0 t θ ∂(MeasureTheory.volume.restrict (Set.Icc a b)) := by
        filter_upwards [ae_mem_Ioo_Itheta] with θ hθ
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
        have h1 : |F x θ - F z0 θ| ≤ ∫ t in Set.uIoc z0 x, |Work.Spaces.pz F t θ| :=
          slice_abs_diff_le_uIoc hsm hθ (lt_of_lt_of_le ha hx.1) (lt_of_lt_of_le ha hz0ab.1)
        have h2 : |phiW m θ| ≤ Cφ := hphiW θ hθI
        have h3 : (0 : ℝ) ≤ ∫ t in Set.uIoc z0 x, |Work.Spaces.pz F t θ| :=
          MeasureTheory.integral_nonneg fun t => by
            by_cases h : t ∈ Set.uIoc z0 x <;> simp [h]
        calc |F x θ - F z0 θ| * |phiW m θ|
            ≤ (∫ t in Set.uIoc z0 x, |Work.Spaces.pz F t θ|) * Cφ :=
              mul_le_mul h1 h2 (abs_nonneg _) h3
          _ = Cφ * ∫ t, pzInd F x z0 t θ ∂(MeasureTheory.volume.restrict (Set.Icc a b)) := by
              rw [← hGi_marg θ]; ring
      -- the difference of the numerators
      have hlin : numW m F x - numW m F z0
          = ∫ θ in Work.Spaces.Iθ, (F x θ - F z0 θ) * phiW m θ := by
        simp only [numW]
        rw [← MeasureTheory.integral_sub (hFint x hx) (hFint z0 hz0ab)]
        refine MeasureTheory.setIntegral_congr_fun (by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ _ => by ring)
      calc |numW m F x - numW m F z0|
          = |∫ θ in Work.Spaces.Iθ, (F x θ - F z0 θ) * phiW m θ| := by rw [hlin]
        _ ≤ ∫ θ in Work.Spaces.Iθ, |(F x θ - F z0 θ) * phiW m θ| :=
            MeasureTheory.abs_integral_le_integral_abs
        _ = ∫ θ in Work.Spaces.Iθ, |F x θ - F z0 θ| * |phiW m θ| :=
            MeasureTheory.setIntegral_congr_fun (by
              rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ _ => by rw [abs_mul])
        _ ≤ ∫ θ in Work.Spaces.Iθ, Cφ * (∫ t, pzInd F x z0 t θ
              ∂(MeasureTheory.volume.restrict (Set.Icc a b))) :=
            MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun θ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (hsecint.const_mul Cφ) hpoint
        _ = Cφ * ∫ θ, (∫ t, pzInd F x z0 t θ
              ∂(MeasureTheory.volume.restrict (Set.Icc a b)))
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
            MeasureTheory.integral_const_mul Cφ _
        _ = Cφ * ∫ t, (∫ θ, pzInd F x z0 t θ
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
              ∂(MeasureTheory.volume.restrict (Set.Icc a b)) := by rw [hswap]
        _ ≤ Cφ * ∫ t in Set.uIoc z0 x, W t := mul_le_mul_of_nonneg_left htmono hCφnn
    -- the `uIoc` integral is the absolute value of the primitive
    have huIoc_eq : ∀ x ∈ Set.Icc a b, ∫ t in Set.uIoc z0 x, W t
        = |∫ t in z0..x, W t| := by
      intro x hx
      rcases le_total z0 x with h | h
      · rw [Set.uIoc_of_le h, ← intervalIntegral.integral_of_le h]
        exact (abs_of_nonneg (intervalIntegral.integral_nonneg h fun t _ => hWnn t)).symm
      · have hsym : (∫ t in z0..x, W t) = -(∫ t in x..z0, W t) :=
          intervalIntegral.integral_symm x z0
        have hnn : 0 ≤ ∫ t in x..z0, W t :=
          intervalIntegral.integral_nonneg h (fun t _ => hWnn t)
        rw [Set.uIoc_of_ge h, ← intervalIntegral.integral_of_le h, hsym,
          abs_of_nonpos (by linarith)]
        ring
    -- the primitive is continuous on `[a,b]`
    have hWint' : MeasureTheory.IntegrableOn W (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]; exact hWint
    have hWii : IntervalIntegrable W MeasureTheory.volume a b :=
      hWint'.intervalIntegrable
    have hVtend : Filter.Tendsto (fun x => ∫ t in z0..x, W t)
        (𝓝[Set.Icc a b] z0) (𝓝 0) := by
      have hVcont : ContinuousOn (fun x => ∫ t in z0..x, W t) (Set.uIcc a b) :=
        intervalIntegral.continuousOn_primitive_interval' hWii (by
          rw [Set.uIcc_of_le hab]; exact ⟨haz0.le, hz0b.le⟩)
      have hVcont' : ContinuousOn (fun x => ∫ t in z0..x, W t) (Set.Icc a b) := by
        rw [← Set.uIcc_of_le hab]; exact hVcont
      have h0 : (∫ t in z0..z0, W t) = 0 := intervalIntegral.integral_same
      have hcw : Filter.Tendsto (fun x => ∫ t in z0..x, W t) (𝓝[Set.Icc a b] z0)
          (𝓝 (∫ t in z0..z0, W t)) := hVcont'.continuousWithinAt hz0ab
      rwa [h0] at hcw
    -- squeeze
    have hsq : Filter.Tendsto (fun x => |numW m F x - numW m F z0|)
        (𝓝[Set.Icc a b] z0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun x => Cφ * |∫ t in z0..x, W t|) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with x hx
        rw [Real.norm_eq_abs, abs_abs]
        calc |numW m F x - numW m F z0| ≤ Cφ * ∫ t in Set.uIoc z0 x, W t := hstep x hx
          _ = Cφ * |∫ t in z0..x, W t| := by rw [huIoc_eq x hx]
      · have h2 : Filter.Tendsto (fun x => |∫ t in z0..x, W t|)
            (𝓝[Set.Icc a b] z0) (𝓝 0) := by
          simpa using hVtend.abs
        simpa using h2.const_mul Cφ
    -- conclude
    have hsub : Filter.Tendsto (fun x => numW m F x - numW m F z0)
        (𝓝[Set.Icc a b] z0) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [Real.norm_eq_abs] using hsq
    have hcwt : ContinuousWithinAt (numW m F) (Set.Icc a b) z0 := by
      rw [ContinuousWithinAt]
      simpa using hsub.add_const (numW m F z0)
    exact (hcwt.continuousAt (Icc_mem_nhds haz0 hz0b)).continuousWithinAt
  -- assemble
  refine (hNumcont.div_const D).congr (fun z _ => ?_)
  exact (cmode_eq_num_div m F z).trans (by rw [hDdef])

end Work.FTS.PhiStar.Honesty
