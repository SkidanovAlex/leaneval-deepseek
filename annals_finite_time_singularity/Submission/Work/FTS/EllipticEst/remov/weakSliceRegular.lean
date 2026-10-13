import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.Elliptic.LzeroAdj_sinCos2
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.integrable_prod_ae
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.EllipticEst.remov.wsSliceLeft
import Submission.Work.FTS.EllipticEst.remov.wsMomentChain
import Submission.Work.FTS.EllipticEst.remov.wsPzBounds
import Submission.Work.FTS.EllipticEst.remov.wsBoxIntegrable
import Submission.Work.FTS.EllipticEst.remov.wsMomentId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Preparatory facts for the endpoint arguments

The right endpoint of the angular interval is controlled by a *single* integration of `Lzero1`
(see the comment above `weakSliceRegular` at the end of this file); the left endpoint by the
integration by parts against `sinθcos²θ`.  The lemmas below supply the inputs those arguments
consume: a.e. strong measurability of a slice (so that the totalised integrals are honest), the
weight facts `sEta > 0`, `sEta ≥ 1` and `sEta⁻¹ ≤ 1` on the open interval, and the passage from
the weighted square to the absolute value. -/

/-- A function that is `C^n` on the open interval `(0,π/2)` is a.e. strongly measurable for the
measure `volume.restrict Iθ` (the two endpoints of `Iθ` are null). -/
theorem aesm_of_contDiffOn_Ioo {u : ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
  obtain ⟨g, hgm, hge⟩ := h.continuousOn.aemeasurable measurableSet_Ioo
  refine ⟨g, hgm.stronglyMeasurable, ?_⟩
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (0 : ℝ) := by
    rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (0 : ℝ)
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (Real.pi / 2)
  have h3 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioo 0 (Real.pi / 2) → u x = g x := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hge
    exact hge
  rw [Filter.EventuallyEq, Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hxI
  exact hx3 ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx1), lt_of_le_of_ne hxI.2 hx2⟩

/-- `sEta` is nonnegative on `Iθ`. -/
theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
  · rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ; linarith [hθ.1]
  · rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ; linarith [hθ.2]

/-- `sEta ≥ 1` on the open interval. -/
theorem one_le_sEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ sEta θ :=
  Work.FTS.EllipticEst.sliceLim_one_le_sEta hθ

/-- `sEta > 0` on the open interval. -/
theorem sEta_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < sEta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  simpa only [Work.FTS.EllipticEst.sEta] using Real.rpow_pos_of_pos hs (-(Work.Spaces.eta))

/-- On the open interval, `sEta⁻¹ = sin(2θ)^{η} ≤ 1`. -/
theorem inv_sEta_le_one_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (sEta θ)⁻¹ ≤ 1 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : 0 ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have hinv : (sEta θ)⁻¹ = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hs0 Work.Spaces.eta, inv_inv]
  rw [hinv]
  exact Real.rpow_le_one hs0 hs1 hη

/-- **From the weighted square to the absolute value.**  If `g²·sEta` is integrable on `Iθ` and
`g` is a.e. strongly measurable, then `|g|` is integrable on `Iθ`: on the open interval
`2|g| ≤ g²·sEta + sEta⁻¹ ≤ g²·sEta + 1`, and the endpoints are null. -/
theorem integrableOn_abs_of_sq_mul_sEta {g : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ))
    (h : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |g θ|) Work.Spaces.Iθ := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ => (1 / 2) * ((g θ) ^ 2 * sEta θ + 1)) Work.Spaces.Iθ :=
    (h.add (integrableOn_const (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (by simp))).const_mul (1 / 2)
  refine MeasureTheory.Integrable.mono' hmaj hgm.norm ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  have hs := sEta_pos_Ioo hθ
  have hamgm : 2 * |g θ| ≤ (g θ) ^ 2 * sEta θ + (sEta θ)⁻¹ := by
    have hsq : 0 ≤ (|g θ| * Real.sqrt (sEta θ) - 1 / Real.sqrt (sEta θ)) ^ 2 := sq_nonneg _
    have hsq' : (|g θ| * Real.sqrt (sEta θ)) ^ 2 = (g θ) ^ 2 * sEta θ := by
      rw [mul_pow, sq_abs, Real.sq_sqrt (le_of_lt hs)]
    have hinv : (1 / Real.sqrt (sEta θ)) ^ 2 = (sEta θ)⁻¹ := by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hs), one_div]
    have hcross : 2 * (|g θ| * Real.sqrt (sEta θ)) * (1 / Real.sqrt (sEta θ)) = 2 * |g θ| := by
      field_simp
    nlinarith [hsq, hsq', hinv, hcross]
  have hle1 : (sEta θ)⁻¹ ≤ 1 := inv_sEta_le_one_Ioo hθ
  have hfin : 2 * |g θ| ≤ 2 * ((1 / 2) * ((g θ) ^ 2 * sEta θ + 1)) := by nlinarith [hamgm, hle1]
  linarith [hfin]

/-- **Boundedness of a slice and of its derivative.**  If `(u'')²·sEta` is integrable on `Iθ`
then `u'' ∈ L¹` on the open interval (`sEta ≥ 1` there), so `u'` has an oscillation bound
`|u' x - u' y| ≤ ∫|u''|` and `u` is bounded by integrating once more. -/
theorem abs_le_of_sq_mul_sEta {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * sEta θ) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ C ∧ |u θ| ≤ C := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hIq : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hq0, hq⟩
  have hsq : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h2
  have habs2 : MeasureTheory.IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x := by
    intro x hx
    have h2' : ContDiffAt ℝ 2 u x := (hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by norm_num)
    have h1 : ContDiffAt ℝ 1 (deriv u) x := h2'.derivWithin (by norm_num)
    exact (h1.differentiableAt (by norm_num)).hasDerivAt
  have hMono : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, |deriv (fun t => deriv u t) s|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro a b hab hsub
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_mono_set habs2
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (Filter.Eventually.of_forall fun s hs => hsub ⟨le_of_lt hs.1, hs.2⟩)
  have hFTC2 : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, deriv (fun t => deriv u t) s = deriv u b - deriv u a := by
    intro a b hab hsub
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
    · intro z hz
      exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
    · intro z hz
      exact hderiv2 z (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    · have h1 : MeasureTheory.IntegrableOn (fun s => deriv (fun t => deriv u t) s)
          (Set.Ioc a b) :=
        MeasureTheory.Integrable.mono'
          (habs2.mono_set fun z hz => hsub ⟨le_of_lt hz.1, hz.2⟩)
          (measurable_deriv _).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs])
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr h1
  have hosc : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u x - deriv u y|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · have hsub : Set.Icc x y ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
      rw [abs_sub_comm, ← hFTC2 hxy hsub]
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun s => deriv (fun t => deriv u t) s) hxy
      simp only [Real.norm_eq_abs] at h1
      exact h1.trans (hMono hxy hsub)
    · have hsub : Set.Icc y x ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
      rw [← hFTC2 hyx hsub]
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun s => deriv (fun t => deriv u t) s) hyx
      simp only [Real.norm_eq_abs] at h1
      exact h1.trans (hMono hyx hsub)
  have hud : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro θ hθ
    have h := hosc θ hθ (Real.pi / 4) hIq
    have h1 : |deriv u θ| ≤ |deriv u θ - deriv u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := by
      have := abs_add_le (deriv u θ - deriv u (Real.pi / 4)) (deriv u (Real.pi / 4))
      simpa using this
    linarith
  have hIint : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |∫ s in (Real.pi / 4)..θ, deriv u s|
        ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := by
    intro θ hθ
    have hb : ∀ s ∈ Set.uIoc (Real.pi / 4) θ,
        ‖deriv u s‖ ≤ |deriv u (Real.pi / 4)|
          + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
      intro s hs
      rw [Set.uIoc, Set.mem_Ioc] at hs
      have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨lt_trans (lt_min hq0 hθ.1) hs.1, lt_of_le_of_lt hs.2 (max_lt hq hθ.2)⟩
      rw [Real.norm_eq_abs]
      exact hud s hs'
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (f := deriv u)
      (C := |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|) hb
    have h2 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · linarith [hθ.1, hθ.2, hq0, Real.pi_pos]
      · linarith [hθ.1, hθ.2, hq0, Real.pi_pos]
    have h3 : 0 ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
      have hI : 0 ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| :=
        integral_nonneg fun s => abs_nonneg _
      linarith [abs_nonneg (deriv u (Real.pi / 4)), hI]
    calc |∫ s in (Real.pi / 4)..θ, deriv u s|
        ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * |θ - Real.pi / 4| := by
          simpa only [Real.norm_eq_abs] using h1
      _ ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := mul_le_mul_of_nonneg_left h2 h3
  have hFTCu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∫ s in (Real.pi / 4)..θ, deriv u s = u θ - u (Real.pi / 4) := by
    intro θ hθ
    rcases le_total (Real.pi / 4) θ with hle | hle
    · have hsub : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hq0 hz.1, lt_of_le_of_lt hz.2 hθ.2⟩
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle ?_ ?_ ?_
      · intro z hz
        exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds (hsub hz))).continuousAt).continuousWithinAt
      · intro z hz
        exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds
          (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩))).differentiableAt (by norm_num)).hasDerivAt
      · have hcd : ContinuousOn (deriv u) (Set.uIcc (Real.pi / 4) θ) := fun z hz => by
          rw [Set.uIcc_of_le hle] at hz
          exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
        exact hcd.intervalIntegrable
    · have hsub : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hθ.1 hz.1, lt_of_le_of_lt hz.2 hq⟩
      have h1 : ∫ s in θ..(Real.pi / 4), deriv u s = u (Real.pi / 4) - u θ := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle ?_ ?_ ?_
        · intro z hz
          exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds (hsub hz))).continuousAt).continuousWithinAt
        · intro z hz
          exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds
            (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩))).differentiableAt (by norm_num)).hasDerivAt
        · have hcd : ContinuousOn (deriv u) (Set.uIcc θ (Real.pi / 4)) := fun z hz => by
            rw [Set.uIcc_of_le hle] at hz
            exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
          exact hcd.intervalIntegrable
      rw [intervalIntegral.integral_symm (a := θ) (b := Real.pi / 4), h1]
      ring
  have hubd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ |u (Real.pi / 4)|
        + (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := by
    intro θ hθ
    have h1 : |u θ| ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := by
      have := abs_add_le (u (Real.pi / 4)) (u θ - u (Real.pi / 4))
      simpa using this
    have h2 : |u θ - u (Real.pi / 4)| ≤ (|deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
        * (Real.pi / 2) := by
      rw [(congrArg abs (hFTCu θ hθ)).symm]
      exact hIint θ hθ
    linarith
  set I0 : ℝ := ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| with hI0def
  have hI0 : 0 ≤ I0 := by
    rw [hI0def]; exact integral_nonneg fun _ => abs_nonneg _
  have hA : 0 ≤ |u (Real.pi / 4)| := abs_nonneg _
  have hB : 0 ≤ |deriv u (Real.pi / 4)| := abs_nonneg _
  have hP' : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h1P' : 1 ≤ 1 + Real.pi / 2 := by linarith [Real.pi_pos]
  have hS0 : 0 ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA, hB, hI0]
  have hSpos : 0 < |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA, hB, hI0]
  refine ⟨(|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2), ?_, ?_⟩
  · exact mul_pos hSpos (by linarith [h1P'])
  · intro θ hθ
    have hud' : |deriv u θ| ≤ |deriv u (Real.pi / 4)| + I0 := by
      rw [hI0def]; exact hud θ hθ
    have hubd' : |u θ| ≤ |u (Real.pi / 4)|
        + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2) := by
      rw [hI0def]; exact hubd θ hθ
    have h9 : |deriv u θ| ≤ |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hud', hI0]
    have h10 : |deriv u (Real.pi / 4)| + I0 + 1
        ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by
      have hle : |deriv u (Real.pi / 4)| + I0 + 1
          ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA]
      calc |deriv u (Real.pi / 4)| + I0 + 1
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1 := by
            rw [mul_one]; exact hle
        _ ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) :=
            mul_le_mul_of_nonneg_left h1P' hS0
    have h12 : |u (Real.pi / 4)| + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
        ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by
      have hleA : |u (Real.pi / 4)| ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1 := by
        rw [mul_one]; linarith [hB, hI0]
      have hleX : (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_right (by linarith [hA]) hP'
      calc |u (Real.pi / 4)| + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1
            + (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (Real.pi / 2) :=
            add_le_add hleA hleX
        _ = (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by ring
    exact ⟨h9.trans h10, hubd'.trans h12⟩

/-- **The right-end limit of a slice with honest `Lzero1`-source.**  A single integration of
`Lzero1 u = -u'' + (tan θ · u)' - 6u` over `(ε,b)` gives

  `tan b · u b = ∫_ε^b Lzero1 u + u'(b) - u'(ε) + tan(ε)·u(ε) + 6∫_ε^b u`,

whose right hand side is bounded uniformly in `ε, b` (`Lzero1 u ∈ L¹`, `u'` bounded by
`abs_le_of_sq_mul_sEta`, `u ∈ L¹`), so that `|tan b · u b| ≤ K` and hence
`|u θ| ≤ K·cos θ/ sin θ → 0` as `θ → (π/2)⁻`.  Proved by the colleague as
`Submission.Work.FTS.EllipticEst.remov.wsSliceRight`. -/
theorem sliceTendstoRight_fts {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hL : MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hu : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  Work.FTS.EllipticEst.remov.wsSliceRight hsm h2 hL hu

/-! # Weak-class slice regularity and honesty

For data of the weak class `EllWeakPos α k F Ψ` (with `α ∈ (0,1/4]`, `k ≥ 1`) and every radial
value `z > 0`, the angular slice `u := θ ↦ Ψ z θ` is *continuous up to the endpoints* of
`[0, π/2]`, takes the Dirichlet values `0` there, satisfies the slice equation
`Lzero1 u = g` with `g := θ ↦ Lzero1 u θ` (the slice of the angular source) on the open
interval, is orthogonal to `sin θ cos²θ`, and its low-order weighted integrals are honest:
`∫ u²`, `∫ (u')²` and `∫ (u'')² sEta` are all finite.

Status: see `NOTES_wsAux.md`.  All the analytic inputs are now available:
`ws_slot_slice` (conjunct 7), `abs_le_of_sq_mul_sEta` (boundedness, hence conjuncts 5-6),
`ws_Lzero1_energy_integrable` and `wsMomentIdentity` (the moment condition for the left
endpoint), `remov.wsSliceRight` and `remov.wsSliceLeft` (the two one-dimensional endpoint
limits) and `remov.wsMomentChain` (the moment chain).  The remaining work is the wrapper below;
a first draft of it is in the git history of this file and in `NOTES_wsAux.md` §2. -/

/-- `D_z(∂_θ²Ψ)(z,θ) = z · ∂_θ²(∂_zΨ)(z,θ)` on the open quadrant. -/
theorem ws_pth2_pz_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
      = z * deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ := by
  rw [← Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hΨ 1 hz hθ]
  have h1 : (fun t => deriv (fun θ' => Work.Spaces.Dz Ψ z θ') t)
      = fun t => z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') t := by
    funext t
    show deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') t
        = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') t
    rw [deriv_const_mul_field]
  show deriv (fun t => deriv (fun θ' => Work.Spaces.Dz Ψ z θ') t) θ
      = z * deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ
  rw [h1]
  show deriv (fun t => z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ
      = z * deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ
  rw [deriv_const_mul_field]

local notation "SS" => Work.FTS.EllipticEst.sEta

/-- The `θ`-energy of `∂_zΨ` is honest (no junk value). -/
theorem ws_pz_energy_integrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2 * SS θ)
      Work.Spaces.Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB1 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * SS θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice (hΨ.pth).pth h.memB 1 hk hz
  have hz2ne : z ^ 2 ≠ 0 := ne_of_gt (pow_pos hz 2)
  have hE : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ) ^ 2 * SS θ)
      Work.Spaces.Iθ := by
    have hcong : (fun θ => (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * SS θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (z ^ 2) * ((deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ)
          ^ 2 * SS θ)) := by
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [Work.FTS.EllipticEst.remov.ws_pth2_pz_eq hΨ hz hθ]
      ring
    refine ((hB1.congr hcong).mul_const ((z ^ 2)⁻¹)).congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ _
    rw [show (z ^ 2 * ((deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ) ^ 2
            * SS θ)) * (z ^ 2)⁻¹
        = ((deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ) ^ 2 * SS θ)
          * ((z ^ 2) * (z ^ 2)⁻¹) from by ring,
      mul_inv_cancel₀ hz2ne, mul_one]
  have hpt := Work.FTS.EllipticEst.remov.ws_slice_pointwise_le
    (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice (hΨ.pz) hz) hE
  set M : ℝ := 2 * (Work.Spaces.pz Ψ z (Real.pi / 4)) ^ 2
    + 4 * Real.pi ^ 2 * (1 + (∫ s in Work.Spaces.Iθ, SS s))
        * (1 + (deriv (fun θ' => Work.Spaces.pz Ψ z θ') (Real.pi / 4)) ^ 2
          + (∫ s in Work.Spaces.Iθ,
              (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) s) ^ 2 * SS s))
    with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 ≤ (∫ s in Work.Spaces.Iθ, SS s) :=
      Work.FTS.EllipticEst.remov.ws_sEta_integral_nonneg
    have h2 : 0 ≤ (∫ s in Work.Spaces.Iθ,
        (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) s) ^ 2 * SS s) := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.remov.ws_sEta_nonneg hs)
    have h3 : 0 ≤ 4 * Real.pi ^ 2 * (1 + (∫ s in Work.Spaces.Iθ, SS s)) := by
      have h4 : (0 : ℝ) ≤ 1 + (∫ s in Work.Spaces.Iθ, SS s) := by linarith
      positivity
    have h5 : 0 ≤ 1 + (deriv (fun θ' => Work.Spaces.pz Ψ z θ') (Real.pi / 4)) ^ 2
        + (∫ s in Work.Spaces.Iθ,
            (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) s) ^ 2 * SS s) := by
      nlinarith [h2, sq_nonneg (deriv (fun θ' => Work.Spaces.pz Ψ z θ') (Real.pi / 4))]
    nlinarith [h3, h5, sq_nonneg (Work.Spaces.pz Ψ z (Real.pi / 4))]
  have hSS : MeasureTheory.AEStronglyMeasurable (fun θ => SS θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => SS p.2)
      (Work.FTS.EllipticEst.remov.ws_contOn_sEta) (z := 1) (by norm_num)
  refine MeasureTheory.Integrable.mono'
    (Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.const_mul M)
    (((Work.FTS.EllipticEst.remov.ws_aesm_slice (hΨ.pz) hz).pow 2).mul hSS) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hS0 : 0 ≤ SS θ := Work.FTS.EllipticEst.remov.ws_sEta_nonneg
    ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hS0)]
  exact mul_le_mul_of_nonneg_right (hpt θ hθ) hS0

/-- The `θ`-energy of `Lzero1 (Ψ z ·)` is honest.  Immediate from the slice equation
`Lzero1 (Ψ z ·) = F z · + α²z²∂_zzΨ(z,·) + α(5+α)(D_zΨ)(z,·)` and the three honest
`θ`-energies `(F z ·)²sEta`, `(z²∂_zzΨ(z,·))²sEta`, `(∂_zΨ(z,·))²sEta`. -/
theorem ws_Lzero1_energy_integrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hk : 1 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) ^ 2 * SS θ)
      Work.Spaces.Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hF : Work.FTS.EllipticEst.SmoothOpen F := Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hΨ
  have hF2 : MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * SS θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hF h.memF 0 (by omega) hz
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * SS θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hA h.memA 0 (by omega) hz
  have hpz2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2 * SS θ)
      Work.Spaces.Iθ := Work.FTS.EllipticEst.remov.ws_pz_energy_integrable hk h hz
  -- the dominating integrand
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => 3 * (((F z θ) ^ 2
        + ((α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        + ((α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2) * SS θ)) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => 3 * ((F z θ) ^ 2 * SS θ)) Work.Spaces.Iθ := hF2.const_mul 3
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => 3 * (((α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * SS θ))
        Work.Spaces.Iθ :=
      ((hA2.const_mul (α ^ 4)).const_mul 3).congr
        (Filter.Eventually.of_forall (fun θ => by ring))
    have h3 : MeasureTheory.IntegrableOn
        (fun θ => 3 * (((α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2 * SS θ))
        Work.Spaces.Iθ :=
      ((hpz2.const_mul ((α * (5 + α) * z) ^ 2)).const_mul 3).congr
        (Filter.Eventually.of_forall (fun θ => by ring))
    refine ((h1.add h2).add h3).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Pi.add_apply]
    ring
  -- a.e. strong measurability
  have hLm : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun θ => deriv (fun t => deriv (fun t' => Ψ z t') t) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (measurable_deriv (fun t => deriv (fun t' => Ψ z t') t)).aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ => deriv (fun t => Real.tan t * Ψ z t) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (measurable_deriv (fun t => Real.tan t * Ψ z t)).aestronglyMeasurable
    have h3 : MeasureTheory.AEStronglyMeasurable (fun θ => Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ hz
    have hfun : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ)
        = fun θ => -(deriv (fun t => deriv (fun t' => Ψ z t') t) θ)
            + deriv (fun t => Real.tan t * Ψ z t) θ - 6 * Ψ z θ := rfl
    rw [hfun]
    exact ((h1.neg).add h2).sub (h3.const_mul 6)
  have hSS : MeasureTheory.AEStronglyMeasurable (fun θ => SS θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => SS p.2)
      (Work.FTS.EllipticEst.remov.ws_contOn_sEta) (z := 1) (by norm_num)
  refine MeasureTheory.Integrable.mono' hdom ((hLm.pow 2).mul hSS) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hS0 : 0 ≤ SS θ := Work.FTS.EllipticEst.remov.ws_sEta_nonneg
    ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hbs := Work.Elliptic.bslOp_apply α Ψ z θ
  have heq : -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
      - α * (5 + α) * z * Work.Spaces.pz Ψ z θ + Work.Elliptic.Lzero Ψ z θ = F z θ :=
    h.eq z hz θ hθ.1 hθ.2
  have hid : Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
      = F z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by
    have hLz : Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Work.Elliptic.Lzero Ψ z θ := rfl
    rw [hLz, hbs] at *
    linarith
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hS0), hid]
  have h3 : 0 ≤ 3 * (((F z θ) ^ 2
      + ((α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) ^ 2
      + ((α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2) * SS θ) := by positivity
  have h4 : (F z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
      + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2
      ≤ 3 * ((F z θ) ^ 2 + ((α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        + ((α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2) := by
    nlinarith [sq_nonneg (F z θ - (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ),
      sq_nonneg ((α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ),
      sq_nonneg ((α * (5 + α) * z) * Work.Spaces.pz Ψ z θ - F z θ)]
  nlinarith [h4, hS0]

/-- **Gluing the two endpoint limits.**  A function that is continuous on the open interval,
vanishes at the two endpoints and has the two one-sided limits `0` there is continuous on the
closed interval. -/
theorem ws_continuousOn_Icc {u : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2))) (h0 : u 0 = 0)
    (hpi : u (Real.pi / 2) = 0)
    (hl : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hr : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) := by
  have key0 : Filter.Tendsto u (nhdsWithin 0 (Set.Icc (0 : ℝ) (Real.pi / 2))) (nhds 0) := by
    have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioc 0 (Real.pi / 2) ∪ ({0} : Set ℝ) := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · exact Or.inr h.symm
      · exact Or.inl ⟨h, hx.2⟩
    have h1 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioc 0 (Real.pi / 2)) ⊔ pure 0) (nhds 0) :=
      Filter.Tendsto.sup (hl.mono_left (nhdsWithin_mono 0 (fun x hx => hx.1)))
        (by simpa [h0] using tendsto_pure_nhds u 0)
    have h2 : nhdsWithin 0 (Set.Icc (0 : ℝ) (Real.pi / 2))
        ≤ nhdsWithin 0 (Set.Ioc 0 (Real.pi / 2)) ⊔ pure 0 := by
      have h3 := nhdsWithin_mono (0 : ℝ) hsub
      rwa [nhdsWithin_union, nhdsWithin_singleton] at h3
    exact h1.mono_left h2
  have keypi : Filter.Tendsto u
      (nhdsWithin (Real.pi / 2) (Set.Icc (0 : ℝ) (Real.pi / 2))) (nhds 0) := by
    have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ico 0 (Real.pi / 2) ∪ ({Real.pi / 2} : Set ℝ) := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨hx.1, h⟩
    have h1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Ico 0 (Real.pi / 2))
        ⊔ pure (Real.pi / 2)) (nhds 0) :=
      Filter.Tendsto.sup (hr.mono_left (nhdsWithin_mono (Real.pi / 2) (fun x hx => hx.2)))
        (by simpa [hpi] using tendsto_pure_nhds u (Real.pi / 2))
    have h2 : nhdsWithin (Real.pi / 2) (Set.Icc (0 : ℝ) (Real.pi / 2))
        ≤ nhdsWithin (Real.pi / 2) (Set.Ico 0 (Real.pi / 2)) ⊔ pure (Real.pi / 2) := by
      have h3 := nhdsWithin_mono (Real.pi / 2) hsub
      rwa [nhdsWithin_union, nhdsWithin_singleton] at h3
    exact h1.mono_left h2
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0
    show Filter.Tendsto u (nhdsWithin 0 (Set.Icc (0 : ℝ) (Real.pi / 2))) (nhds (u 0))
    rw [h0]
    exact key0
  rcases eq_or_lt_of_le hx.2 with hxpi | hxpi
  · rw [hxpi]
    show Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Icc (0 : ℝ) (Real.pi / 2)))
      (nhds (u (Real.pi / 2)))
    rw [hpi]
    exact keypi
  · exact (hu.continuousAt (isOpen_Ioo.mem_nhds ⟨hx0, hxpi⟩)).continuousWithinAt

theorem weakSliceRegular (k : ℕ) (hk : 1 ≤ k) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ z, 0 < z →
        ContinuousOn (fun θ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) ∧
        Ψ z 0 = 0 ∧ Ψ z (Real.pi / 2) = 0 ∧
        (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 ∧
        MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => Ψ z t) θ) ^ 2)
          Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn
          (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h z hz
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hsm : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hΨ hz
  -- conjunct 7
  have h7 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 * SS θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice (hΨ.pth).pth h.memB 0 (by omega) hz
  -- conjuncts 5 and 6, from the boundedness of the slice and of its derivative
  obtain ⟨C, hCpos, hC⟩ := abs_le_of_sq_mul_sEta hsm (by simpa using h7)
  have h5 : MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := C ^ 2)
        (Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) (by simp))
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ hz).pow 2) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : 0 ≤ (C - Ψ z θ) * (C + Ψ z θ) :=
      mul_nonneg (by linarith [le_abs_self (Ψ z θ), (hC θ hθ).2])
        (by linarith [neg_le_abs (Ψ z θ), (hC θ hθ).2])
    nlinarith [h1]
  have h6 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => Ψ z t) θ) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := C ^ 2)
        (Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) (by simp))
      ((measurable_deriv (fun t => Ψ z t)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : 0 ≤ (C - deriv (fun t => Ψ z t) θ) * (C + deriv (fun t => Ψ z t) θ) :=
      mul_nonneg (by linarith [le_abs_self (deriv (fun t => Ψ z t) θ), (hC θ hθ).1])
        (by linarith [neg_le_abs (deriv (fun t => Ψ z t) θ), (hC θ hθ).1])
    nlinarith [h1]
  -- the `L¹`-hypothesis of the two endpoint limits
  have hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) ^ 2 * SS θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_Lzero1_energy_integrable hα hk h hz
  -- the moment identity for the left endpoint
  have hmom : (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * Work.Elliptic.sinCos2 θ) = 0 :=
    (Work.FTS.EllipticEst.remov.wsMomentIdentity h hk
      (Work.FTS.EllipticEst.remov.wsMomentChain α k F Ψ hα hk h)
      (fun z' hz' => by
        have hpz := Work.FTS.EllipticEst.remov.ws_pz_energy_integrable
          (α := α) (k := k) (F := F) hk h hz'
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Work.Spaces.pz Ψ z' θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
          (Work.FTS.EllipticEst.remov.ws_absMoment
            (Work.FTS.EllipticEst.remov.ws_aesm_slice (hΨ.pz) hz') hpz).1
        exact (h1.const_mul z').congr
          (Filter.Eventually.of_forall (fun θ => by
            simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
            ring))
      )
      (fun z' hz' θ hθ' => Work.FTS.EllipticEst.remov.DzIter_two_eq hΨ hz' hθ'))
      z hz
  refine ⟨?_, h.zero z, h.pi_half z, ?_, h5, h6, h7⟩
  · exact Work.FTS.EllipticEst.remov.ws_continuousOn_Icc
      hsm.continuousOn
      (h.zero z) (h.pi_half z)
      (Work.FTS.EllipticEst.remov.wsSliceLeft hsm h7 hL hmom)
      (sliceTendstoRight_fts hsm h7 hL h5)
  · have := h.orthPsi z hz
    simpa only [Work.Elliptic.Fstar] using this

end

end Work.FTS.EllipticEst.remov
