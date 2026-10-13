/-
Copyright: work module for the Elgindi finite-time singularity project.

# The left endpoint of a slice with weighted-square-integrable second derivative

This module proves `Work.FTS.EllipticEst.sliceLimitLeftExists`: a function `u` of class
`C^n` on `(0, π/2)` for every `n`, whose second derivative satisfies the *weighted*
square-integrability hypothesis

  `∫_{Iθ} (u'')² · sEta < ∞`,   `sEta θ = sin(2θ)^{-η}`,   `η = 99/100`,

has a finite limit at `0⁺`.

The mathematical point is that although the weight `sEta` blows up like `θ^{-η}` at `0`, the
exponent is `η < 1`, so `sEta^{-1} = sin(2θ)^{η}` is *bounded* on `Iθ`.  In fact on the open
interval `(0, π/2)` one has `sin(2θ) ≤ 1`, hence `sEta ≥ 1` there, so the hypothesis is at least
as strong as plain `L¹`-integrability of `(u'')²` on `(0, π/2)`:

* `(u'')² ∈ L¹(0, π/2)`, hence `|u''| ∈ L¹(0, π/2)`;
* Newton–Leibniz on `[θ, π/4]` (`θ ∈ (0, π/4)`) bounds `|u' θ|` by `|u' (π/4)|` plus the total
  mass of `|u''|`, so `u'` is bounded on `(0, π/4)` and therefore `u' ∈ L¹(0, π/4)`;
* `exists_tendsto_nhdsGT_zero_of_integrableOn_deriv` (integrable derivative ⟹ limit at `0⁺`)
  finishes.

The main statement is stated exactly as requested; the auxiliary lemmas above it are the
elementary pieces of the argument.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Topology

/-! ## Auxiliary estimates -/

/-- **`sEta ≥ 1` on `(0, π/2)`.**  There `0 < sin(2θ) ≤ 1` and the exponent `-η` of the weight
`sEta θ = sin(2θ)^{-η}` is nonpositive, so the weight is at least `1`. -/
lemma sliceLim_one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ sEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one (2 * θ)
  have hz : -(Work.Spaces.eta) ≤ 0 := by
    have het : (0 : ℝ) ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    linarith
  have h := Real.rpow_le_rpow_of_nonpos hpos hle hz
  simpa [sEta, Real.one_rpow] using h

/-- **First transfer of integrability.**  Since `sEta ≥ 1` on `(0, π/2)`, the weighted
square-integrability hypothesis for `u''` implies plain square-integrability of `u''`. -/
lemma sliceLim_integrableOn_sq_of_integrableOn_mul_sEta (u : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hint.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  refine MeasureTheory.Integrable.mono' hI ?_ ?_
  · exact ((measurable_deriv (fun t : ℝ => deriv u t)).pow_const 2).aestronglyMeasurable
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
      have hsq : 0 ≤ (deriv (fun t : ℝ => deriv u t) θ) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hsq]
      nlinarith [sliceLim_one_le_sEta hθ, hsq])

/-- **Second transfer of integrability.**  `|x| ≤ x² + 1` turns square-integrability of `u''`
into integrability of `|u''|` (the interval has finite measure). -/
lemma sliceLim_integrableOn_abs_of_integrableOn_sq (u : ℝ → ℝ)
    (h : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 + 1)
      (Set.Ioo 0 (Real.pi / 2)) :=
    h.add (MeasureTheory.integrableOn_const (C := (1 : ℝ))
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (by simp))
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · simpa only [Real.norm_eq_abs] using
      (measurable_deriv (fun t : ℝ => deriv u t)).norm.aestronglyMeasurable
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => by
      have hnn : 0 ≤ |deriv (fun t : ℝ => deriv u t) θ| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      by_cases h1 : |deriv (fun t : ℝ => deriv u t) θ| ≤ 1
      · nlinarith [sq_nonneg (deriv (fun t : ℝ => deriv u t) θ)]
      · push_neg at h1
        nlinarith [sq_abs (deriv (fun t : ℝ => deriv u t) θ), h1,
          abs_nonneg (deriv (fun t : ℝ => deriv u t) θ)])

/-- **Newton–Leibniz bound.**  If `f` has derivative `f'` on the whole closed interval
`[a, b]` and `f'` is integrable there, then for `a ≤ c ≤ b` the increment of `f` from `a` to `c`
is bounded by the mass of `|f'|` on `(a, c]`. -/
lemma sliceLim_abs_sub_le_setIntegral {f f' : ℝ → ℝ} {a b c : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Icc a b) volume) :
    |f c - f a| ≤ ∫ x in Set.Ioc a c, |f' x| := by
  have hsub : Set.Ioc a c ⊆ Set.Icc a b := fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 hcb⟩
  have hInt : IntervalIntegrable f' volume a c :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mpr (hint.mono_set hsub)
  have hFTC : ∫ x in a..c, f' x = f c - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x (by
      rw [Set.uIcc_of_le hac] at hx
      exact ⟨hx.1, le_trans hx.2 hcb⟩)) hInt
  have hnorm : |∫ x in a..c, f' x| ≤ ∫ x in a..c, |f' x| := by
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (μ := volume) hac (f := f')
  rw [← hFTC]
  exact hnorm.trans (le_of_eq (intervalIntegral.integral_of_le hac))

/-- **Boundedness of `u'` on `(0, π/4)`.**  If `u''` (written out as
`deriv (fun t => deriv u t)`) is the derivative of `u'` on `(0, π/2)` and `|u''|` is integrable
there, then for `θ ∈ (0, π/4)` the value `|u' θ|` is bounded by `|u' (π/4)|` plus the total mass
of `|u''|` on `(0, π/2)`. -/
lemma sliceLim_abs_deriv_le_of_second_deriv_integrableOn {u : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4))
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x)
    (hg : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    |deriv u θ| ≤ |deriv u (Real.pi / 4)|
      + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s| := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hle : θ ≤ Real.pi / 4 := le_of_lt hθ1
  have hsub : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 hq⟩
  have hIcc : MeasureTheory.IntegrableOn
      (fun x : ℝ => |deriv (fun t : ℝ => deriv u t) x|) (Set.Icc θ (Real.pi / 4)) :=
    hg.mono_set hsub
  have hint : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => deriv u t))
      (Set.Icc θ (Real.pi / 4)) :=
    MeasureTheory.Integrable.mono' hIcc (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs])
  have hmain := sliceLim_abs_sub_le_setIntegral (f := deriv u)
    (f' := deriv (fun t : ℝ => deriv u t))
    (a := θ) (b := Real.pi / 4) (c := Real.pi / 4) hle le_rfl
    (fun x hx => hderiv x (hsub hx)) hint
  have htri : |deriv u θ| ≤ |deriv u (Real.pi / 4)|
      + |deriv u (Real.pi / 4) - deriv u θ| := by
    have hid : deriv u θ = deriv u (Real.pi / 4) - (deriv u (Real.pi / 4) - deriv u θ) := by
      ring
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (deriv u (Real.pi / 4)),
        le_abs_self (deriv u (Real.pi / 4) - deriv u θ), hid]
    · linarith [le_abs_self (deriv u (Real.pi / 4)),
        neg_abs_le (deriv u (Real.pi / 4) - deriv u θ), hid]
  have hmono : ∫ x in Set.Ioc θ (Real.pi / 4), |deriv (fun t : ℝ => deriv u t) x|
      ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s| :=
    MeasureTheory.setIntegral_mono_set hg
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx =>
        ⟨lt_trans hθ0 hx.1, lt_of_le_of_lt hx.2 hq⟩)
  calc |deriv u θ|
      ≤ |deriv u (Real.pi / 4)| + |deriv u (Real.pi / 4) - deriv u θ| := htri
    _ ≤ |deriv u (Real.pi / 4)|
        + ∫ x in Set.Ioc θ (Real.pi / 4), |deriv (fun t : ℝ => deriv u t) x| := by
        linarith [hmain]
    _ ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s| := by
        linarith [hmono]

theorem sliceLimitLeftExists : ∀ (u : ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    ∃ L : ℝ, Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds L) := by
  intro u hsm hint
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- `u` and `u'` are differentiable on the open interval
  have hderiv1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u x) x := by
    intro x hx
    have h1 : ContDiffAt ℝ 1 u x := (hsm 1).contDiffAt (isOpen_Ioo.mem_nhds hx)
    exact (h1.differentiableAt (by norm_num)).hasDerivAt
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 u x := (hsm 2).contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  -- integrability of `(u'')²` and of `|u''|` on `(0, π/2)`
  have hsq : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u hint
  have habs : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  -- `u'` is bounded on `(0, π/4)`, hence integrable there
  have hderivu : MeasureTheory.IntegrableOn (deriv u) (Set.Ioo 0 (Real.pi / 4)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ (measurable_deriv u).aestronglyMeasurable
      (|deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s|) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
        rw [Real.norm_eq_abs]
        exact sliceLim_abs_deriv_le_of_second_deriv_integrableOn hθ hderiv2 habs)
  exact exists_tendsto_nhdsGT_zero_of_integrableOn_deriv hpi4
    (fun x hx => hderiv1 x ⟨hx.1, lt_of_lt_of_le hx.2 hpi4lt.le⟩) hderivu

end Work.FTS.EllipticEst
