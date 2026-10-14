import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv_const
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Boundedness of a slice from the `σ`-weighted `L²`-norm of its second derivative

`σ θ = sin(2θ)^{-η}` (`η = 99/100`) is `≥ 1` on the interior of `Iθ = [0, π/2]`, so the
hypothesis `∫_{Iθ} (u'')² σ < ∞` is *stronger* than the plain square-integrability of `u''`:
it forces `∫_{Iθ} |u''| < ∞`.  The fundamental theorem of calculus on the open interval
`(0, π/2)` then bounds `u'` (and, once more, `u`) by the values at the interior point `π/4`
plus that finite `L¹`-norm.  Nothing is assumed at the endpoints: `u` may blow up there.
-/

/-- The absolute value of an interval integral over a subinterval of `(0, π/2)` is bounded by
the set integral of the absolute value over `Iθ`. -/
theorem abs_intervalIntegral_le_setIntegral_Iθ {f : ℝ → ℝ} {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hI : IntervalIntegrable (fun x => |f x|) volume 0 (Real.pi / 2)) :
    |∫ x in a..b, f x| ≤ ∫ x in Work.Spaces.Iθ, |f x| := by
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |f x|) = ∫ x in Work.Spaces.Iθ, |f x| := by
    rw [intervalIntegral.integral_of_le (by positivity), Work.Spaces.Iθ,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rcases le_total a b with hh | hh
  · exact le_trans (intervalIntegral.abs_integral_le_integral_abs hh) (by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval ha.1.le hh hb.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hI)
  · rw [intervalIntegral.integral_symm b a, abs_neg]
    exact le_trans (intervalIntegral.abs_integral_le_integral_abs hh) (by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hb.1.le hh ha.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hI)

/-- **Slicewise boundedness from the `σ`-weighted `L²`-bound on `u''`.**
If `u` is `C²` on the open interval `(0, π/2)` and `∫_{Iθ} (u'')² σ < ∞`, then `u` and `u'`
are bounded on `(0, π/2)`, with a constant depending on `u`. -/
theorem slice_bdd_of_sq_mul_sEta {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C ∧ |deriv u θ| ≤ C := by
  have hpi4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  -- `u''` is continuous on the open interval, so `σ ≥ 1` and the hypothesis give `∫|u''| < ∞`.
  have hcont : ContinuousOn (fun θ : ℝ => deriv (fun t : ℝ => deriv u t) θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 : ContDiffOn ℝ 0 (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h2.continuousOn
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hcont hint
  have hIi : IntervalIntegrable
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|) volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact habs.mono_set Set.Ioc_subset_Icc_self
  -- the finite bound on `u'`
  set B : ℝ := |deriv u (Real.pi / 4)|
    + ∫ t in Work.Spaces.Iθ, |deriv (fun s : ℝ => deriv u s) t| with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h := integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun t : ℝ => |deriv (fun s : ℝ => deriv u s) t|) (fun t => abs_nonneg _)
    linarith [abs_nonneg (deriv u (Real.pi / 4))]
  have hseg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  -- the bound for `u'`: integrate `u''` from `π/4` to `θ`
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
          have := abs_intervalIntegral_le_setIntegral_Iθ hpi4 hθ hIi
          linarith
      _ = B := by rw [hBdef]
  -- the bound for `u`: integrate `u'` from `π/4` to `θ`, using the bound on `u'`
  refine ⟨max B (|u (Real.pi / 4)| + B * (Real.pi / 2)),
    le_trans hB0 (le_max_left _ _), ?_⟩
  intro θ hθ
  constructor
  · have hc0 : ContDiffOn ℝ 1 u (Set.uIcc (Real.pi / 4) θ) :=
      (hsm.of_le (by norm_num)).mono (hseg θ hθ)
    have hFTC : (∫ t in (Real.pi / 4)..θ, deriv u t) = u θ - u (Real.pi / 4) :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc hc0
    have hval : u θ = u (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, deriv u t := by
      linarith [hFTC]
    have hbnd : ∀ x ∈ Set.uIoc (Real.pi / 4) θ, ‖deriv u x‖ ≤ B := by
      intro x hx
      rw [Real.norm_eq_abs]
      rw [Set.mem_uIoc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hpthle x ⟨lt_of_lt_of_le hpi4.1 (le_of_lt h1), lt_of_le_of_lt h2 hθ.2⟩
      · exact hpthle x ⟨lt_of_lt_of_le hθ.1 (le_of_lt h1), lt_of_le_of_lt h2 hpi4.2⟩
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    have hdist : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    have hstep : |∫ t in (Real.pi / 4)..θ, deriv u t| ≤ B * |θ - Real.pi / 4| := by
      rw [← Real.norm_eq_abs]
      exact hnorm
    calc |u θ| = |u (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, deriv u t| := by rw [hval]
      _ ≤ |u (Real.pi / 4)| + |∫ t in (Real.pi / 4)..θ, deriv u t| := abs_add_le _ _
      _ ≤ |u (Real.pi / 4)| + B * |θ - Real.pi / 4| := by linarith
      _ ≤ |u (Real.pi / 4)| + B * (Real.pi / 2) := by
          have := mul_le_mul_of_nonneg_left hdist hB0
          linarith
      _ ≤ max B (|u (Real.pi / 4)| + B * (Real.pi / 2)) := le_max_right _ _
  · exact le_trans (hpthle θ hθ) (le_max_left _ _)

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.pzIter_uncurry_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst

open Set

/-- The angular interval `[0,π/2]` is contained in the open interval on which
`SmoothNbhd` gives smoothness in the `θ`-variable. -/
theorem Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (π / 2 + 1) := by
  intro θ hθ
  obtain ⟨h0, h1⟩ := hθ
  exact ⟨by linarith, by linarith⟩

/-- `∂_z^k u` is jointly continuous on the half-open rectangle `(-1,∞) × [0,π/2]`
whenever `u` is smooth on a neighbourhood of the closed quadrant. -/
theorem continuousOn_uncurry_pzIter {u : ℝ → ℝ → ℝ} (hu : Work.Spaces.SmoothNbhd u)
    (k : ℕ) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter k u))
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
  ((Work.Spaces.smoothNbhd_pzIter hu k).continuousOn).mono
    (Set.prod_mono Subset.rfl Iθ_subset_Ioo)

theorem pzIter_uncurry_continuousOn (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) (k : ℕ) :
    ContinuousOn (Function.uncurry fun z θ => Work.Spaces.pzIter k u z θ * φ θ)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := by
  have hpz := continuousOn_uncurry_pzIter hu k
  have hφ' : ContinuousOn (fun p : ℝ × ℝ => φ p.2) (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
    hφ.comp continuous_snd.continuousOn fun p hp => hp.2
  exact hpz.mul hφ'

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.H2.STBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Auxiliary: the `𝒲^{l,∞}`-norm is nonnegative -/

theorem WlInf_nonneg {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} (hW : Spaces.WlInfMem α l f) :
    0 ≤ Spaces.WlInf α l f := by
  rw [Spaces.WlInf]
  exact add_nonneg (Spaces.wlZSum_nonneg α l f hW) (Spaces.wlThSum_nonneg α l f hW)

/-! ## Joint smoothness of the iterated `z`-partials -/





/-- A function vanishing at a fixed `θ` has all its `z`-derivatives vanishing there. -/
theorem pzIter_eq_zero_of_slice_zero {f : ℝ → ℝ → ℝ} {θ₀ : ℝ} (h : ∀ z, f z θ₀ = 0)
    (m : ℕ) (z : ℝ) : Spaces.pzIter m f z θ₀ = 0 := by
  induction m generalizing z with
  | zero => exact h z
  | succ n ih =>
      rw [Spaces.pzIter_succ, Spaces.pz]
      have : (fun z' => Spaces.pzIter n f z' θ₀) = fun _ => (0 : ℝ) := funext ih
      rw [this, deriv_const]

/-! ## The mean value bound on the `z`-difference quotient -/




/-! ## Continuity and `θ`-differentiability of the slices at interior points -/








/-- Triangle inequality in the form `|x - y| ≤ |x| + |y|`. -/
theorem abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.sin_weight_hardy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The `sin(2θ)`-weighted Hardy inequality on `[0,π/2]`

For `0 < β ≤ 1` and `φ` of class `C¹` on `[0,π/2]`,

* `∫_0^{π/2} φ² sin(2θ)^{β-1} ≤ (400/β²)(∫_0^{π/2} (φ')² sin(2θ)^{1-β} + φ(π/4)²)`,
* `∫_0^{π/2} φ² sin(2θ)^{β} ≤ 400 (∫_0^{π/2} (φ')² sin(2θ)^{1-β} + φ(π/4)²)`.

The two weights `sin(2θ)^{β-1}` and `sin(2θ)^{1-β}` are reciprocal, so the first inequality is the
weighted Hardy inequality with a boundary term at the *interior* point `θ = π/4`; the second is
its `L²`-counterpart with the (bounded) weight `sin(2θ)^β`.

The proof splits `(0,π/2)` at `π/4` and on each half uses the *power* weighted Hardy inequality
`power_hardy_boundary` together with Jordan's inequality `(4/π)θ ≤ sin(2θ) ≤ 1` on `[0,π/4]`
(and its mirror image on `[π/4,π/2]`, via `θ ↦ π/2 - θ`, under which `sin 2θ` is invariant).
-/

/-! ## Elementary pointwise facts on `[0,π/4]` -/

theorem four_div_pi_mul_le_sin_two (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 4)) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h2 : (2 / Real.pi) * (2 * θ) ≤ Real.sin (2 * θ) :=
    Real.mul_le_sin (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : (4 / Real.pi) * θ = (2 / Real.pi) * (2 * θ) := by ring
  rwa [hc]

theorem theta_le_quarter_sin_two (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 4)) :
    θ ≤ Real.pi / 4 * Real.sin (2 * θ) := by
  have h2 : (2 / Real.pi) * (2 * θ) ≤ Real.sin (2 * θ) :=
    Real.mul_le_sin (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : (Real.pi / 4) * ((2 / Real.pi) * (2 * θ)) = θ := by
    field_simp
    ring
  calc θ = (Real.pi / 4) * ((2 / Real.pi) * (2 * θ)) := hc.symm
    _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem sin_two_pos_of_quarter {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ)^{β-1} ≤ (4/π)^{β-1} θ^{β-1}` on `(0,π/4]` for `β ≤ 1`. -/
theorem sin_rpow_sub_le_theta {β θ : ℝ} (hβ1 : β ≤ 1) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ (β - 1) ≤ (4 / Real.pi) ^ (β - 1) * θ ^ (β - 1) := by
  have hJ : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) :=
    four_div_pi_mul_le_sin_two θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hpos : 0 < (4 / Real.pi) * θ := by
    have h0 := hθ.1
    positivity
  have h1 : (Real.sin (2 * θ)) ^ (β - 1) ≤ ((4 / Real.pi) * θ) ^ (β - 1) :=
    Real.rpow_le_rpow_of_nonpos hpos hJ (by linarith)
  rwa [Real.mul_rpow (by positivity) (le_of_lt hθ.1)] at h1

/-- `θ^{β+1} ≤ (π/4)^{β+1} sin(2θ)^{1-β}` on `(0,π/4]` for `0 ≤ β`. -/
theorem theta_rpow_le_sin_rpow {β θ : ℝ} (hβ : 0 ≤ β) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    θ ^ (β + 1) ≤ (Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (1 - β) := by
  have hle := theta_le_quarter_sin_two θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin_pos : 0 < Real.sin (2 * θ) := sin_two_pos_of_quarter hθ
  have h1 : θ ^ (β + 1) ≤ (Real.pi / 4 * Real.sin (2 * θ)) ^ (β + 1) :=
    Real.rpow_le_rpow (le_of_lt hθ.1) hle (by linarith)
  rw [Real.mul_rpow (by positivity) (le_of_lt hsin_pos)] at h1
  have h2 : (Real.sin (2 * θ)) ^ (β + 1) ≤ (Real.sin (2 * θ)) ^ (1 - β) :=
    Real.rpow_le_rpow_of_exponent_ge hsin_pos (Real.sin_le_one _) (by linarith)
  calc θ ^ (β + 1) ≤ (Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (β + 1) := h1
    _ ≤ (Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (1 - β) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by positivity) _)



/-! ## Integrability helpers -/






/-- Interval integrals do not see the endpoints: `F = G` on `Ioo a b` suffices. -/
theorem integral_congr_Ioo {a b : ℝ} (hab : a ≤ b) {F G : ℝ → ℝ}
    (h : ∀ x ∈ Set.Ioo a b, F x = G x) :
    (∫ x in a..b, F x) = ∫ x in a..b, G x := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (Set.Finite.measure_zero (Set.finite_singleton b) volume)
  intro x hx
  simp only [Set.mem_setOf_eq, not_imp] at hx
  obtain ⟨hxin, hne⟩ := hx
  rw [Set.uIoc_of_le hab, Set.mem_Ioc] at hxin
  by_contra hxb
  have hxb' : x ≠ b := by simpa using hxb
  exact hne (h x ⟨hxin.1, lt_of_le_of_ne hxin.2 hxb'⟩)

/-! ## The mirror `θ ↦ π/2 - θ` -/

/-- The mirror substitution. -/
theorem integral_mirror_sub (g : ℝ → ℝ) :
    (∫ u in (0:ℝ)..(Real.pi / 4), g (Real.pi / 2 - u))
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), g θ := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := Real.pi / 4) g
    (Real.pi / 2)
  rw [show (Real.pi / 2 - Real.pi / 4 : ℝ) = Real.pi / 4 by ring,
    show (Real.pi / 2 - 0 : ℝ) = Real.pi / 2 by ring] at h
  exact h



/-- The mirror identity for the `f²`-integral (`sin 2θ` is invariant under `θ ↦ π/2 - θ`). -/
theorem mirror_sq_sin_rpow (p : ℝ) (f : ℝ → ℝ) :
    (∫ u in (0:ℝ)..(Real.pi / 4), (f (Real.pi / 2 - u)) ^ 2 * (Real.sin (2 * u)) ^ p)
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ p := by
  rw [← integral_mirror_sub (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ p)]
  exact intervalIntegral.integral_congr (fun u _ => by
    rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u by ring, Real.sin_pi_sub])


/-! ## The numeric constants -/

/-- `(4/π)^{β-1}(π/4)^{β+1} = (π/4)²`. -/
theorem rpow_quarter_mul (β : ℝ) :
    (4 / Real.pi) ^ (β - 1) * (Real.pi / 4) ^ (β + 1) = (Real.pi / 4) ^ 2 := by
  have hp : (0:ℝ) < Real.pi / 4 := by positivity
  have h1 : (4 / Real.pi) = (Real.pi / 4)⁻¹ := (inv_div Real.pi 4).symm
  rw [h1, Real.inv_rpow (le_of_lt hp), ← Real.rpow_neg (le_of_lt hp) (β - 1),
    ← Real.rpow_add hp, show -(β - 1) + (β + 1) = 2 by ring, Real.rpow_two]

/-- `(4/π)^{β-1}(π/4)^{β} = π/4`. -/
theorem rpow_quarter_mul' (β : ℝ) :
    (4 / Real.pi) ^ (β - 1) * (Real.pi / 4) ^ β = Real.pi / 4 := by
  have hp : (0:ℝ) < Real.pi / 4 := by positivity
  have h1 : (4 / Real.pi) = (Real.pi / 4)⁻¹ := (inv_div Real.pi 4).symm
  rw [h1, Real.inv_rpow (le_of_lt hp), ← Real.rpow_neg (le_of_lt hp) (β - 1),
    ← Real.rpow_add hp, show -(β - 1) + β = 1 by ring, Real.rpow_one]

/-- `(4/π)^{β-1}·(4/β²)·(π/4)^{β+1} = (4/β²)·(π/4)²`. -/
theorem quarter_const_mul (β : ℝ) :
    (4 / Real.pi) ^ (β - 1) * (4 / β ^ 2) * (Real.pi / 4) ^ (β + 1)
      = 4 / β ^ 2 * (Real.pi / 4) ^ 2 := by
  rw [mul_comm ((4 / Real.pi) ^ (β - 1)) (4 / β ^ 2), mul_assoc, rpow_quarter_mul β]

/-- `(4/π)^{β-1}·(2/β)·(π/4)^{β} = π/(2β)`. -/
theorem bdry_const_mul {β : ℝ} (hβ : β ≠ 0) :
    (4 / Real.pi) ^ (β - 1) * (2 / β) * (Real.pi / 4) ^ β = Real.pi / (2 * β) := by
  rw [mul_comm ((4 / Real.pi) ^ (β - 1)) (2 / β), mul_assoc, rpow_quarter_mul' β]
  field_simp
  ring

/-! ## The two half-interval Hardy estimates on `[0,π/4]` -/



/-! ## The assembly -/



end Work.FTS.H2.Transport3Aux
end
end
-- ===== merged: Submission.Work.LWP.BiotSavart =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

variable {α : NNReal}

/-! ## The `C^{1,α}` closure of the Biot–Savart map -/



/-! ## The Biot–Savart law -/

/-- **Curl half of the Biot–Savart law**: `∇× (biotSavart ω) = ω` for divergence-free `ω`. -/
theorem vorticity_biotSavart (h : BiotSavartLaw) {ω : R3 → R3} (hint : Integrable ω)
    (hb : IsBoundedFun ω) (hdiv : ∀ x, div ω x = 0) (x : R3) :
    vorticity (biotSavart ω) x = ω x :=
  (h ω hint hb hdiv).1 x


/-! ## The odd/reflection clause -/

/-- **Reflection equivariance of the Biot–Savart map.**  A vorticity in the parity class
`IsOddVorticity` produces a reflection-invariant velocity field; together with axisymmetry this
is `IsOdd u` (see `Work.Cyl.isOdd_of_reflZ_invariant`).  This is the "odd" clause of the
Lichtenstein–Gunther class at the level of the Biot–Savart map. -/
theorem biotSavart_reflZ (h : BiotSavartReflection) {ω : R3 → R3} (hω : IsOddVorticity ω)
    (x : R3) : biotSavart ω (reflZ x) = flipZ (biotSavart ω x) :=
  h ω hω x


/-! ## The assembly's datum construction -/

/-- **The assembly's `EulerData` construction.**  If `ω₀` is `L¹`, bounded, `α`-Hölder and
divergence-free, if `u₀ = biotSavart ω₀` is odd (the parity clause, available for the
axisymmetric no-swirl class from `Work.Cyl`), and if `ω₀` decays like `‖x‖^{-α}`, then
`u₀ = biotSavart ω₀` is Lichtenstein–Gunther admissible data:
`div u₀ = 0`, `IsOdd u₀`, `IsContDiffHolder ℝ α u₀`, and `VorticityDecay α (vorticity u₀)`
(the last two by `BiotSavartLaw` and `BiotSavartSchauder`). -/
theorem eulerData_of_biotSavart {α : NNReal} (hS : BiotSavartSchauder α) (hLaw : BiotSavartLaw)
    {ω₀ : R3 → R3} (hint : Integrable ω₀) (hb : IsBoundedFun ω₀) (hh : Holder α ω₀)
    (hdiv : ∀ x, div ω₀ x = 0) (hodd : IsOdd (biotSavart ω₀))
    (hdec : VorticityDecay α ω₀) :
    EulerData α (biotSavart ω₀) :=
  ⟨funext (hLaw ω₀ hint hb hdiv).2, hodd, hS ω₀ hint hb hh hdiv,
   by rw [funext (hLaw ω₀ hint hb hdiv).1]; exact hdec⟩

/-- The Biot–Savart-compatible data (`EulerDataBS`) for the assembly's construction: for a
vorticity `ω₀` that is `L¹`, bounded, `α`-Hölder and divergence-free, the field
`biotSavart ω₀` has `L¹`, divergence-free, bounded, `α`-Hölder vorticity; the remaining decay
field of `EulerDataBS` is exactly the far-field statement of `farField_decay`. -/
theorem eulerDataBS_of_biotSavart {α : NNReal} (hLaw : BiotSavartLaw) {ω₀ : R3 → R3}
    (hint : Integrable ω₀) (hb : IsBoundedFun ω₀) (hh : Holder α ω₀)
    (hdiv : ∀ x, div ω₀ x = 0)
    (hdecay : ∃ C : ℝ, ∀ x : R3, ‖biotSavart ω₀ x‖ ≤ C / (1 + ‖x‖)) :
    EulerDataBS α (biotSavart ω₀) := by
  have h := hLaw ω₀ hint hb hdiv
  refine ⟨?_, ?_, ?_, ?_, hdecay⟩
  · rw [funext h.1]; exact hint
  · rw [funext h.1]; exact hdiv
  · rw [funext h.1]; exact hb
  · rw [funext h.1]; exact hh


/-- Boundedness of a field from a uniform bound on its norm. -/
theorem isBoundedFun_of_norm_le {ω : R3 → R3} {M : ℝ} (h : ∀ y, ‖ω y‖ ≤ M) :
    IsBoundedFun ω :=
  (Metric.isBounded_iff_subset_closedBall (0 : R3)).mpr ⟨M, fun y hy => by
    obtain ⟨x, -, rfl⟩ := hy
    simpa [Metric.mem_closedBall] using h x⟩

/-- **The assembly's `EulerDataBS`, fully automatic for compactly supported vorticity.**  If `ω₀`
is `L¹`, bounded by `M` and supported in `B(0,R)`, `α`-Hölder and divergence-free, then
`biotSavart ω₀` carries the whole Biot–Savart-compatible datum class; the decay field is
`Work.LWP.BiotSavart.exists_decay_of_compactSupport` (far-field decay plus the near-field bound),
so no decay hypothesis has to be supplied by hand. -/
theorem eulerDataBS_of_compactSupport {α : NNReal} (hLaw : BiotSavartLaw) {ω₀ : R3 → R3}
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hint : Integrable ω₀) (hω : ∀ y, ‖ω₀ y‖ ≤ M)
    (hh : Holder α ω₀) (hdiv : ∀ x, div ω₀ x = 0)
    (hsupp : ∀ y, ω₀ y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    EulerDataBS α (biotSavart ω₀) :=
  eulerDataBS_of_biotSavart hLaw hint (isBoundedFun_of_norm_le hω) hh hdiv
    (BiotSavart.exists_decay_of_compactSupport hR hM hω hsupp)

/-- **The self-consistency clause `hself` of `Work.LWP.local_existence`, automatically.**  For
`u₀ = biotSavart ω₀` with `vorticity u₀ = ω₀` (the Biot–Savart law), `u₀ = biotSavart (vorticity u₀)`
holds by rewriting. -/
theorem self_eq_biotSavart_of_biotSavart (hLaw : BiotSavartLaw) {ω₀ : R3 → R3}
    (hint : Integrable ω₀) (hb : IsBoundedFun ω₀) (hdiv : ∀ x, div ω₀ x = 0) :
    ∀ x, biotSavart ω₀ x = biotSavart (vorticity (biotSavart ω₀)) x := by
  have h := funext (hLaw ω₀ hint hb hdiv).1
  intro x
  rw [h]

end Work.LWP
end
-- ===== merged: Submission.Work.Spaces.sup_mixed_le_H4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- `VanishTheta` is preserved by iterated `D_z`-derivatives: the slice `θ ↦ DzIter n f z θ`
is identically zero at the two angular boundaries as soon as `f` is. -/
private lemma DzIter_vanish {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (n : ℕ) :
    VanishTheta (DzIter n f) := by
  induction n with
  | zero => exact h
  | succ m ih =>
      constructor
      · intro z
        have hfun : (fun z' => DzIter m f z' 0) = fun _ => (0 : ℝ) := funext ih.1
        simp [DzIter_succ, Dz, pz, hfun]
      · intro z
        have hfun : (fun z' => DzIter m f z' (π / 2)) = fun _ => (0 : ℝ) := funext ih.2
        simp [DzIter_succ, Dz, pz, hfun]

/-- Any positive iterate of `D_θ` already vanishes on the two angular boundaries
(`D_θ` carries the factor `sin(2θ)`). -/
private lemma DthIter_vanish_of_pos (f : ℝ → ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    VanishTheta (DthIter a f) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  constructor
  · intro z
    show Real.sin (2 * 0) * pth (DthIter a' f) z 0 = 0
    simp
  · intro z
    show Real.sin (2 * (π / 2)) * pth (DthIter a' f) z (π / 2) = 0
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- `VanishTheta` is preserved by mixed `D`-derivatives `D_z^b D_θ^a`. -/
private lemma VanishTheta_mixed {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (b a : ℕ) :
    VanishTheta (mixed b a f) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simpa [mixed] using DzIter_vanish h b
  · have h1 : VanishTheta (DthIter a f) := DthIter_vanish_of_pos f ha
    simpa [mixed] using DzIter_vanish h1 b


end Work.Spaces
end
end
