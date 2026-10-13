import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta

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
