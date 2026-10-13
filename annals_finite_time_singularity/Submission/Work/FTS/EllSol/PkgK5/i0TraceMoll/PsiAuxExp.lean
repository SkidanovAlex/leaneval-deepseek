/-
# `PsiAuxExp` — auxiliary facts for the `PsiFacts` development

Two reusable facts:

* the mollifying kernel `sKer δ` is bounded by its prefactor `|(δ · sMass)⁻¹|`, and it
  vanishes off the interval `(log z - δ, log z + δ)` (so every `t`-integral weighted by
  `sKer δ (log z - t)` is supported there);
* the dominating function `MGf G` of the angular slice is integrable in the *logarithmic*
  radial variable: `t ↦ MGf G (e^t)` is integrable on every bounded interval, whenever
  `MGf G` is integrable on compact subintervals of `(0,∞)` (which is what
  `Work.FTS.EllSol.EllPkgAux.mollSliceBound` gives from `TraceClass G` and `FourInts G`).

The second fact is the `t`-variable form of the slice domination used by the Fatou step of
the mollification transfer; it is what allows the doubled-odd extension to be dominated by an
integrable function of `t` in the dominated-convergence arguments for the endpoint limits of
`Work.FTS.EllSol.PkgK5.i0TraceMoll.Psi`.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.i0TraceMoll

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The kernel: boundedness and support -/

/-- **The mollifying kernel is bounded by its prefactor.** -/
theorem abs_sKer_le {δ : ℝ} (t : ℝ) :
    |Work.FTS.EllSol.PkgK5.K5c.sKer δ t|
      ≤ |(δ * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹| := by
  rw [Work.FTS.EllSol.PkgK5.K5c.sKer, abs_mul,
    abs_of_nonneg (Work.FTS.EllSol.PkgK5.K5c.sBump_nonneg (t / δ))]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (Work.FTS.EllSol.PkgK5.K5c.sBump_le_one (t / δ))

/-- **The support of `t ↦ sKer δ (log z - t)` is contained in `(log z - δ, log z + δ)`.** -/
theorem sKer_log_sub_eq_zero {δ z t : ℝ} (hδ : 0 < δ)
    (ht : t ∉ Set.Ioo (Real.log z - δ) (Real.log z + δ)) :
    Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) = 0 := by
  by_cases h : t ≤ Real.log z - δ
  · have h1 : δ ≤ Real.log z - t := by linarith
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ
      (le_trans h1 (le_abs_self _))
  · have h2 : Real.log z + δ ≤ t := by
      by_contra hc
      exact ht ⟨not_le.mp h, not_le.mp hc⟩
    have h1 : δ ≤ t - Real.log z := by linarith
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ
      (le_trans h1 (by rw [abs_sub_comm]; exact le_abs_self _))

/-! ## Integrability of the slice domination in the logarithmic variable -/

/-- **`t ↦ MGf G (e^t)` is integrable on bounded intervals**, from the local integrability of
`MGf G` on compact subintervals of `(0,∞)`.  The substitution rule for `t ↦ e^t` (whose
derivative is bounded below by `e^a > 0` on `(a,b)`) converts the interval `(a,b)` into
`(e^a, e^b)`. -/
theorem integrableOn_MGf_exp (G : ℝ → ℝ → ℝ)
    (hint : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MGf G) (Set.Icc a b))
    {a b : ℝ} (hab : a < b) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (Set.Ioo a b) := by
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (f := Real.exp) (f' := fun x => Real.exp x) (g := Work.FTS.EllSol.EllPkgAux.MGf G)
    (a := a) (b := b)
    (by fun_prop) (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
  have hR : IntervalIntegrable (Work.FTS.EllSol.EllPkgAux.MGf G) volume (Real.exp a)
      (Real.exp b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (le_of_lt (Real.exp_lt_exp.mpr hab))).mpr
      ((hint (Real.exp a) (Real.exp b) (Real.exp_pos a)
        (le_of_lt (Real.exp_lt_exp.mpr hab))).mono_set Set.Ioo_subset_Icc_self)
  have hL : IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * Real.exp t)
      (Set.Ioo a b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hab)).mp (hiff.mpr hR)
  have hMGnn : ∀ w : ℝ, 0 ≤ Work.FTS.EllSol.EllPkgAux.MGf G w := by
    intro w
    have h2 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := Real.sqrt_nonneg _
    simp only [Work.FTS.EllSol.EllPkgAux.MGf]
    linarith
  rw [IntegrableOn] at hL ⊢
  have h2 : Integrable (fun t : ℝ =>
      (Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * Real.exp t))
      (volume.restrict (Set.Ioo a b)) := hL.const_mul _
  refine h2.mono' ?_ ?_
  · have hcont : Continuous (fun t : ℝ => Real.exp a * (Real.exp t)⁻¹) :=
      continuous_const.mul (Real.continuous_exp.inv₀ (fun t => Real.exp_ne_zero t))
    refine (hcont.aestronglyMeasurable.mul h2.aestronglyMeasurable).congr ?_
    filter_upwards with t
    have ha : Real.exp a ≠ 0 := Real.exp_ne_zero a
    have ht : Real.exp t ≠ 0 := Real.exp_ne_zero t
    calc Real.exp a * (Real.exp t)⁻¹ * ((Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * Real.exp t))
        = (Real.exp t)⁻¹ * Real.exp t * (Real.exp a * (Real.exp a)⁻¹)
            * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) := by ring
      _ = Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) := by
          rw [inv_mul_cancel₀ ht, mul_inv_cancel₀ ha]; ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hpa : 0 < Real.exp a := Real.exp_pos a
    have hlt : Real.exp a < Real.exp t := Real.exp_lt_exp.mpr ht.1
    have hge : 1 ≤ Real.exp t / Real.exp a := (one_le_div hpa).mpr hlt.le
    rw [Real.norm_of_nonneg (hMGnn _)]
    calc Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)
        = Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * 1 := by ring
      _ ≤ Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * (Real.exp t / Real.exp a) :=
          mul_le_mul_of_nonneg_left hge (hMGnn _)
      _ = (Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * Real.exp t) := by ring

/-- The `TraceClass`/`FourInts` form of `integrableOn_MGf_exp`, via `mollSliceBound`. -/
theorem integrableOn_MGf_exp_of_trace (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (hF : Work.FTS.EllSol.EllPkgAux.FourInts G)
    {a b : ℝ} (hab : a < b) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (Set.Ioo a b) := by
  obtain ⟨C, hC, hbound⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
  exact integrableOn_MGf_exp G (fun _ _ ha hab' => (hbound G hT hF).2 _ _ ha hab') hab

end Work.FTS.EllSol.PkgK5.i0TraceMoll
