import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
The endpoint value `deriv f x` of a `C²` function near the left endpoint of `(0,t)`, `t ≤ π/2`,
is bounded as soon as the second derivative is square-integrable on `(0,t)`.

The mathematics is one line: for `0 < x < t` and any fixed `a ∈ (0,t)` the fundamental theorem of
calculus gives `deriv f x - deriv f a = ∫_a^x deriv (deriv f)`, and since `(deriv (deriv f))²` is
integrable on `(0,t)` the derivative `deriv (deriv f)` is integrable there (`|y| ≤ y² + 1`), so
the difference is bounded by `∫_{(0,t)} |deriv (deriv f)|` — an absolute constant.  In particular
the possible blow-up of `deriv f` at the *right* endpoint `t` is irrelevant: the same estimate
only uses that both `x` and the reference point `a = t/2` lie in `(0,t)`.
-/

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open MeasureTheory Set Filter
open scoped Topology

/-- Elementary inequality: `|x| ≤ x ^ 2 + 1` for every real `x`. -/
theorem abs_le_sq_add_one_aux (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg (|x| - 1 / 2), abs_nonneg x, sq_abs x]

theorem derivBoundedNearLeft {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hta : t ≤ Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv (deriv f) x) ^ 2) (Set.Ioo 0 t)) :
    ∃ M, ∀ x ∈ Set.Ioo 0 t, |deriv f x| ≤ M := by
  have hIopen : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  -- the interval of interest sits inside the domain of smoothness
  have hsub : Set.Ioo (0 : ℝ) t ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hta⟩
  -- `deriv f` is `C¹`, so `deriv (deriv f)` is continuous on the open interval
  have hg1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.deriv_of_isOpen hIopen (by norm_num)
  have hcont : ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hg1.continuousOn_deriv_of_isOpen hIopen le_rfl
  have hmeas : AEStronglyMeasurable (deriv (deriv f)) (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioo
  -- `deriv (deriv f)` is integrable on `(0,t)`, because `|y| ≤ y² + 1` there
  have hsum : IntegrableOn (fun x : ℝ => (deriv (deriv f) x) ^ 2 + 1) (Set.Ioo 0 t) :=
    h2.add (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
  have habs : IntegrableOn (fun x : ℝ => |deriv (deriv f) x|) (Set.Ioo 0 t) := by
    refine Integrable.mono' hsum hmeas.norm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_le_sq_add_one_aux (deriv (deriv f) x)
  have hint : IntegrableOn (fun x : ℝ => deriv (deriv f) x) (Set.Ioo 0 t) := by
    refine (MeasureTheory.integrable_norm_iff hmeas).mp ?_
    simpa only [Real.norm_eq_abs, IntegrableOn] using habs
  -- the explicit bound
  refine ⟨|deriv f (t / 2)| + ∫ y in Set.Ioo (0 : ℝ) t, |deriv (deriv f) y|, ?_⟩
  intro x hx
  have ha : (t / 2) ∈ Set.Ioo (0 : ℝ) t := ⟨by linarith, by linarith⟩
  -- differentiability of `deriv f` on `(0,t)`, with derivative `deriv (deriv f)`
  have hmem : ∀ y ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (deriv f) (deriv (deriv f) y) y := by
    intro y hy
    exact ((hg1.differentiableOn_one).differentiableAt
      (Ioo_mem_nhds (hsub hy).1 (hsub hy).2)).hasDerivAt
  have hsubIcc : Set.uIcc (t / 2) x ⊆ Set.Ioo (0 : ℝ) t := by
    intro y hy
    rw [Set.mem_uIcc] at hy
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [ha.1, h1], by linarith [h2, hx.2]⟩
    · exact ⟨by linarith [hx.1, h1], by linarith [h2, ha.2]⟩
  have hIoc1 : Set.Ioc (t / 2) x ⊆ Set.Ioo (0 : ℝ) t := by
    intro y hy
    rw [Set.mem_Ioc] at hy
    exact ⟨lt_trans ha.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
  have hIoc2 : Set.Ioc x (t / 2) ⊆ Set.Ioo (0 : ℝ) t := by
    intro y hy
    rw [Set.mem_Ioc] at hy
    exact ⟨lt_trans hx.1 hy.1, lt_of_le_of_lt hy.2 ha.2⟩
  have hInt : IntervalIntegrable (deriv (deriv f)) volume (t / 2) x :=
    ⟨hint.mono_set hIoc1, hint.mono_set hIoc2⟩
  -- fundamental theorem of calculus on `[t/2, x]`
  have hFTC : ∫ y in (t / 2)..x, deriv (deriv f) y = deriv f x - deriv f (t / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hmem y (hsubIcc hy)) hInt
  -- the absolute value of that integral is bounded by the full `L¹` mass of `deriv (deriv f)`
  have hbound : |deriv f x - deriv f (t / 2)| ≤
      ∫ y in Set.Ioo (0 : ℝ) t, |deriv (deriv f) y| := by
    rw [← hFTC]
    rcases le_total (t / 2) x with hle | hle
    · have h3 : |∫ y in (t / 2)..x, deriv (deriv f) y| ≤
          ∫ y in (t / 2)..x, |deriv (deriv f) y| :=
        intervalIntegral.abs_integral_le_integral_abs hle
      have h4 : ∫ y in (t / 2)..x, |deriv (deriv f) y| ≤
          ∫ y in Set.Ioo (0 : ℝ) t, |deriv (deriv f) y| := by
        rw [intervalIntegral.integral_of_le hle]
        refine MeasureTheory.setIntegral_mono_set habs (ae_of_all _ fun y => abs_nonneg _) ?_
        filter_upwards with y hy
        exact hIoc1 hy
      exact h3.trans h4
    · have h3 : |∫ y in (t / 2)..x, deriv (deriv f) y| ≤
          ∫ y in x..(t / 2), |deriv (deriv f) y| := by
        rw [intervalIntegral.integral_symm x (t / 2), abs_neg]
        exact intervalIntegral.abs_integral_le_integral_abs hle
      have h4 : ∫ y in x..(t / 2), |deriv (deriv f) y| ≤
          ∫ y in Set.Ioo (0 : ℝ) t, |deriv (deriv f) y| := by
        rw [intervalIntegral.integral_of_le hle]
        refine MeasureTheory.setIntegral_mono_set habs (ae_of_all _ fun y => abs_nonneg _) ?_
        filter_upwards with y hy
        exact hIoc2 hy
      exact h3.trans h4
  have hsplit : |deriv f x| ≤ |deriv f x - deriv f (t / 2)| + |deriv f (t / 2)| := by
    have h := abs_add_le (deriv f x - deriv f (t / 2)) (deriv f (t / 2))
    rwa [sub_add_cancel] at h
  linarith

end Work.EllipticEst.Core.i0Aux.EndpointValues
