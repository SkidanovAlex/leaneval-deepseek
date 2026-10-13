import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory

/-- A function with an *everywhere* derivative `deriv φ` on the open interval `(a,b)` whose
derivative is integrable there is bounded on `(a,b)`: the total variation
`∫_{(a,b)} |φ'|` is finite, so `φ` is absolutely continuous and extends continuously to the
closed interval.  (Nothing is assumed off `(a,b)`: only the values of `deriv φ` on `(a,b)`
enter the hypotheses and the conclusion.) -/
theorem bdd_of_integrableOn_deriv {a b : ℝ} (hab : a < b) {φ : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt φ (deriv φ x) x)
    (hint : MeasureTheory.IntegrableOn (deriv φ) (Set.Ioo a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo a b, |φ θ| ≤ C := by
  -- A reference point in the interior and the total variation of the derivative.
  set c : ℝ := (a + b) / 2 with hcdef
  have hac : a < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  set M : ℝ := ∫ x in Set.Ioo a b, |deriv φ x| with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => abs_nonneg (deriv φ x))
  have hIntAbs : IntegrableOn (fun x => |deriv φ x|) (Set.Ioo a b) := by
    simpa only [Real.norm_eq_abs, IntegrableOn] using hint.abs
  -- On the whole interval, `φ` moves by at most the total variation of its derivative.
  have key : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, x ≤ y → |φ y - φ x| ≤ M := by
    intro x hx y hy hxy
    have hsubIcc : Set.uIcc x y ⊆ Set.Ioo a b := by
      rw [Set.uIcc_of_le hxy]
      intro t ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    have hsub1 : Set.Ioc x y ⊆ Set.Ioo a b := fun t ht =>
      ⟨lt_trans hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    have hsub2 : Set.Ioc y x ⊆ Set.Ioo a b := fun t ht =>
      ⟨lt_trans hy.1 ht.1, lt_of_le_of_lt ht.2 hx.2⟩
    have hInt : MeasureTheory.IntegrableOn (deriv φ) (Set.Ioc x y) := hint.mono_set hsub1
    have hInt' : MeasureTheory.IntegrableOn (deriv φ) (Set.Ioc y x) := hint.mono_set hsub2
    have hftc : ∫ t in x..y, deriv φ t = φ y - φ x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := φ)
        (fun t ht => hderiv t (hsubIcc ht)) ⟨hInt, hInt'⟩
    have hMI : ∫ t in x..y, |deriv φ t| ≤ M := by
      rw [hMdef, intervalIntegral.integral_of_le hxy]
      refine setIntegral_mono_set hIntAbs
        (Filter.Eventually.of_forall fun t => abs_nonneg (deriv φ t)) ?_
      filter_upwards with t ht
      exact ⟨lt_trans hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    calc |φ y - φ x| = |∫ t in x..y, deriv φ t| := by rw [hftc]
      _ ≤ ∫ t in x..y, |deriv φ t| := intervalIntegral.abs_integral_le_integral_abs hxy
      _ ≤ M := hMI
  have key' : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, |φ y - φ x| ≤ M := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · exact key x hx y hy hxy
    · rw [abs_sub_comm]
      exact key y hy x hx hyx
  refine ⟨|φ c| + M, add_nonneg (abs_nonneg (φ c)) hMnn, ?_⟩
  intro θ hθ
  have h1 : |φ θ - φ c| ≤ M := key' c ⟨hac, hcb⟩ θ hθ
  calc |φ θ| = |φ c + (φ θ - φ c)| := by rw [show φ c + (φ θ - φ c) = φ θ by ring]
    _ ≤ |φ c| + |φ θ - φ c| := abs_add_le _ _
    _ ≤ |φ c| + M := add_le_add le_rfl h1

end Work.FTS.EllipticEst.Honest
