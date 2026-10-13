import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open MeasureTheory Set
open scoped Real

/-- **A function with an integrable derivative is bounded.**

If `F` has derivative `f'` at every point of the open interval `(0, π/2)` and `f'` is
integrable on `Iθ = [0, π/2]`, then `F` is bounded on `(0, π/2)`.

The mechanism is the fundamental theorem of calculus: for interior points `a < b` of the
interval the increment is the integral of `f'`, hence bounded by the (finite) integral of
`|f'|` over the whole interval; anchoring at the fixed interior point `π/4` bounds `F`
everywhere by `|F (π/4)| + ∫_{Ioc 0 (π/2)} |f'|`. -/
theorem ftcBoundOfIntegrableDeriv {F f' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt F (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' Work.Spaces.Iθ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Ioo 0 (Real.pi / 2), |F x| ≤ M := by
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- unfold the domain of integrability
  have hIcc : MeasureTheory.IntegrableOn f' (Set.Icc 0 (Real.pi / 2)) := by
    have hIθ : Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) := rfl
    rwa [hIθ] at hint
  have hAbsIcc : MeasureTheory.IntegrableOn (fun t => |f' t|) (Set.Icc 0 (Real.pi / 2)) := by
    change Integrable (fun t => |f' t|) (volume.restrict (Set.Icc 0 (Real.pi / 2)))
    simpa only [Real.norm_eq_abs] using hIcc.norm
  have hAbs : MeasureTheory.IntegrableOn (fun t => |f' t|) (Set.Ioc 0 (Real.pi / 2)) :=
    hAbsIcc.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  -- interval integrability on any subinterval of `[0, π/2]`
  have hInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable f' volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hIcc.mono_set (fun x hx => ⟨le_of_lt (lt_of_le_of_lt ha hx.1), le_trans hx.2 hb⟩)
  set L : ℝ := ∫ t in Set.Ioc (0 : ℝ) (Real.pi / 2), |f' t| with hL
  have hL0 : 0 ≤ L := by
    rw [hL]; exact setIntegral_nonneg measurableSet_Ioc (fun t _ => abs_nonneg (f' t))
  refine ⟨|F (Real.pi / 4)| + L, add_nonneg (abs_nonneg _) hL0, ?_⟩
  -- the FTC bound for any pair of interior points `a ≤ b`
  have hkey : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < Real.pi / 2 → |F b - F a| ≤ L := by
    intro a b ha hab hb
    have hderiv' : ∀ t ∈ Set.uIcc a b, HasDerivAt F (f' t) t := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hderiv t ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
    have hint' : IntervalIntegrable f' volume a b := hInt ha.le hab hb.le
    have hftc : ∫ t in a..b, f' t = F b - F a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hint'
    have h1 : |F b - F a| ≤ ∫ t in a..b, |f' t| := by
      rw [← hftc]; exact intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ t in a..b, |f' t|) ≤ L := by
      rw [hL, intervalIntegral.integral_of_le hab]
      refine setIntegral_mono_set hAbs (Filter.Eventually.of_forall fun t => abs_nonneg _)
        (Filter.Eventually.of_forall fun t ht =>
          ⟨lt_trans ha ht.1, le_of_lt (lt_of_le_of_lt ht.2 hb)⟩)
    linarith
  -- anchor every point at `π/4`
  intro x hx
  rcases le_total x (Real.pi / 4) with hle | hle
  · have h := hkey hx.1 hle hπ4lt
    calc |F x| = |F (Real.pi / 4) + (F x - F (Real.pi / 4))| := by ring_nf
      _ ≤ |F (Real.pi / 4)| + |F x - F (Real.pi / 4)| := abs_add_le _ _
      _ = |F (Real.pi / 4)| + |F (Real.pi / 4) - F x| := by rw [abs_sub_comm]
      _ ≤ |F (Real.pi / 4)| + L := by linarith
  · have h := hkey hπ4 hle hx.2
    calc |F x| = |F x - F (Real.pi / 4) + F (Real.pi / 4)| := by ring_nf
      _ ≤ |F x - F (Real.pi / 4)| + |F (Real.pi / 4)| := abs_add_le _ _
      _ ≤ L + |F (Real.pi / 4)| := by linarith
      _ = |F (Real.pi / 4)| + L := by ring

end Work.FTS.EllipticEst.remov.SourceBound
