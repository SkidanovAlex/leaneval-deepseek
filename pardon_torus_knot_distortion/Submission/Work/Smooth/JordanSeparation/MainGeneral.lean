import Submission.Work.Smooth.JordanSeparation.AtMostTwoGeneral

/-!
# Jordan separation for a `C¹` simple closed curve, modulo the non-separation of a subarc

`AtMostTwoGeneral.lean` reduces the "at most two components" half for a `C¹` simple closed curve to
the classical statement that a proper subcontinuum of the curve does not separate the plane
(`NoSeparationOfSubcontinuum`).  This file packages the resulting separation theorem, together with
the two index values, in the form used by the sibling chapter `Submission/Work/Smooth/Jordan`.

The hypothesis `NoSeparationOfSubcontinuum c` follows from the classical theorem that an arc does
not separate the plane: a proper subcontinuum of the trace of a simple closed curve is a point or an
arc, and neither separates.
-/

open Set Metric
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The plane is not separated by a proper subcontinuum of the curve.**  This is the classical
statement that a point, or an arc, does not separate the plane (here for subcontinua of the trace of
a simple closed curve). -/
def NoSeparationOfSubcontinuum (c : SmoothPlaneCurve) : Prop :=
  ∀ S : Set ℂ, S ⊆ c.trace → IsConnected S → IsCompact S → S ≠ c.trace → IsPathConnected Sᶜ

/-- The hypothesis of `atMostTwo_of_no_separation` in the packaged form. -/
theorem atMostTwo_of_noSeparation (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    (hArc : NoSeparationOfSubcontinuum c) :
    ∀ x y z : ℂ, x ∉ c.trace → y ∉ c.trace → z ∉ c.trace →
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ y ∨
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ z ∨
      connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z :=
  atMostTwo_of_no_separation c hs hArc

/-- **Jordan separation for a `C¹` simple closed curve**, given the non-separation of proper
subcontinua. -/
theorem jordanSeparation_of_noSeparation (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    (hArc : NoSeparationOfSubcontinuum c) :
    Nonempty (PlaneSeparation c.toPlaneCurve) :=
  nonempty_planeSeparation c.toPlaneCurve hs (atMostTwo_of_noSeparation c hs hArc)
    (exists_two_components_of_isSimple c hs)

/-- The index vanishes on the unbounded side of any separation of a `C¹` simple closed curve. -/
theorem ind_eq_zero_of_mem_U_noSeparation (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {x : ℂ} (hx : x ∈ S.U) : ind c x = 0 :=
  ind_eq_zero_of_mem_U_of_isSimple c hs hx

/-- The index has modulus one on the bounded side. -/
theorem ind_abs_eq_one_of_mem_V_noSeparation (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {y : ℂ} (hy : y ∈ S.V) : |ind c y| = 1 :=
  ind_abs_eq_one_of_mem_V_of_isSimple c hs hy

/-- **`JordanInput` for `C¹` simple closed curves**, given the non-separation of proper
subcontinua. -/
theorem jordanInput_of_contDiff_noSeparation (γ : ℝ → ℂ) (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hdiff : ContDiff ℝ 1 γ)
    (hsimp : (⟨γ, hcont, hper⟩ : PlaneCurve).IsSimple)
    (hArc : NoSeparationOfSubcontinuum
      { γ := γ, cont := hcont, periodic := hper, contDiff := hdiff }) :
    Nonempty (PlaneSeparation (⟨γ, hcont, hper⟩ : PlaneCurve)) := by
  by_cases himm : ∀ t, deriv γ t ≠ 0
  · exact planeSeparation_of_contDiff (⟨γ, hcont, hper⟩ : PlaneCurve) hdiff himm hsimp
  · exact jordanSeparation_of_noSeparation
      { γ := γ, cont := hcont, periodic := hper, contDiff := hdiff } hsimp hArc

end

end Work.Smooth.JordanSeparation
