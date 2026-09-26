import Submission.Work.Smooth.JordanSeparation.subcontinuum_trace_interval
import Submission.Work.Smooth.JordanSeparation.arc_not_separate
import Submission.Work.Smooth.JordanSeparation.MainGeneral

/-!
# A proper subcontinuum of a simple closed curve does not separate the plane

`Work.Smooth.JordanSeparation.NoSeparationOfSubcontinuum` (in `MainGeneral.lean`) is the classical
statement that a proper subcontinuum of the trace of a `C¹` simple closed plane curve does not
separate the plane.  It is the *only* remaining hypothesis of the chapter's separation theorem for
non-immersed `C¹` curves (`jordanSeparation_of_noSeparation`), and this file **discharges it**.

The proof has two pieces, both already available:

* `Work.Smooth.JordanSeparation.subcontinuum_trace_interval` — a compact connected proper subset
  `S` of the trace of a simple closed curve is the image of a closed parameter interval
  `[a, b]` of length `< 2π`;
* `Work.Smooth.JordanSeparation.arc_not_separate` — an arc (the image of a closed interval under a
  continuous injective map) does not separate the plane: its complement is path connected.

The only point to check is that `c.γ` *is* injective on `[a, b]`, which follows from
`PlaneCurve.IsSimple.eq_mod_period` and `b - a < 2π`.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **Simplicity on a short interval.**  A simple closed curve with period `2π` is injective on
every closed parameter interval of length `< 2π`.  (Two parameters at which the curve agrees differ
by a multiple `k · 2π` of the period; the multiple lies in `(-1, 1)`, hence is `0`.) -/
theorem injOn_Icc_of_lt_period {c : PlaneCurve} (hs : c.IsSimple)
    {a b : ℝ} (_hab : a ≤ b) (hlt : b - a < 2 * Real.pi) : Set.InjOn c.γ (Set.Icc a b) := by
  intro s hs' t ht' hst
  obtain ⟨k, hk⟩ := hs.eq_mod_period hst
  have hle : |t - s| ≤ b - a := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ht'.2, hs'.1], by linarith [hs'.2, ht'.1]⟩
  have hk' : t - s = (k : ℝ) * (2 * Real.pi) := by linarith [hk]
  have hlt' : |t - s| < 2 * Real.pi := lt_of_le_of_lt hle hlt
  rw [hk'] at hlt'
  have hk0 : k = 0 := int_eq_zero_of_mul_two_pi_abs_lt k hlt'
  rw [hk0, Int.cast_zero, zero_mul, add_zero] at hk
  linarith [hk]

/-- **A proper subcontinuum of a simple closed curve does not separate the plane**, stated for a
plane curve (no smoothness needed). -/
theorem noSeparationOfSubcontinuum_of_planeCurve (c : PlaneCurve) (hs : c.IsSimple) :
    ∀ S : Set ℂ, S ⊆ c.trace → IsConnected S → IsCompact S → S ≠ c.trace →
      IsPathConnected Sᶜ := by
  intro S hS hSc hScomp hSne
  obtain ⟨a, b, hab, hlt, hSeq⟩ :=
    subcontinuum_trace_interval c hs hS hSc hScomp hSne
  rw [hSeq]
  exact arc_not_separate c.cont (injOn_Icc_of_lt_period hs hab hlt)

/-- **A proper subcontinuum of a simple closed curve does not separate the plane.**  This is
`Work.Smooth.JordanSeparation.NoSeparationOfSubcontinuum`, now a theorem: the hypothesis of
`jordanSeparation_of_noSeparation` is discharged. -/
theorem noSeparationOfSubcontinuum (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple) :
    NoSeparationOfSubcontinuum c :=
  noSeparationOfSubcontinuum_of_planeCurve c.toPlaneCurve hs

end

end Work.Smooth.JordanSeparation
