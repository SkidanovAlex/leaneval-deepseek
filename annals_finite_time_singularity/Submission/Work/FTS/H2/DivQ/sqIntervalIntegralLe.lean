import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set

/-- **Cauchy–Schwarz (Bunyakovsky) for the interval integral.**  For `a ≤ b` and `f` with `f`
and `f²` interval-integrable on `[a,b]`,

  `(∫_a^b f)² ≤ (b - a) · ∫_a^b f²`.

The proof rewrites both sides as set integrals over `Ioc a b`
(`intervalIntegral.integral_of_le`), notes that `f` is square integrable there
(`intervalIntegrable_iff_integrableOn_Ioc_of_le` + `memLp_two_iff_integrable_sq`) and that the
constant function `1` is too (`intervalIntegrable_const` + `memLp_two_iff_integrable_sq`), applies
the abstract Cauchy–Schwarz inequality `Work.Spaces.cs_integral` to `u = f`, `v = 1`, and evaluates
`∫ x in a..b, 1 = b - a` with `intervalIntegral.integral_const`. -/
theorem sqIntervalIntegralLe (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) MeasureTheory.volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  have hF1 : Integrable f (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf
  have hF2 : Integrable (fun x : ℝ => f x ^ 2) (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf2
  have hmf : MemLp f 2 (volume.restrict (Ioc a b)) :=
    (memLp_two_iff_integrable_sq hF1.aestronglyMeasurable).mpr hF2
  have hm1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioc a b)) := by
    refine (memLp_two_iff_integrable_sq (f := fun _ : ℝ => (1 : ℝ)) aestronglyMeasurable_const).mpr ?_
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp intervalIntegrable_const
  have h := Work.Spaces.cs_integral hmf hm1
  have e1 : (∫ x in Ioc a b, f x * (fun _ : ℝ => (1 : ℝ)) x) = ∫ x in a..b, f x := by
    rw [← intervalIntegral.integral_of_le hab]
    simp
  have e2 : (∫ x in Ioc a b, f x ^ 2) = ∫ x in a..b, f x ^ 2 := by
    rw [← intervalIntegral.integral_of_le (f := fun x : ℝ => f x ^ 2) hab]
  have e3 : (∫ x in Ioc a b, (fun _ : ℝ => (1 : ℝ)) x ^ 2) = b - a := by
    have hpt : (fun x : ℝ => (fun _ : ℝ => (1 : ℝ)) x ^ 2) = fun _ : ℝ => (1 : ℝ) := by
      funext x
      norm_num
    rw [hpt, ← intervalIntegral.integral_of_le (f := fun _ : ℝ => (1 : ℝ)) hab,
      intervalIntegral.integral_const]
    simp
  rw [e1, e2, e3] at h
  calc (∫ x in a..b, f x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (b - a) := h
    _ = (b - a) * ∫ x in a..b, f x ^ 2 := by ring

end Work.FTS.H2.DivQ
