import Mathlib
import Submission.Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp

namespace Work.LinnikAreas.Density4

open MeasureTheory

/-- The vertical line `t ↦ c + t * I` meets the set of non-positive integers at most at `t = 0`,
so the composition with `Complex.Gamma` is measurable. -/
theorem measurable_gamma_vertical (c : ℝ) :
    Measurable (fun t : ℝ => Complex.Gamma (c + (t : ℂ) * Complex.I)) := by
  refine measurable_of_continuousOn_compl_singleton (0 : ℝ) ?_
  intro t ht
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
  have hne : ∀ m : ℕ, c + (t : ℂ) * Complex.I ≠ -(m : ℂ) := by
    intro m hm
    have him : (c + (t : ℂ) * Complex.I).im = (-(m : ℂ)).im := by rw [hm]
    simp at him
    exact ht him
  have hline : ContinuousAt (fun s : ℝ => c + (s : ℂ) * Complex.I) t := by fun_prop
  have hcomp : ContinuousAt (fun s : ℝ => Complex.Gamma (c + (s : ℂ) * Complex.I)) t :=
    (Complex.continuousAt_Gamma (c + (t : ℂ) * Complex.I) hne).tendsto.comp hline.tendsto
  exact hcomp.continuousWithinAt

theorem gamma_vertical_integrable_of_bound (c : ℝ) (C : ℝ) (hC : 0 < C)
    (h : ∀ t : ℝ, ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ c * Real.exp (-(Real.pi / 2) * |t|)) :
    MeasureTheory.Integrable (fun t : ℝ => Complex.Gamma (c + (t : ℂ) * Complex.I)) := by
  have hbase : MeasureTheory.Integrable
      (fun t : ℝ => (1 + |t|) ^ c * Real.exp (-(Real.pi / 2 * |t|))) :=
    integrable_one_add_abs_rpow_exp c (Real.pi / 2) (by positivity)
  have hg : MeasureTheory.Integrable
      (fun t : ℝ => C * ((1 + |t|) ^ c * Real.exp (-(Real.pi / 2 * |t|)))) :=
    hbase.const_mul C
  refine hg.mono' (measurable_gamma_vertical c).aestronglyMeasurable ?_
  filter_upwards with t
  calc ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖
      ≤ C * (1 + |t|) ^ c * Real.exp (-(Real.pi / 2) * |t|) := h t
    _ = C * ((1 + |t|) ^ c * Real.exp (-(Real.pi / 2 * |t|))) := by ring_nf

end Work.LinnikAreas.Density4
