import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Calculus

open MeasureTheory Filter
open scoped Topology

/-- Newton--Leibniz for the upper limit of a halfline integral, with continuity in place of
smoothness: if `f` is continuous, integrable and eventually vanishes at `+∞`, then
`x ↦ ∫_{s > x} f s` has derivative `-f x`. -/
theorem hasDerivAt_integral_Ioi_of_continuous (f : ℝ → ℝ) (hfcont : Continuous f)
    (hfint : Integrable f) (hvanish : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → f x = 0) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ s in Set.Ioi x, f s) (-(f t)) t := by
  obtain ⟨R, hR⟩ := hvanish
  set R' : ℝ := max R t with hR'def
  have hRle : R ≤ R' := le_max_left _ _
  have hIoiR' : ∫ s in Set.Ioi R', f s = 0 := by
    have h : ∫ s in Set.Ioi R', f s = ∫ s in Set.Ioi R', (0 : ℝ) :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun s hs => hR s (le_trans hRle (le_of_lt hs)))
    simpa using h
  have hfun : (fun x : ℝ => ∫ s in Set.Ioi x, f s) = fun x : ℝ => ∫ s in x..R', f s := by
    funext x
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (μ := volume) (f := f) (a := x) (b := R')
      hfint.integrableOn hfint.integrableOn
    rw [hIoiR', sub_zero] at h
    exact h
  rw [hfun]
  exact intervalIntegral.integral_hasDerivAt_left (hfcont.intervalIntegrable t R')
    (hfcont.stronglyMeasurableAtFilter volume (𝓝 t)) hfcont.continuousAt

end Commons.Analysis.Calculus