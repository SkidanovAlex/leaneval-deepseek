import Mathlib
import Submission.Work.LinnikAreas.TuranOther.orderInvGammaR_eq_indicator

namespace Work.LinnikAreas.turanAux2

/-!
# The order of vanishing of `1 / Γ_ℝ(· + a)`

We transport the unshifted computation `orderInvGammaR_eq_indicator` (the reciprocal of
`Γ_ℝ` has a simple zero exactly at `-2n`, `n : ℕ`, and vanishes nowhere else) along the
translation `z ↦ z + a`.  A translation has derivative `1 ≠ 0`, so it preserves the
analytic order of vanishing; hence `(Γ_ℝ(· + a))⁻¹` has a simple zero exactly at the
points `-(a + 2n)`, `n : ℕ`, and vanishes nowhere else. -/

theorem gammaROrderShift (a : ℕ) (u : ℂ) :
    analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u
      = (Set.range (fun n : ℕ => -(((a + 2 * n : ℕ) : ℂ)))).indicator (fun _ => (1 : ℕ)) u := by
  -- A translation preserves the order of vanishing (its derivative is `1 ≠ 0`).
  have hcomp : analyticOrderAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u
      = analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) (u + (a:ℂ)) := by
    have h := analyticOrderAt_comp_of_deriv_ne_zero
      (f := fun s : ℂ => (Complex.Gammaℝ s)⁻¹) (g := fun z : ℂ => z + (a:ℂ)) (z₀ := u)
      (by fun_prop) (by rw [deriv_add_const]; simp)
    simpa only [Function.comp_def] using h
  have hnat : analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u
      = analyticOrderNatAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) (u + (a:ℂ)) := by
    simp only [analyticOrderNatAt, hcomp]
  rw [hnat, Work.LinnikAreas.TuranOther.orderInvGammaR_eq_indicator (u + (a:ℂ))]
  -- `u + a = -2n` for some `n` iff `u = -(a + 2n)` for the same `n`.
  have hiff : (u + (a:ℂ)) ∈ Set.range (fun n : ℕ => -(((2*n : ℕ) : ℂ)))
      ↔ u ∈ Set.range (fun n : ℕ => -(((a + 2*n : ℕ) : ℂ))) := by
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hu : u = -(((2*n:ℕ):ℂ)) - (a:ℂ) := eq_sub_of_add_eq hn.symm
      rw [hu]; push_cast; ring
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [← hn]; push_cast; ring
  by_cases h : u ∈ Set.range (fun n : ℕ => -(((a + 2*n : ℕ) : ℂ)))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mp hc))]

end Work.LinnikAreas.turanAux2
