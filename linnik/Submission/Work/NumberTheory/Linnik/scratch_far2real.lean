import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_absorb
import Submission.Work.NumberTheory.Linnik.scratch_farreal

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false

namespace Commons.NumberTheory.Linnik

/-- **HB (6.14), real-valued version.**  There is `L₀ ≥ 1` such that for `L ≥ L₀`,
`|a| ≤ loglog L/3` and `(δ/2)L ≤ |η|`, the Laplace transform of the (complexified) real test
function at `z = a + iη` has modulus at most `ε`. -/
theorem far_term_le_real {x₀ B δ : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hδ : 0 < δ) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀,
      ‖iteratedDeriv 2 (fun t : ℝ => ((f t : ℝ) : ℂ)) t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ {a η L : ℝ}, L₀ ≤ L → 1 ≤ L →
      |a| ≤ Real.log (Real.log L) / 3 → δ / 2 * L ≤ |η| →
      ‖∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((a : ℂ) + (η : ℂ) * Complex.I)) * (t : ℂ))) * ((f t : ℝ) : ℂ)‖
        ≤ ε := by
  obtain ⟨L₀, hL₀1, hL₀⟩ := far_absorb (x₀ := x₀) (δ := δ) (K := ‖((f 0 : ℝ) : ℂ)‖)
    (C := 2 * ‖derivWithin (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Ioi 0) 0‖ + 2 * B * x₀)
    hx₀ hδ (norm_nonneg _) (by positivity) hε
  refine ⟨max L₀ 1, le_max_right _ _, ?_⟩
  intro a η L hL hL1 ha hη
  have hL₀le : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hfar := laplace_far_le_real hx₀ hB hδ hLpos hcont hf2 hBnd hvan
    (M := Real.log (Real.log L) / 3) ha hη
  have habs := hL₀ L hL₀le
  linarith [hfar, habs]

end Commons.NumberTheory.Linnik
