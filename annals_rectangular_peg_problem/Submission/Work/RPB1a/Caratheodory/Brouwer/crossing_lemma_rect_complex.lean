import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_paths

namespace Work.RPB1a.Caratheodory.Brouwer

/-- **Crossing statement for the rectangle `[-1,1] × [-2,2]`, in complex coordinates.**

A path `h` joining the left side (`re = -1`) to the right side (`re = 1`) of the rectangle and a path
`v` joining the bottom side (`im = -2`) to the top side (`im = 2`), both mapping `[-1,1]` into the
rectangle, must meet.  This is `crossing_lemma_paths` rescaled by the map `(x,y) ↦ (x, y/2)`. -/
theorem crossing_lemma_rect_complex {h v : ℝ → ℂ} (hh : Continuous h) (hv : Continuous v)
    (hhm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(h t).re| ≤ 1 ∧ |(h t).im| ≤ 2)
    (hvm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(v t).re| ≤ 1 ∧ |(v t).im| ≤ 2)
    (hh_left : (h (-1)).re = -1) (hh_right : (h 1).re = 1)
    (hv_bot : (v (-1)).im = -2) (hv_top : (v 1).im = 2) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1, ∃ t ∈ Set.Icc (-1 : ℝ) 1, h s = v t := by
  -- The vertical coordinate is rescaled by the factor `2` so that the rectangle
  -- `[-1,1] × [-2,2]` becomes the square `[-1,1] × [-1,1]`.
  set H : ℝ → ℝ × ℝ := fun t => ((h t).re, (h t).im / 2) with hH
  set V : ℝ → ℝ × ℝ := fun t => ((v t).re, (v t).im / 2) with hV
  have hHcont : Continuous H := by
    rw [hH]
    exact (Complex.continuous_re.comp hh).prodMk ((Complex.continuous_im.comp hh).div_const 2)
  have hVcont : Continuous V := by
    rw [hV]
    exact (Complex.continuous_re.comp hv).prodMk ((Complex.continuous_im.comp hv).div_const 2)
  have hHmem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, H t ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hhm t ht
    rw [Set.mem_prod]
    constructor
    · change (h t).re ∈ Set.Icc (-1 : ℝ) 1
      exact abs_le.mp h1
    · change (h t).im / 2 ∈ Set.Icc (-1 : ℝ) 1
      have h3 : |(h t).im / 2| ≤ 1 := by
        rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
        linarith
      exact abs_le.mp h3
  have hVmem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, V t ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hvm t ht
    rw [Set.mem_prod]
    constructor
    · change (v t).re ∈ Set.Icc (-1 : ℝ) 1
      exact abs_le.mp h1
    · change (v t).im / 2 ∈ Set.Icc (-1 : ℝ) 1
      have h3 : |(v t).im / 2| ≤ 1 := by
        rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
        linarith
      exact abs_le.mp h3
  have hHleft : (H (-1)).1 = -1 := by
    change (h (-1)).re = -1
    exact hh_left
  have hHright : (H 1).1 = 1 := by
    change (h 1).re = 1
    exact hh_right
  have hVbot : (V (-1)).2 = -1 := by
    change (v (-1)).im / 2 = -1
    rw [hv_bot]; norm_num
  have hVtop : (V 1).2 = 1 := by
    change (v 1).im / 2 = 1
    rw [hv_top]; norm_num
  obtain ⟨s, hs, t, ht, hst⟩ :=
    crossing_lemma_paths hHcont hVcont hHmem hVmem hHleft hHright hVbot hVtop
  refine ⟨s, hs, t, ht, ?_⟩
  have e1 : (h s).re = (v t).re := by
    have := congrArg Prod.fst hst
    simpa only [hH, hV] using this
  have e2 : (h s).im / 2 = (v t).im / 2 := by
    have := congrArg Prod.snd hst
    simpa only [hH, hV] using this
  have e2' : (h s).im = (v t).im :=
    (div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp e2
  exact Complex.ext e1 e2'

end Work.RPB1a.Caratheodory.Brouwer
