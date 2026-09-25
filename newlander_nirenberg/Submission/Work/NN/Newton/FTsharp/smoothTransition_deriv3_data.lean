/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Third derivative data for the smooth transition profile `Real.smoothTransition`

This extends `Work.NN.Core.Lev.smoothTransition_deriv_bounds` (which bounds `σ'` and `σ''` and
shows that both vanish on `(-∞,0]` and on `[1,∞)`) to the third derivative `σ'''`.

The facts recorded here are exactly what is needed to bound the third Fréchet derivative of the
rescaled profile `ζ ↦ σ ((b² - ‖ζ‖²)/(b² - a²))` (the parametric cutoff `Work.NN.Core.sharpCut`):
`σ'''` is bounded by a constant, and it vanishes on `(-∞,0]` and on `[1,∞)`.  The vanishing at
the endpoints `0` and `1` (where `σ'` and `σ''` are *not* locally constant) follows from
continuity of `σ'''` together with the vanishing of `σ''` on the corresponding half lines.
-/
import Mathlib
import Submission.Work.NN.Core.Lev.smoothTransition_deriv_data

noncomputable section

open scoped ContDiff Topology
open Function Filter

namespace Work.NN.Newton.FTsharp

/-- `σ''' = deriv (deriv (deriv σ))` is smooth. -/
lemma contDiff_deriv3_smoothTransition :
    ContDiff ℝ ∞ (deriv (deriv (deriv Real.smoothTransition))) := by
  have heq : deriv^[3] Real.smoothTransition = deriv (deriv (deriv Real.smoothTransition)) := by
    funext x; simp [Function.iterate_succ, Function.comp_apply]
  rw [← heq]
  exact ContDiff.iterate_deriv 3 (Work.NN.Core.Lev.contDiff_smoothTransition)

/-- `σ'''` has compact support: it is the derivative of the compactly supported `σ''`. -/
lemma hasCompactSupport_deriv3_smoothTransition :
    HasCompactSupport (deriv (deriv (deriv Real.smoothTransition))) :=
  Work.NN.Core.Lev.hasCompactSupport_deriv_deriv_smoothTransition.deriv

/-- `σ''' = 0` on `(-∞,0)`, where `σ''` is locally constant `0`. -/
lemma deriv3_eq_zero_of_lt_zero {t : ℝ} (ht : t < 0) :
    deriv (deriv (deriv Real.smoothTransition)) t = 0 := by
  have hev : deriv (deriv Real.smoothTransition) =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact Work.NN.Core.Lev.deriv_deriv_smoothTransition_eq_zero_of_nonpos hs.le
  rw [hev.deriv_eq]
  simp

/-- `σ''' = 0` on `(-∞,0]`: by continuity, since it vanishes on `(-∞,0)`. -/
lemma deriv3_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv (deriv (deriv Real.smoothTransition)) t = 0 := by
  rcases lt_or_eq_of_le ht with h | rfl
  · exact deriv3_eq_zero_of_lt_zero h
  · have h2 : Tendsto (deriv (deriv (deriv Real.smoothTransition))) (𝓝[<] (0 : ℝ))
        (𝓝 (deriv (deriv (deriv Real.smoothTransition)) 0)) :=
      contDiff_deriv3_smoothTransition.continuous.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have h1 : Tendsto (deriv (deriv (deriv Real.smoothTransition))) (𝓝[<] (0 : ℝ))
        (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (deriv3_eq_zero_of_lt_zero hs).symm)
    exact tendsto_nhds_unique h2 h1

/-- `σ''' = 0` on `(1,∞)`, where `σ''` is locally constant `0`. -/
lemma deriv3_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv (deriv (deriv Real.smoothTransition)) t = 0 := by
  have hev : deriv (deriv Real.smoothTransition) =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact Work.NN.Core.Lev.deriv_deriv_smoothTransition_eq_zero_of_one_le hs.le
  rw [hev.deriv_eq]
  simp

/-- `σ''' = 0` on `[1,∞)`: by continuity, since it vanishes on `(1,∞)`. -/
lemma deriv3_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv (deriv (deriv Real.smoothTransition)) t = 0 := by
  rcases lt_or_eq_of_le ht with h | rfl
  · exact deriv3_eq_zero_of_one_lt h
  · have h2 : Tendsto (deriv (deriv (deriv Real.smoothTransition))) (𝓝[>] (1 : ℝ))
        (𝓝 (deriv (deriv (deriv Real.smoothTransition)) 1)) :=
      contDiff_deriv3_smoothTransition.continuous.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have h1 : Tendsto (deriv (deriv (deriv Real.smoothTransition))) (𝓝[>] (1 : ℝ))
        (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (deriv3_eq_zero_of_one_lt hs).symm)
    exact tendsto_nhds_unique h2 h1

/-- **Third derivative data for the smooth transition profile.**

There is a constant `C₃ ≥ 0` bounding `|σ'''|`, and `σ'''` vanishes on `(-∞,0]` and on
`[1,∞)`. -/
theorem smoothTransition_deriv3_data :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧
      (∀ t : ℝ, |deriv (deriv (deriv Real.smoothTransition)) t| ≤ C₃) ∧
      (∀ t : ℝ, t ≤ 0 → deriv (deriv (deriv Real.smoothTransition)) t = 0) ∧
      (∀ t : ℝ, 1 ≤ t → deriv (deriv (deriv Real.smoothTransition)) t = 0) := by
  obtain ⟨A, hA⟩ := contDiff_deriv3_smoothTransition.continuous.bounded_above_of_compact_support
    hasCompactSupport_deriv3_smoothTransition
  refine ⟨max A 0, le_max_right _ _, ?_, ?_, ?_⟩
  · intro t
    have h := hA t
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · exact fun t ht => deriv3_eq_zero_of_nonpos ht
  · exact fun t ht => deriv3_eq_zero_of_one_le ht

end Work.NN.Newton.FTsharp
