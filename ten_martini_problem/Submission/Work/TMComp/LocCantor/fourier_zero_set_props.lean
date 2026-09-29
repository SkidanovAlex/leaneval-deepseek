import Mathlib
import Submission.Work.TMComp.LocCantor.Defs

namespace Work.TMComp.LocCantor

open Set Filter

/-- Structural properties of the zero set of a nonzero real-analytic, `1`-periodic function
`ℝ → ℂ`.  For `f = fourier u`: the zero set is closed, its points are isolated, it meets `[0,1]`
in a finite set, and it is invariant under the translations `z ↦ z ± 1`.

The analytic part is the *principle of isolated zeros*: a nonzero real-analytic function on the
connected set `ℝ` has no accumulation point of zeros among its zeros, whence the zero set is a
closed discrete subset of `ℝ`; a closed discrete subset of the compact interval `[0,1]` is
finite.  The `z ± 1` part is exactly periodicity. -/
theorem fourier_zero_set_props {u : ℤ → ℂ}
    (hAn : AnalyticOnNhd ℝ (Work.TMComp.fourier u) Set.univ)
    (hnt : Work.TMComp.fourier u ≠ 0)
    (hper : ∀ x : ℝ, Work.TMComp.fourier u (x + 1) = Work.TMComp.fourier u x) :
    IsClosed {x : ℝ | Work.TMComp.fourier u x = 0} ∧
      (∀ z ∈ {x : ℝ | Work.TMComp.fourier u x = 0}, ∃ ε > 0,
        ∀ y ∈ {x : ℝ | Work.TMComp.fourier u x = 0}, |y - z| < ε → y = z) ∧
      (({x : ℝ | Work.TMComp.fourier u x = 0} ∩ Set.Icc 0 1).Finite) ∧
      (∀ z ∈ {x : ℝ | Work.TMComp.fourier u x = 0},
        z + 1 ∈ {x : ℝ | Work.TMComp.fourier u x = 0} ∧
        z - 1 ∈ {x : ℝ | Work.TMComp.fourier u x = 0}) := by
  set Z : Set ℝ := {x : ℝ | Work.TMComp.fourier u x = 0} with hZ
  -- The zero set is closed, since `fourier u` is continuous.
  have hclosed : IsClosed Z := by
    rw [hZ]
    exact isClosed_eq (continuousOn_univ.mp hAn.continuousOn) continuous_const
  -- The zero set is discrete, by the principle of isolated zeros.
  have hcod : ∀ᶠ x in Filter.codiscreteWithin (Set.univ : Set ℝ),
      Work.TMComp.fourier u x ≠ 0 := by
    rcases AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (𝕜 := ℝ) (E := ℂ) hAn isPreconnected_univ with h | h
    · exact absurd (funext fun x => h (mem_univ x)) hnt
    · exact h
  have hdis : IsDiscrete Z := by
    have h2 := isDiscrete_of_codiscreteWithin (U := (Set.univ : Set ℝ)) (s := Z)
      (show Zᶜ ∈ Filter.codiscreteWithin (Set.univ : Set ℝ) from hcod)
    simpa using h2
  refine ⟨hclosed, ?_, ?_, ?_⟩
  · -- each zero is isolated
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdis hz
    refine ⟨ε, hε, fun y hy hyz => ?_⟩
    have hyb : y ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, Real.dist_eq]; exact hyz
    have : y ∈ ({z} : Set ℝ) := by
      rw [← hball]; exact ⟨hyb, hy⟩
    simpa using this
  · -- finitely many zeros in `[0,1]`
    have hcomp : IsCompact (Z ∩ Set.Icc 0 1) :=
      IsCompact.of_isClosed_subset isCompact_Icc (hclosed.inter isClosed_Icc)
        Set.inter_subset_right
    exact IsCompact.finite hcomp (hdis.mono Set.inter_subset_left)
  · -- periodicity of the zero set
    intro z hz
    refine ⟨?_, ?_⟩
    · change Work.TMComp.fourier u (z + 1) = 0
      rw [hper z]; exact hz
    · change Work.TMComp.fourier u (z - 1) = 0
      have h := hper (z - 1)
      simp only [sub_add_cancel] at h
      rw [← h]; exact hz

end Work.TMComp.LocCantor
