import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Transport
import Submission.Work.SurgeryInvariance.API

namespace Work.Smooth.Morse.Sweep

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **A regular value of `g|_F` has a neighbourhood containing no critical value.**

The critical values are locally finite (`LocallyFiniteCriticalValues`): on the bounded interval
`[t-1, t+1]` there are only finitely many of them, hence (being finite) they form a closed set
which does not contain `t` (a regular value).  A neighbourhood of `t` therefore misses them, and
restricted to the ball of radius `1` it misses all critical values. -/
theorem exists_notMem_criticalValues_near (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hcrit : Work.Smooth.Morse.LocallyFiniteCriticalValues ψ g) {t : ℝ}
    (ht : t ∉ Work.Smooth.Morse.criticalValues ψ g) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s - t| < ε → s ∉ Work.Smooth.Morse.criticalValues ψ g := by
  -- the critical values inside the window `[t-1, t+1]` form a finite, hence closed, set
  have hAfin : (Work.Smooth.Morse.criticalValues ψ g ∩ Set.Icc (t - 1) (t + 1)).Finite :=
    hcrit (t - 1) (t + 1)
  have hAcl : IsClosed (Work.Smooth.Morse.criticalValues ψ g ∩ Set.Icc (t - 1) (t + 1)) :=
    hAfin.isClosed
  -- `t` is not one of them
  have htA : t ∉ Work.Smooth.Morse.criticalValues ψ g ∩ Set.Icc (t - 1) (t + 1) :=
    fun h => ht h.1
  -- hence a whole neighbourhood of `t` misses them, giving a radius `ε₁`
  have hmem : (Work.Smooth.Morse.criticalValues ψ g ∩ Set.Icc (t - 1) (t + 1))ᶜ ∈ nhds t :=
    hAcl.isOpen_compl.mem_nhds htA
  rw [Metric.mem_nhds_iff] at hmem
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := hmem
  -- shrink to radius `min ε₁ 1` so that the window restriction applies as well
  refine ⟨min ε₁ 1, lt_min hε₁pos one_pos, ?_⟩
  intro s hs
  have hsA : s ∉ Work.Smooth.Morse.criticalValues ψ g ∩ Set.Icc (t - 1) (t + 1) :=
    hε₁ (by
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_lt_of_le hs (min_le_left _ _))
  intro hsc
  exact hsA ⟨hsc, by
    have h1 : |s - t| < 1 := lt_of_lt_of_le hs (min_le_right _ _)
    rw [abs_lt] at h1
    exact ⟨by linarith, by linarith⟩⟩

/-- **The winding span is locally constant at a regular value.**

`t` is a regular value of `g|_F`, so by `exists_notMem_criticalValues_near` a whole neighbourhood
of `t` consists of regular values.  For any `s` in that neighbourhood the interval between `s`
and `t` is a regular interval, so `RegularEquivalent` (the loop-level transport across a regular
interval) relates the two sublevel regions `region ψ g s` and `region ψ g t`, and their winding
spans coincide (`RegularEquivalent.windingSpan_eq`, which is
`Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq`). -/
theorem windingSpan_locally_const_of_regularValue (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hcrit : Work.Smooth.Morse.LocallyFiniteCriticalValues ψ g) (hreg : Work.Smooth.Morse.RegularEquivalent ψ g) {t : ℝ} (ht : Work.Smooth.Morse.IsRegularValue ψ g t) : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g s) = Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g t) := by
  obtain ⟨ε, hεpos, hε⟩ := exists_notMem_criticalValues_near ψ hcrit ht
  refine ⟨ε, hεpos, ?_⟩
  intro s hs
  rcases lt_trichotomy s t with hlt | heq | hgt
  · -- `s < t`: the interval `[s,t]` is regular, so the two regions are `RegionEquivalent`
    have hregI : ∀ u ∈ Set.Icc s t, Work.Smooth.Morse.IsRegularValue ψ g u := by
      intro u hu
      apply hε u
      rw [Set.mem_Icc] at hu
      rw [abs_lt] at hs ⊢
      constructor <;> linarith [hu.1, hu.2, hs.1, hs.2]
    exact Work.Smooth.Morse.RegularEquivalent.windingSpan_eq
      (hreg s t (le_of_lt hlt) hregI)
  · -- `s = t`
    subst heq
    rfl
  · -- `t < s`: same, with the interval `[t,s]`
    have hregI : ∀ u ∈ Set.Icc t s, Work.Smooth.Morse.IsRegularValue ψ g u := by
      intro u hu
      apply hε u
      rw [Set.mem_Icc] at hu
      rw [abs_lt] at hs ⊢
      constructor <;> linarith [hu.1, hu.2, hs.1, hs.2]
    exact (Work.Smooth.Morse.RegularEquivalent.windingSpan_eq
      (hreg t s (le_of_lt hgt) hregI)).symm

end

end Work.Smooth.Morse.Sweep
