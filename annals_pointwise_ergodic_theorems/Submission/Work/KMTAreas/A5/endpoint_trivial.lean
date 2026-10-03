import Mathlib
import Submission.Work.KMTAreas.A5.Basic

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- On `ℤ` with counting measure, a function whose `eLpNorm` vanishes is identically zero: the
counting measure has no non-empty null sets. -/
lemma eq_zero_of_eLpNorm_count_eq_zero {p : ℝ≥0∞} (hp : p ≠ 0) {u : ℤ → ℂ}
    (h : eLpNorm u p Measure.count = 0) : u = 0 := by
  funext n
  have hsm : AEStronglyMeasurable u Measure.count := AEStronglyMeasurable.of_discrete
  have h0 : u =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hp).mp h
  by_contra hn
  have hsub : ({n} : Set ℤ) ⊆ {m : ℤ | u m ≠ 0} := by
    intro m hm
    rw [Set.mem_singleton_iff] at hm
    subst hm
    exact hn
  have hle : Measure.count {n} ≤ Measure.count {m : ℤ | u m ≠ 0} := measure_mono hsub
  rw [Measure.count_singleton] at hle
  have hne : Measure.count {m : ℤ | u m ≠ 0} ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hle)
  exact hne (ae_iff.mp h0)

/-- **The trivial endpoint of the bilinear bound.**  A bilinear-type estimate that holds for all
pairs of *finite* `eLpNorm` extends to all pairs: whenever one of the two norms is infinite the
right-hand side is either `⊤` (and the inequality is trivial) or `0`, the latter only when the
corresponding input vanishes identically (counting measure on `ℤ`), in which case the
hypotheses `hzero_left`/`hzero_right` make the left-hand side vanish too. -/
theorem endpoint_trivial (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    {p q r : ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hzero_left : ∀ v : ℤ → ℂ, T 0 v = 0)
    (hzero_right : ∀ u : ℤ → ℂ, T u 0 = 0)
    (hfin : ∀ u v : ℤ → ℂ, eLpNorm u p Measure.count < ⊤ → eLpNorm v q Measure.count < ⊤ →
      eLpNorm (T u v) r Measure.count
        ≤ M * eLpNorm u p Measure.count * eLpNorm v q Measure.count) :
    ∀ u v : ℤ → ℂ, eLpNorm (T u v) r Measure.count
      ≤ M * eLpNorm u p Measure.count * eLpNorm v q Measure.count := by
  intro u v
  by_cases htop : (eLpNorm u p Measure.count = ⊤ ∧ eLpNorm v q Measure.count ≠ 0) ∨
      (eLpNorm v q Measure.count = ⊤ ∧ eLpNorm u p Measure.count ≠ 0)
  · -- one of the two norms is infinite and the other is non-zero: the right-hand side is `⊤`
    have hRHS : M * eLpNorm u p Measure.count * eLpNorm v q Measure.count = ⊤ := by
      rcases htop with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · rw [ha, ENNReal.mul_top hM, ENNReal.top_mul hb]
      · rw [hb, ENNReal.mul_top (mul_ne_zero hM ha)]
    rw [hRHS]
    exact le_top
  · -- otherwise the right-hand side is finite, or one of the two inputs vanishes
    have h1 : eLpNorm u p Measure.count = ⊤ → eLpNorm v q Measure.count = 0 :=
      fun h => by by_contra hb; exact htop (Or.inl ⟨h, hb⟩)
    have h2 : eLpNorm v q Measure.count = ⊤ → eLpNorm u p Measure.count = 0 :=
      fun h => by by_contra ha; exact htop (Or.inr ⟨h, ha⟩)
    rcases eq_or_ne (eLpNorm u p Measure.count) 0 with hu0 | hu0
    · have hu : u = 0 := eq_zero_of_eLpNorm_count_eq_zero hp hu0
      rw [hu, hzero_left v, eLpNorm_zero]
      exact bot_le
    rcases eq_or_ne (eLpNorm v q Measure.count) 0 with hv0 | hv0
    · have hv : v = 0 := eq_zero_of_eLpNorm_count_eq_zero hq hv0
      rw [hv, hzero_right u, eLpNorm_zero]
      exact bot_le
    · exact hfin u v (lt_top_iff_ne_top.mpr (fun h => hv0 (h1 h)))
        (lt_top_iff_ne_top.mpr (fun h => hu0 (h2 h)))

end Work.KMTAreas.A5
