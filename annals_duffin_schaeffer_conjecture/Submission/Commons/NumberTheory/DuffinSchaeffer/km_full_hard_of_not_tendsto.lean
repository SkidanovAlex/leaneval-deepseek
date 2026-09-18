import Mathlib
import Submission.Commons.NumberTheory.DuffinSchaeffer.eventually_reduced_fractions_near_Ico_nat

namespace Commons.NumberTheory.DuffinSchaeffer

open Set Filter MeasureTheory
open scoped Topology

private lemma norm_sub_coe_le_abs {x y : ℝ} :
    ‖(x : UnitAddCircle) - (y : UnitAddCircle)‖ ≤ |x - y| := by
  rw [← AddCircle.coe_sub]
  rw [UnitAddCircle.norm_eq]
  simpa using round_le (x - y) 0

private lemma eventually_reduced_fractions_near_circle (x : UnitAddCircle) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ m : ℕ, m < n ∧ m.gcd n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < ε := by
  let y := AddCircle.equivIco (1 : ℝ) 0 x
  have hxIco : (y : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    simpa using y.property
  have hxcoe : ((y : ℝ) : UnitAddCircle) = x := by
    simpa [y] using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := x))
  refine (eventually_reduced_fractions_near_Ico_nat hxIco hε).mono ?_
  intro n hn
  rcases hn with ⟨m, hm, hg, hlt⟩
  refine ⟨m, hm, hg, ?_⟩
  have hnorm : ‖((y : ℝ) : UnitAddCircle) - ↑((m : ℝ) / n)‖ ≤
      |(y : ℝ) - (m : ℝ) / n| := by
    rw [← AddCircle.coe_sub]
    rw [UnitAddCircle.norm_eq]
    simpa using round_le ((y : ℝ) - (m : ℝ) / n) 0
  rw [← hxcoe]
  exact lt_of_le_of_lt hnorm hlt

private lemma exists_frequently_ge_of_not_tendsto {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n)
    (h : ¬ Tendsto δ atTop (𝓝 0)) :
    ∃ ε > 0, ∃ᶠ (n : ℕ) in atTop, ε ≤ δ n := by
  rw [Metric.tendsto_atTop] at h
  push Not at h
  rcases h with ⟨ε, hε, h⟩
  refine ⟨ε, hε, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨n, hn, hle⟩ := h N
  refine ⟨n, hn, ?_⟩
  have hdist : dist (δ n) 0 = δ n := by
    simp [abs_of_nonneg (hδ n)]
  simpa [hdist] using hle

theorem km_full_hard_of_not_tendsto (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (h : ¬ Filter.Tendsto δ Filter.atTop (nhds 0)) :
    MeasureTheory.volume (addWellApproximable UnitAddCircle δ) = 1 := by
  have huniv : addWellApproximable UnitAddCircle δ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [UnitAddCircle.mem_addWellApproximable_iff]
    obtain ⟨ε, hε0, hfreq⟩ := exists_frequently_ge_of_not_tendsto hδ h
    have hevent := eventually_reduced_fractions_near_circle x hε0
    have hfreq_both : ∃ᶠ (n : ℕ) in atTop,
        (∃ m : ℕ, m < n ∧ m.gcd n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < ε) ∧ ε ≤ δ n :=
      hevent.and_frequently hfreq
    have hinf : {n : ℕ |
        (∃ m : ℕ, m < n ∧ m.gcd n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < ε) ∧
          ε ≤ δ n}.Infinite := by
      rwa [Nat.frequently_atTop_iff_infinite] at hfreq_both
    apply hinf.mono
    intro n hn
    rcases hn with ⟨⟨m, hm, hg, hnorm⟩, hδn⟩
    exact ⟨m, hm, hg, lt_of_lt_of_le hnorm hδn⟩
  rw [huniv]
  exact UnitAddCircle.measure_univ

end Commons.NumberTheory.DuffinSchaeffer
