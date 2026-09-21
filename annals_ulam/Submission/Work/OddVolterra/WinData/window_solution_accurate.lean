import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.WinData.window_core_exists_rho
import Submission.Work.OddVolterra.WinData.window_tail_glue_rho

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

theorem window_solution_accurate (n : ℕ) (hn : 1 ≤ n) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ s : ℝ, 1 - 2 * Work.OddVolterra.tau ≤ s →
        s < 1 - 2 * Work.OddVolterra.tau + η₀ → h s = 0) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      h 0 = 0 → h ≠ 0 →
      ∃ Z : ℝ → Work.OddVolterra.St,
        ContinuousOn Z (Set.Icc (7 / 10 : ℝ) (1 : ℝ)) ∧
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) ∧
        (∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s) ∧
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (1 : ℝ), dist (Z s) (Work.OddVolterra.baseState s) ≤ η) := by
  intro η hη
  -- the target closeness, capped at `1/100` so that the cut-off data of the core coincide with
  -- the paper's data
  obtain ⟨ρ, hρpos, hρ100, hρη⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 100 ∧ ρ ≤ η :=
    ⟨min η (1 / 100), lt_min hη (by norm_num), min_le_right _ _, min_le_left _ _⟩
  -- the core: a continuous solution of the truncated system on `[7/10,19/20]`, within `ρ`
  obtain ⟨εc, hεc, Hc⟩ := window_core_exists_rho n hn ρ hρpos hρ100
  refine ⟨min εc (1 / 100), lt_min hεc (by norm_num), ?_⟩
  intro h hh hsupp hflat hsmall h0 hne
  have hsmallc : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ εc :=
    fun k hk s => le_trans (hsmall k hk s) (min_le_left _ _)
  have hsmall100 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hsmall k hk s) (min_le_right _ _)
  obtain ⟨Z, hZc, hZeq, hZdist, hZend⟩ := Hc h hh hsupp hflat hsmallc h0 hne
  -- the tail glue: a solution of the full system on `[7/10,9/10]`, frozen at `baseState`
  -- for `s ≥ 9/10`
  have hρ2 : ρ ≤ 1 / 2 := le_trans hρ100 (by norm_num)
  obtain ⟨Z', hZ'c, hZ'eq, hZ'tail, hZ'dist⟩ :=
    window_tail_glue_rho n hn hρpos hρ2 hh hsupp hsmall100 Z hZc hZeq hZdist hZend
  refine ⟨Z', hZ'c, hZ'eq, hZ'tail, ?_⟩
  intro s hs
  rcases lt_or_ge s (9 / 10 : ℝ) with hs' | hs'
  · exact le_trans (hZ'dist s ⟨hs.1, le_of_lt hs'⟩) hρη
  · rw [hZ'tail s hs', dist_self]
    exact hη.le

end Work.OddVolterra.WinData
