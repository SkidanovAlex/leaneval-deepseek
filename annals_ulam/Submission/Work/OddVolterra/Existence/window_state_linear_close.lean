import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddVolterra.Existence.window_C1_state
import Submission.Work.OddVolterra.Existence.exists_isEnvelopeCurve_of_window_solution
import Submission.Work.OddCurveB.Step2.StateWide

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- A non-zero `C^{n+3}` bump of size `ε` forces `ε > 0`. -/
lemma bump_eps_pos {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpThree n ε h) (hne : h ≠ 0) : 0 < ε := by
  by_contra hle
  push_neg at hle
  refine hne (funext fun s => ?_)
  have h1 : |iteratedDeriv 0 h s| ≤ ε := hb.deriv_bound (k := 0) (by omega) s
  rw [iteratedDeriv_zero] at h1
  exact abs_eq_zero.mp (le_antisymm (le_trans h1 hle) (abs_nonneg _))

theorem window_state_linear_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ} {h : ℝ → ℝ} {Z : ℝ → Work.OddVolterra.St},
      Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
      h 0 = 0 → h ≠ 0 →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z (Set.Ioi (0 : ℝ)) →
      (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
        Work.OddVolterra.Godd n h s (Z s) =
          (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) + Work.OddVolterra.Xi n h s) →
      (∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s) →
      (∀ s : ℝ, 1 / 4 ≤ s →
        ‖Z s - Work.OddVolterra.baseState s‖ ≤ 1 / 1000 ∧
        ‖deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s‖ ≤ 1 / 1000) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1,
        ‖Z s - Work.OddVolterra.baseState s‖ ≤ C * ε ∧
        ‖deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s‖ ≤ C * ε := by
  -- The two halves of the estimate: state closeness on `[1/4,9/10]` and derivative
  -- closeness on `[1/4,19/20]`; on `(9/10,1]` both sides agree with the ball's state.
  obtain ⟨Ks, εs, hKspos, hεspos, _, hcloseS⟩ :=
    Work.OddCurveB.Step2.w_window_state_close_core n hn
  obtain ⟨Kd, εd, hKdpos, hεdpos, _, hcloseD⟩ :=
    Work.OddVolterra.Existence.window_deriv_close_est n hn
  set C : ℝ := max (max Ks Kd) (1 / (1000 * min εs εd)) with hC
  have hCgeKs : Ks ≤ C := by
    rw [hC]; exact le_trans (le_max_left Ks Kd) (le_max_left (max Ks Kd) _)
  have hCgeKd : Kd ≤ C := by
    rw [hC]; exact le_trans (le_max_right Ks Kd) (le_max_left (max Ks Kd) _)
  have hCge : 1 / (1000 * min εs εd) ≤ C := by
    rw [hC]; exact le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le hKspos hCgeKs
  refine ⟨C, hCpos, ?_⟩
  intro ε h Z hb h0 hne hZsm hZsys hZtail hZdist
  have hεpos : 0 < ε := bump_eps_pos hb hne
  have htau : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := one_sub_tau
  have htail' : ∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s :=
    fun s hs => hZtail s (by rw [htau]; exact hs)
  have hZsm14 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z (Set.Ioi (1 / 4 : ℝ)) :=
    hZsm.mono (Set.Ioi_subset_Ioi (by norm_num))
  have hZcont : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) 1) :=
    hZsm.continuousOn.mono (fun x hx => by
      simp only [Set.mem_Ioi]; linarith [hx.1])
  have hdist4 : ∀ u : ℝ, 1 / 4 ≤ u →
      ‖Z u - Work.OddVolterra.baseState u‖ ≤ 1 / 1000 ∧
      ‖deriv Z u - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) u‖ ≤ 1 / 1000 :=
    fun u hu => hZdist u hu
  intro s hs
  have hs1 : (1 / 2 : ℝ) ≤ s := hs.1
  have hs4 : (1 / 4 : ℝ) ≤ s := by linarith
  rcases le_or_gt ε (min εs εd) with hεle | hεgt
  · have hstate : ‖Z s - Work.OddVolterra.baseState s‖ ≤ C * ε := by
      rcases le_or_gt s (9 / 10 : ℝ) with hs9 | hs9
      · have hball : ∀ u ∈ Set.Icc (1 / 4 : ℝ) 1,
            dist (Z u) (Work.OddVolterra.baseState u) ≤ 1 / 2 := by
          intro u hu
          rw [dist_eq_norm]
          exact le_trans (hdist4 u hu.1).1 (by norm_num)
        have h := hcloseS h Z ε hεpos (le_trans hεle (min_le_left εs εd)) hb
          hZsm14 hZcont hZsys htail' hball s ⟨by linarith, hs9⟩
        rw [dist_eq_norm] at h
        exact le_trans h (mul_le_mul_of_nonneg_right hCgeKs hεpos.le)
      · rw [htail' s (by linarith), sub_self, norm_zero]
        exact mul_nonneg hCpos.le hεpos.le
    have hderiv : ‖deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s‖
        ≤ C * ε := by
      rcases le_or_gt s (19 / 20 : ℝ) with hs19 | hs19
      · have hball : ∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
            dist (Z u) (Work.OddVolterra.baseState u) ≤ 9 / 20 := by
          intro u hu
          rw [dist_eq_norm]
          exact le_trans (hdist4 u hu.1).1 (by norm_num)
        have h := hcloseD h Z ε hεpos (le_trans hεle (min_le_right εs εd)) hb h0
          hZsm hZsys hZtail hball s ⟨by linarith, hs19⟩
        rw [dist_eq_norm] at h
        exact le_trans h (mul_le_mul_of_nonneg_right hCgeKd hεpos.le)
      · have hgt : (9 / 10 : ℝ) < s := by linarith
        have hev : Z =ᶠ[𝓝 s] (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) := by
          filter_upwards [Ici_mem_nhds hgt] with x hx
          exact htail' x hx
        rw [hev.deriv_eq, sub_self, norm_zero]
        exact mul_nonneg hCpos.le hεpos.le
    exact ⟨hstate, hderiv⟩
  · -- for `ε` above the small threshold the raw `1/1000` bounds already suffice
    have hbig : (1 : ℝ) / 1000 ≤ C * ε := by
      have hden : (0 : ℝ) < 1000 * min εs εd := by positivity
      have h2 : (1 : ℝ) / 1000 < (1 / (1000 * min εs εd)) * ε := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hden]
        have h3 : (1 : ℝ) / 1000 * (1000 * min εs εd) = min εs εd := by ring
        rw [h3]
        simpa using hεgt
      exact le_of_lt (lt_of_lt_of_le h2 (mul_le_mul_of_nonneg_right hCge hεpos.le))
    obtain ⟨h1, h2⟩ := hdist4 s hs4
    exact ⟨le_trans h1 hbig, le_trans h2 hbig⟩

end

end Work.OddVolterra.Existence
