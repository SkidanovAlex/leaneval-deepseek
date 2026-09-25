import Mathlib
import Submission.Commons.Analysis.Maximal.real_maximal_weak_type

namespace Commons.Analysis.Maximal

open _root_.MeasureTheory
open Filter
open scoped ENNReal Topology

/-- The (centred) maximal average over all intervals containing `x` can be computed using only
intervals with rational endpoints.  The non-trivial direction is that every real interval
`[a,b] ∋ x` is the limit of rational intervals `[q_n, r_n] ∋ x` whose averages tend up to the
average over `[a,b]`. -/
theorem hlMax_eq_iSup_rat (φ : ℝ → ENNReal) (x : ℝ) :
    Commons.Analysis.Maximal.hlMax φ x
      = ⨆ (q : ℚ) (r : ℚ) (_ : (q : ℝ) ≤ x ∧ x ≤ (r : ℝ)),
          ENNReal.ofReal ((r : ℝ) - (q : ℝ))⁻¹ * lintegral
            (Measure.restrict volume (Set.Icc (q : ℝ) (r : ℝ))) φ := by
  set S : ℝ≥0∞ := ⨆ (q : ℚ) (r : ℚ) (_ : (q : ℝ) ≤ x ∧ x ≤ (r : ℝ)),
          ENNReal.ofReal ((r : ℝ) - (q : ℝ))⁻¹ * lintegral
            (Measure.restrict volume (Set.Icc (q : ℝ) (r : ℝ))) φ with hS
  apply le_antisymm
  · -- `hlMax φ x ≤ S`: every real interval is approximated by rational intervals.
    unfold hlMax
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    by_cases hlt : a < b
    · have hpos : 0 < b - a := sub_pos.mpr hlt
      -- rational approximations of `a` from below and of `b` from above
      have hq_exists : ∀ n : ℕ, ∃ q : ℚ, a - 1 / ((n : ℝ) + 1) < (q : ℝ) ∧ (q : ℝ) < a := by
        intro n
        apply exists_rat_btwn
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      have hr_exists : ∀ n : ℕ, ∃ r : ℚ, b < (r : ℝ) ∧ (r : ℝ) < b + 1 / ((n : ℝ) + 1) := by
        intro n
        apply exists_rat_btwn
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      choose q hq using hq_exists
      choose r hr using hr_exists
      have hone : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hq_tend : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝 a) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le
          (by have h := (tendsto_const_nhds (x := a)).sub hone; simpa using h)
          tendsto_const_nhds
          (fun n => le_of_lt (hq n).1) (fun n => le_of_lt (hq n).2)
      have hr_tend : Tendsto (fun n : ℕ => (r n : ℝ)) atTop (𝓝 b) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds
          (by have h := (tendsto_const_nhds (x := b)).add hone; simpa using h)
          (fun n => le_of_lt (hr n).1) (fun n => le_of_lt (hr n).2)
      have hd : Tendsto (fun n : ℕ => (r n : ℝ) - (q n : ℝ)) atTop (𝓝 (b - a)) :=
        hr_tend.sub hq_tend
      have hinv : Tendsto (fun n : ℕ => ((r n : ℝ) - (q n : ℝ))⁻¹) atTop (𝓝 ((b - a)⁻¹)) :=
        hd.inv₀ (ne_of_gt hpos)
      have hm : Tendsto (fun n : ℕ => ENNReal.ofReal (((r n : ℝ) - (q n : ℝ))⁻¹)) atTop
          (𝓝 (ENNReal.ofReal ((b - a)⁻¹))) :=
        ENNReal.tendsto_ofReal hinv
      set C : ℝ≥0∞ := ∫⁻ y in Set.Icc a b, φ y with hC
      have hA : ENNReal.ofReal ((b - a)⁻¹) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (inv_pos.mpr hpos)).ne'
      have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (((r n : ℝ) - (q n : ℝ))⁻¹) * C) atTop
          (𝓝 (ENNReal.ofReal ((b - a)⁻¹) * C)) :=
        ENNReal.Tendsto.mul_const hm (Or.inl hA)
      have hterm : ∀ n : ℕ,
          ENNReal.ofReal (((r n : ℝ) - (q n : ℝ))⁻¹) * C ≤ S := by
        intro n
        have hle : C ≤ ∫⁻ y in Set.Icc (q n : ℝ) (r n : ℝ), φ y := by
          rw [hC]
          exact lintegral_mono_set
            (Set.Icc_subset_Icc (le_of_lt (hq n).2) (le_of_lt (hr n).1))
        calc ENNReal.ofReal (((r n : ℝ) - (q n : ℝ))⁻¹) * C
            ≤ ENNReal.ofReal (((r n : ℝ) - (q n : ℝ))⁻¹)
                * (∫⁻ y in Set.Icc (q n : ℝ) (r n : ℝ), φ y) :=
              mul_le_mul_right hle _
          _ ≤ S := le_iSup_of_le (q n) (le_iSup_of_le (r n)
                    (le_iSup_of_le ⟨(hq n).2.le.trans hab.1, hab.2.trans (hr n).1.le⟩ le_rfl))
      exact le_of_tendsto' hlim hterm
    · -- `a = b`: the average over a degenerate interval vanishes.
      have hab' : a = b := le_antisymm (hab.1.trans hab.2) (not_lt.mp hlt)
      have hzero : ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, φ y = 0 := by
        have : b - a = 0 := by rw [← hab', sub_self]
        rw [this, inv_zero, ENNReal.ofReal_zero, zero_mul]
      rw [hzero]
      exact zero_le
  · -- `S ≤ hlMax φ x`: rational intervals are real intervals.
    rw [hS]
    refine iSup_le fun q => iSup_le fun r => iSup_le fun h => ?_
    unfold hlMax
    exact le_iSup_of_le (q : ℝ) (le_iSup_of_le (r : ℝ) (le_iSup_of_le h le_rfl))

end Commons.Analysis.Maximal
