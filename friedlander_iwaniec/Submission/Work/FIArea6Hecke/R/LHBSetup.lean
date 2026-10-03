import Mathlib
import Submission.Work.FIArea5.S16Hecke.LcontDefs
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6Hecke.StripCoreDefs

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- The archimedean factor at `m = 0` is the completion denominator. -/
lemma heckeArch_zero_eq_completeDenom (d : ℕ) (s : ℂ) :
    Work.FITop4.Bridge.heckeArch d 0 s = Work.FIArea5.S16Hecke.completeDenom d 0 s := by
  simp [Work.FITop4.Bridge.heckeArch, Work.FIArea5.S16Hecke.completeDenom]

/-- `Lval d 0 Lam = Lcont d Lam 0`. -/
lemma Lval_eq_Lcont (d : ℕ) (Lam : ℂ → ℂ) (s : ℂ) :
    Work.FIArea6Hecke.Lval d 0 Lam s = Work.FIArea5.S16Hecke.Lcont d Lam 0 s := by
  simp [Work.FIArea6Hecke.Lval, Work.FIArea5.S16Hecke.Lcont, heckeArch_zero_eq_completeDenom]

/-- The denominator does not vanish on `re s > 0`. -/
lemma heckeArch_zero_ne_zero {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 0 < s.re) :
    Work.FITop4.Bridge.heckeArch d 0 s ≠ 0 := by
  rw [heckeArch_zero_eq_completeDenom]
  exact Work.FIArea5.S16Hecke.completeDenom_ne_zero hd (by simpa using hs)

/-- On `re s > 1` the `L`-value read off any completion is the Hecke `L`-series. -/
lemma Lval_eq_heckeLSeries_of_one_lt_re {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    {Lam : ℂ → ℂ}
    (hagree : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 s)
    {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea6Hecke.Lval d 0 Lam s = Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
  have hD : Work.FITop4.Bridge.heckeArch d 0 s ≠ 0 := heckeArch_zero_ne_zero hd (by linarith)
  rw [Work.FIArea6Hecke.Lval, hagree s hs]
  exact mul_div_cancel_left₀ _ hD

end

end Work.FIArea6Hecke.R

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- Reindexing `range` against `Icc` when the `0` term vanishes. -/
lemma sum_range_eq_Icc (f : ℕ → ℝ) (hf0 : f 0 = 0) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.Icc 1 (N - 1), f n := by
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (f := f) (by norm_num : (0:ℕ) ≤ 1) hN]
  rw [show ∑ n ∈ Finset.Ico 0 1, f n = 0 from by
    rw [Finset.sum_Ico_eq_sum_range]; simp [hf0]]
  rw [show Finset.Ico 1 N = Finset.Icc 1 (N - 1) from by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
  ring

/-- Log bookkeeping for converting `log (4 C d (2 + u))` into a constant times
`log (4 d (2 + w))` when `u ≤ 2 + w`. -/
lemma log_bookkeeping {C d u w : ℝ} (hC : 1 ≤ C) (hd : 1 ≤ d)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (huz : u ≤ 2 + w) :
    Real.log (4 * C * d * (2 + u))
      ≤ (Real.log (16 * C) / Real.log 2 + 1) * Real.log (4 * d * (2 + w)) := by
  have hd0 : (0:ℝ) < d := by linarith
  have hC0 : (0:ℝ) < C := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hw2 : (0:ℝ) < 2 + w := by linarith
  have hA : 4 * C * d * (2 + u) ≤ 16 * C * (d * (2 + w)) := by
    have h1 : 2 + u ≤ 4 * (2 + w) := by nlinarith
    calc 4 * C * d * (2 + u) ≤ 4 * C * d * (4 * (2 + w)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 16 * C * (d * (2 + w)) := by ring
  have hApos : (0:ℝ) < 4 * C * d * (2 + u) := by
    have : 0 < 2 + u := by linarith
    positivity
  have hlogd : Real.log 2 ≤ Real.log (d * (2 + w)) := by
    refine Real.log_le_log (by norm_num) ?_
    have : (1:ℝ) ≤ (2 + w) := by linarith
    nlinarith
  have hL0 : 0 ≤ Real.log (16 * C) := Real.log_nonneg (by nlinarith)
  calc Real.log (4 * C * d * (2 + u))
      ≤ Real.log (16 * C * (d * (2 + w))) := Real.log_le_log hApos hA
    _ = Real.log (16 * C) + Real.log (d * (2 + w)) :=
        Real.log_mul (by positivity) (by positivity)
    _ ≤ (Real.log (16 * C) / Real.log 2) * Real.log (d * (2 + w)) + Real.log (d * (2 + w)) := by
        have : Real.log (16 * C) ≤ (Real.log (16 * C) / Real.log 2) * Real.log (d * (2 + w)) := by
          calc Real.log (16 * C) = (Real.log (16 * C) / Real.log 2) * Real.log 2 := by field_simp
            _ ≤ (Real.log (16 * C) / Real.log 2) * Real.log (d * (2 + w)) :=
                mul_le_mul_of_nonneg_left hlogd (by positivity)
        linarith
    _ = (Real.log (16 * C) / Real.log 2 + 1) * Real.log (d * (2 + w)) := by ring
    _ ≤ (Real.log (16 * C) / Real.log 2 + 1) * Real.log (4 * d * (2 + w)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Real.log_le_log (by positivity) ?_
        nlinarith

end

end Work.FIArea6Hecke.R
