import Mathlib
import Submission.Work.KMTAreas.A4.lip2ArcDefs
import Submission.Work.KMTAreas.A4.lip2Defs

/-!
# The support of the periodized tiling bump

The tiling bump `arcChi` of `Work.KMTAreas.A4.lip2ArcDefs` is supported in `[-3/4, 3/4]`
(it is `arcBump0`, supported in `(-3/4, 3/4)`, divided by the strictly positive
periodization `arcTileH`).  Consequently the periodized symbol

`t ↦ ∑' n : ℤ, arcChi (N * (t - s + n))`

of scale `N` centred at `s` vanishes unless some term of the sum is non-zero, i.e. unless
`N * (t - s + n)` lies in the support of `arcChi` for some integer `n`.  Equivalently: if the
sum is non-zero then the frequency `t` lies in the closed arc of the circle of radius
`3 / (4 * N)` around `s`.

This is the elementary support statement used to extract a *single* arc from the periodized
window symbol (compare `Work.KMTAreas.A4.lip2Defs.arcSet`).
-/

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

theorem arcChiSumSupport (N : ℝ) (hN : 0 < N) (t s : ℝ) (h : (∑' n : ℤ, Work.KMTAreas.A4.arcChi (N * (t - s + (n : ℝ)))) ≠ 0) : ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ Work.KMTAreas.A4.arcSet ((s : ℝ) : Work.Analysis.InverseTheory.FreqCircle) (3 / (4 * N)) := by
  -- Step 1: some term of the sum is non-zero.
  have hex : ∃ n : ℤ, arcBump0 (N * (t - s + (n : ℝ))) ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    refine h ?_
    refine (tsum_congr fun n => ?_).trans tsum_zero
    simp only [arcChi, hc n, zero_div]
  obtain ⟨n, hn⟩ := hex
  -- Step 2: that term's argument is small.  `arcBump0 u ≠ 0` forces `|u| < 3/4`, since
  -- `arcBump0 u = lipSchChi (u * 4/3)` and `lipSchChi x = 0` for `|x| ≥ 1`.
  have hlt : |t - s + (n : ℝ)| < 3 / (4 * N) := by
    have h1 : lipSchChi ((N * (t - s + (n : ℝ))) * (4 / 3)) ≠ 0 := by
      intro hh; exact hn (by rw [arcBump0]; exact hh)
    have h2 : ¬ ((1 : ℝ) ≤ |(N * (t - s + (n : ℝ))) * (4 / 3)|) :=
      fun hh => h1 (lipSchChi_eq_zero _ hh)
    have h3 : |(N * (t - s + (n : ℝ))) * (4 / 3)| < 1 := not_le.mp h2
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3), abs_mul, abs_of_pos hN] at h3
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * N)]
    nlinarith
  -- Step 3: the arithmetic frequency `n` is trivial in the circle, so `t` is within
  -- `3 / (4 * N)` of `s`.
  refine ⟨t - s + (n : ℝ), le_of_lt hlt, ?_⟩
  have hn0 : (((n : ℤ) : ℝ) : FreqCircle) = 0 := by
    rw [show ((n : ℤ) : ℝ) = n • (1 : ℝ) by simp]
    rw [AddCircle.coe_zsmul]
    simp [AddCircle.coe_period]
  rw [← AddCircle.coe_add, show s + (t - s + (n : ℝ)) = t + (n : ℝ) by ring,
    AddCircle.coe_add, hn0, add_zero]

end Work.KMTAreas.A4

