import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Setup

namespace Work.Fatou.Analysis

/-!
# Balls in the vertical strip around `xOf` lie in `Qreg`

The reference abscissa `xOf b₁ b₂` is chosen so that the vertical strip
`|Re s - xOf b₁ b₂| ≤ 1` is contained in `Qreg b₁ b₂`, and so that the cones
defining `Qreg` are met transversally on that strip: `Re b₁ + 1 < xOf` and
`xOf + 3 < Re b₂`.  Consequently a ball of radius `R` centred at a point `s` of
the slightly larger strip `[xOf - 1/32, xOf + 1 + 1/32]` is still inside
`Qreg b₁ b₂`, provided `2R` is bounded by `|Im s|` up to a constant `K`
measuring how far the vertices `b₁, b₂` sit off the real axis.

The two coordinate estimates below are the analytic content: on the ball,
`Re (w - b₁) + |Im (w - b₁)| > 0` (the left cone) and
`Re (w - b₂) - |Im (w - b₂)| < 0` (the right cone).
-/

/-- **Left cone.**  If `Re (s - a) ≥ 31/32` and `2R + K ≤ |Im s|` with
`K ≥ |Im a| + 1`, then every `w` in the ball `B(s,R)` satisfies
`-|Im (w - a)| < Re (w - a)`, i.e. lies strictly inside the left cone with
vertex `a`. -/
private lemma left_cone {a s w : ℂ} {R : ℝ} (K : ℝ) (hK : |a.im| + 1 ≤ K)
    (hs : a.re + 31 / 32 ≤ s.re) (him : 2 * R + K ≤ |s.im|)
    (hw : w ∈ Metric.ball s R) : -|(w - a).im| < (w - a).re := by
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hwr : |(w - s).re| < R := lt_of_le_of_lt (Complex.abs_re_le_norm (w - s)) hw
  have hwi : |(w - s).im| < R := lt_of_le_of_lt (Complex.abs_im_le_norm (w - s)) hw
  have hre : (w - a).re = (s - a).re + (w - s).re := by simp only [Complex.sub_re]; ring
  have him2 : (w - a).im = (s - a).im + (w - s).im := by simp only [Complex.sub_im]; ring
  have hsre : (31 / 32 : ℝ) ≤ (s - a).re := by simp only [Complex.sub_re]; linarith
  have hsa : |s.im| - |a.im| ≤ |(s - a).im| := by
    have h := abs_sub_abs_le_abs_sub (s.im) (a.im)
    simpa [Complex.sub_im] using h
  have hsim : 2 * R + 1 ≤ |(s - a).im| := by linarith
  have htri : |(s - a).im| - |(w - s).im| ≤ |(w - a).im| := by
    have h := abs_sub_abs_le_abs_sub ((s - a).im) (-((w - s).im))
    rw [abs_neg, sub_neg_eq_add] at h
    rw [him2]
    exact h
  have h1 : (s - a).re - R < (w - a).re := by rw [hre]; linarith [(abs_lt.mp hwr).1]
  have h2 : |(s - a).im| - R < |(w - a).im| := by linarith
  have hsum : 0 < (w - a).re + |(w - a).im| := by linarith
  linarith [abs_nonneg ((w - a).im)]

/-- **Right cone.**  If `Re (s - b) ≤ -63/32` and `2R + K ≤ |Im s|` with
`K ≥ |Im b| + 1`, then every `w` in the ball `B(s,R)` satisfies
`Re (w - b) < |Im (w - b)|`, i.e. lies strictly inside the right cone with
vertex `b`. -/
private lemma right_cone {b s w : ℂ} {R : ℝ} (K : ℝ) (hK : |b.im| + 1 ≤ K)
    (hs : s.re ≤ b.re - 63 / 32) (him : 2 * R + K ≤ |s.im|)
    (hw : w ∈ Metric.ball s R) : (w - b).re < |(w - b).im| := by
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hwr : |(w - s).re| < R := lt_of_le_of_lt (Complex.abs_re_le_norm (w - s)) hw
  have hwi : |(w - s).im| < R := lt_of_le_of_lt (Complex.abs_im_le_norm (w - s)) hw
  have hre : (w - b).re = (s - b).re + (w - s).re := by simp only [Complex.sub_re]; ring
  have him2 : (w - b).im = (s - b).im + (w - s).im := by simp only [Complex.sub_im]; ring
  have hsre : (s - b).re ≤ -(63 / 32 : ℝ) := by simp only [Complex.sub_re]; linarith
  have hsb : |s.im| - |b.im| ≤ |(s - b).im| := by
    have h := abs_sub_abs_le_abs_sub (s.im) (b.im)
    simpa [Complex.sub_im] using h
  have hsim : 2 * R + 1 ≤ |(s - b).im| := by linarith
  have htri : |(s - b).im| - |(w - s).im| ≤ |(w - b).im| := by
    have h := abs_sub_abs_le_abs_sub ((s - b).im) (-((w - s).im))
    rw [abs_neg, sub_neg_eq_add] at h
    rw [him2]
    exact h
  have h1 : (w - b).re ≤ (s - b).re + R := by rw [hre]; linarith [(abs_lt.mp hwr).2]
  have h2 : |(s - b).im| - R < |(w - b).im| := by linarith
  have hsum : (w - b).re - |(w - b).im| < 0 := by linarith
  linarith [abs_nonneg ((w - b).im)]

theorem exists_ball_subset_Qreg (b₁ b₂ : Option ℂ) (hadm : MandelDim.QAdm b₁ b₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, Work.Fatou.xOf b₁ b₂ - 1 / 32 ≤ s.re →
      s.re ≤ Work.Fatou.xOf b₁ b₂ + 1 + 1 / 32 → ∀ R : ℝ,
      2 * R + K ≤ |s.im| → Metric.ball s R ⊆ MandelDim.Qreg b₁ b₂ := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · refine ⟨0, le_rfl, ?_⟩
      intro s _ _ R _ w _
      simp [MandelDim.Qreg]
    · refine ⟨|b.im| + 1, by positivity, ?_⟩
      intro s hs1 hs2 R him w hw
      have hs : s.re ≤ b.re - 63 / 32 := by
        simp only [Work.Fatou.xOf_none_some] at hs2
        linarith
      refine ⟨fun b' hb' => by simp at hb', ?_⟩
      simpa using right_cone (|b.im| + 1) le_rfl hs him hw
  · rcases b₂ with _ | b
    · refine ⟨|a.im| + 1, by positivity, ?_⟩
      intro s hs1 hs2 R him w hw
      have hs : a.re + 31 / 32 ≤ s.re := by
        simp only [Work.Fatou.xOf_some_none] at hs1
        linarith
      refine ⟨?_, fun b' hb' => by simp at hb'⟩
      simpa using left_cone (|a.im| + 1) le_rfl hs him hw
    · have hab : a.re + 4 < b.re := hadm a rfl b rfl
      refine ⟨|a.im| + |b.im| + 1, by positivity, ?_⟩
      intro s hs1 hs2 R him w hw
      have hsL : a.re + 31 / 32 ≤ s.re := by
        simp only [Work.Fatou.xOf_some_some] at hs1
        linarith
      have hsR : s.re ≤ b.re - 63 / 32 := by
        simp only [Work.Fatou.xOf_some_some] at hs2
        linarith
      refine ⟨?_, ?_⟩
      · simpa using left_cone (|a.im| + |b.im| + 1) (by linarith [abs_nonneg b.im]) hsL him hw
      · simpa using right_cone (|a.im| + |b.im| + 1) (by linarith [abs_nonneg a.im]) hsR him hw

end Work.Fatou.Analysis
