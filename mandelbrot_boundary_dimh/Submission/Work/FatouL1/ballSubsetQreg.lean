import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouL1.strip_in_Qreg

/-!
# Balls off the real axis are contained in `Qreg`

`Qreg b₁ b₂` is the complement of the two closed `45°` wedges that open to the left with apex
`b₁` and to the right with apex `b₂`.  Hence a euclidean ball whose centre sits in the open
strip `(x₀-1, x₀+3)` and whose *radius* is small compared with `|Im s|` (with a linear gain
`2R + K ≤ |Im s|`, exactly the form used for the cylinder charts) stays in `Qreg`.

The two vertex conditions are handled separately: for a vertex `a ∈ b₁` (which lies strictly
left of the strip) the point `z ∈ ball s R` satisfies `|z.im - a.im| > R > a.re - z.re`, and
for a vertex `b ∈ b₂` (strictly right of the strip) it satisfies
`(z - b).re < R < |(z - b).im|`. -/

namespace Work.FatouL1

open Set Metric

/-- If `s` lies strictly right of `a` and the ball is `K > |a.im|` away from the real axis,
then the ball misses the left wedge of apex `a`. -/
private lemma ball_left {a : ℂ} {x₀ K : ℝ} (ha : a.re + 1 < x₀) (hK : |a.im| < K)
    {s : ℂ} (hs : x₀ - 1 < s.re) {R : ℝ} (hR : 2 * R + K ≤ |s.im|)
    {z : ℂ} (hz : z ∈ Metric.ball s R) : -|(z - a).im| < (z - a).re := by
  rw [Metric.mem_ball] at hz
  have hzre : |z.re - s.re| ≤ dist z s := by
    rw [dist_eq_norm]
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - s)
  have hzim : |z.im - s.im| ≤ dist z s := by
    rw [dist_eq_norm]
    simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - s)
  have hzre' : z.re > s.re - R := by
    have h := (abs_lt.1 (lt_of_le_of_lt hzre hz)).1
    linarith
  have him : |(z - a).im| > R := by
    have hsi : |z.im| > R + K := by
      have h1 : |s.im| - |z.im| ≤ |z.im - s.im| := by
        have := abs_sub_abs_le_abs_sub s.im z.im
        linarith [abs_sub_comm s.im z.im]
      have h2 : |z.im - s.im| < R := lt_of_le_of_lt hzim hz
      linarith
    have h3 : |(z - a).im| ≥ |z.im| - |a.im| := by
      simpa [Complex.sub_im] using abs_sub_abs_le_abs_sub z.im a.im
    linarith
  have hre : (z - a).re = z.re - a.re := Complex.sub_re z a
  rw [hre]
  linarith

/-- If `s` lies strictly left of `b` and the ball is `K > |b.im|` away from the real axis,
then the ball misses the right wedge of apex `b`. -/
private lemma ball_right {b : ℂ} {x₀ K : ℝ} (hb : x₀ + 3 < b.re) (hK : |b.im| < K)
    {s : ℂ} (hs : s.re < x₀ + 3) {R : ℝ} (hR : 2 * R + K ≤ |s.im|)
    {z : ℂ} (hz : z ∈ Metric.ball s R) : (z - b).re < |(z - b).im| := by
  rw [Metric.mem_ball] at hz
  have hzre : |z.re - s.re| ≤ dist z s := by
    rw [dist_eq_norm]
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - s)
  have hzim : |z.im - s.im| ≤ dist z s := by
    rw [dist_eq_norm]
    simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - s)
  have hzre' : z.re < s.re + R := by
    have h := (abs_lt.1 (lt_of_le_of_lt hzre hz)).2
    linarith
  have him : |(z - b).im| > R := by
    have hsi : |z.im| > R + K := by
      have h1 : |s.im| - |z.im| ≤ |z.im - s.im| := by
        have := abs_sub_abs_le_abs_sub s.im z.im
        linarith [abs_sub_comm s.im z.im]
      have h2 : |z.im - s.im| < R := lt_of_le_of_lt hzim hz
      linarith
    have h3 : |(z - b).im| ≥ |z.im| - |b.im| := by
      simpa [Complex.sub_im] using abs_sub_abs_le_abs_sub z.im b.im
    linarith
  have hre : (z - b).re = z.re - b.re := Complex.sub_re z b
  rw [hre]
  linarith

theorem ballSubsetQreg {b₁ b₂ : Option ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, x₀ - 1 < s.re → s.re < x₀ + 3 → ∀ R : ℝ,
      2 * R + K ≤ |s.im| → Metric.ball s R ⊆ MandelDim.Qreg b₁ b₂ := by
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · -- both vertices are absent: every ball qualifies
    exact ⟨1, by norm_num, fun s _ _ R _ z _ => by simp [MandelDim.Qreg]⟩
  · have hb : x₀ + 3 < b.re := h₂ b (by simp)
    refine ⟨|b.im| + 1, by positivity, fun s hs1 hs2 R hR z hz => ?_⟩
    refine ⟨fun c hc => by simp at hc, fun c hc => ?_⟩
    have hc' : c = b := by simpa [eq_comm] using hc
    rw [hc']
    exact ball_right hb (by linarith) hs2 hR hz
  · have ha : a.re + 1 < x₀ := h₁ a (by simp)
    refine ⟨|a.im| + 1, by positivity, fun s hs1 hs2 R hR z hz => ?_⟩
    refine ⟨fun c hc => ?_, fun c hc => by simp at hc⟩
    have hc' : c = a := by simpa [eq_comm] using hc
    rw [hc']
    exact ball_left ha (by linarith) hs1 hR hz
  · have ha : a.re + 1 < x₀ := h₁ a (by simp)
    have hb : x₀ + 3 < b.re := h₂ b (by simp)
    refine ⟨|a.im| + |b.im| + 1, by positivity, fun s hs1 hs2 R hR z hz => ?_⟩
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have hc' : c = a := by simpa [eq_comm] using hc
      rw [hc']
      exact ball_left ha (by linarith [abs_nonneg b.im]) hs1 hR hz
    · have hc' : c = b := by simpa [eq_comm] using hc
      rw [hc']
      exact ball_right hb (by linarith [abs_nonneg a.im]) hs2 hR hz

end Work.FatouL1
