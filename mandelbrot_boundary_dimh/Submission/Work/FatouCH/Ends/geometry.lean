import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# Geometry at the two ends of `MandelDim.Qreg`

For `T` large the region `MandelDim.Qreg b₁ b₂` is `T/4`-thick at every point of height `±T` whose
real part is at most `T/4` in modulus (`marginsSafe`), and hence contains the ball of radius `T/8`
around such a point (`ballSubsetSafe`).  This is the geometric input for the pointwise derivative
bound `endsDerivBound` at both ends (the statement is deliberately sign-symmetric in `Im`).
-/

namespace Work.FatouCH.Ends

open Set Metric Complex
open scoped Topology

noncomputable section

/-- The left-cone margin grows at least like `T/4` at height `T`. -/
theorem margin1 {a z : ℂ} {T : ℝ} (hT : 2 * (|a.re| + |a.im|) ≤ T) (him : |z.im| = T)
    (hre : |z.re| ≤ T / 4) :
    T / 4 ≤ (z - a).re + |(z - a).im| := by
  have him_a : T - |a.im| ≤ |(z - a).im| := by
    have h := abs_add_le ((z - a).im) a.im
    have he : (z - a).im + a.im = z.im := by rw [Complex.sub_im]; ring
    rw [he, him] at h
    linarith
  have hre_a : -(T / 4) - |a.re| ≤ (z - a).re := by
    have he : (z - a).re = z.re - a.re := by rw [Complex.sub_re]
    have h1 : -|z.re| ≤ z.re := neg_abs_le _
    have h2 : -|a.re| ≤ -a.re := neg_le_neg (le_abs_self _)
    rw [he]
    linarith
  have habs : |a.re| + |a.im| ≤ T / 2 := by linarith
  linarith

/-- The right-cone margin grows at least like `T/4` at height `T`. -/
theorem margin2 {b z : ℂ} {T : ℝ} (hT : 2 * (|b.re| + |b.im|) ≤ T) (him : |z.im| = T)
    (hre : |z.re| ≤ T / 4) :
    T / 4 ≤ |(z - b).im| - (z - b).re := by
  have him_b : T - |b.im| ≤ |(z - b).im| := by
    have h := abs_add_le ((z - b).im) b.im
    have he : (z - b).im + b.im = z.im := by rw [Complex.sub_im]; ring
    rw [he, him] at h
    linarith
  have hre_b : (z - b).re ≤ T / 4 + |b.re| := by
    have he : (z - b).re = z.re - b.re := by rw [Complex.sub_re]
    have h1 : z.re ≤ |z.re| := le_abs_self _
    have h2 : -b.re ≤ |b.re| := neg_le_abs _
    rw [he]
    linarith
  have habs : |b.re| + |b.im| ≤ T / 2 := by linarith
  linarith

/-- Both cone margins of `MandelDim.Qreg b₁ b₂` grow like `T` in the region `|Im z| = T`,
`|Re z| ≤ T/4`. -/
theorem marginsSafe {b₁ b₂ : Option ℂ} :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (T : ℝ) (z : ℂ), T₀ ≤ T → |z.im| = T → |z.re| ≤ T / 4 →
      (∀ a ∈ b₁, T / 4 ≤ (z - a).re + |(z - a).im|) ∧
      (∀ b ∈ b₂, T / 4 ≤ |(z - b).im| - (z - b).re) := by
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · exact ⟨1, one_pos, fun T z hT him hre =>
      ⟨fun a' ha' => absurd ha' (by simp), fun b' hb' => absurd hb' (by simp)⟩⟩
  · refine ⟨max 1 (2 * (|b.re| + |b.im|)), by positivity, fun T z hT him hre => ⟨?_, ?_⟩⟩
    · intro a' ha'; exact absurd ha' (by simp)
    · intro b' hb'
      have hb'e : b' = b := (Option.mem_some.mp hb').symm
      subst hb'e
      exact margin2 (le_trans (le_max_right 1 _) hT) him hre
  · refine ⟨max 1 (2 * (|a.re| + |a.im|)), by positivity, fun T z hT him hre => ⟨?_, ?_⟩⟩
    · intro a' ha'
      have ha'e : a' = a := (Option.mem_some.mp ha').symm
      subst ha'e
      exact margin1 (le_trans (le_max_right 1 _) hT) him hre
    · intro b' hb'; exact absurd hb' (by simp)
  · refine ⟨max 1 (max (2 * (|a.re| + |a.im|)) (2 * (|b.re| + |b.im|))), by positivity,
      fun T z hT him hre => ⟨?_, ?_⟩⟩
    · intro a' ha'
      have ha'e : a' = a := (Option.mem_some.mp ha').symm
      subst ha'e
      exact margin1 (le_trans (le_max_left _ _) (le_trans (le_max_right 1 _) hT)) him hre
    · intro b' hb'
      have hb'e : b' = b := (Option.mem_some.mp hb').symm
      subst hb'e
      exact margin2 (le_trans (le_max_right _ _) (le_trans (le_max_right 1 _) hT)) him hre

/-- Cone-margin inequalities at `z` put the ball of radius `T/8` into `MandelDim.Qreg b₁ b₂`. -/
theorem ballSubsetSafe {b₁ b₂ : Option ℂ} {T : ℝ} (hT : 0 < T) {z : ℂ}
    (h1 : ∀ a ∈ b₁, T / 4 ≤ (z - a).re + |(z - a).im|)
    (h2 : ∀ b ∈ b₂, T / 4 ≤ |(z - b).im| - (z - b).re) :
    Metric.ball z (T / 8) ⊆ MandelDim.Qreg b₁ b₂ := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hwz : ‖w - z‖ < T / 8 := hw
  have hre_shift : ∀ c : ℂ, (z - c).re - ‖w - z‖ ≤ (w - c).re := by
    intro c
    have he : (w - c).re = (z - c).re + (w - z).re := by
      rw [Complex.sub_re, Complex.sub_re, Complex.sub_re]; ring
    rw [he]
    have h : -(‖w - z‖ : ℝ) ≤ (w - z).re := by
      linarith [neg_abs_le (w - z).re, Complex.abs_re_le_norm (w - z)]
    linarith
  have hre_shift' : ∀ c : ℂ, (w - c).re ≤ (z - c).re + ‖w - z‖ := by
    intro c
    have he : (w - c).re = (z - c).re + (w - z).re := by
      rw [Complex.sub_re, Complex.sub_re, Complex.sub_re]; ring
    rw [he]
    have h : (w - z).re ≤ ‖w - z‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    linarith
  have him_shift : ∀ c : ℂ, |(z - c).im| - ‖w - z‖ ≤ |(w - c).im| := by
    intro c
    have he : (z - c).im = (w - c).im - (w - z).im := by
      rw [Complex.sub_im, Complex.sub_im, Complex.sub_im]; ring
    rw [he]
    have h1' : |(w - c).im - (w - z).im| ≤ |(w - c).im| + |(w - z).im| := by
      have h := abs_add_le ((w - c).im) (-((w - z).im))
      rw [abs_neg] at h
      have heq : (w - c).im + -((w - z).im) = (w - c).im - (w - z).im := by ring
      rwa [heq] at h
    have h2' : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    linarith
  refine ⟨?_, ?_⟩
  · intro a ha
    have hza := h1 a ha
    have hR := hre_shift a
    have hI := him_shift a
    linarith
  · intro b hb
    have hzb := h2 b hb
    have hR := hre_shift' b
    have hI := him_shift b
    linarith

end

end Work.FatouCH.Ends
