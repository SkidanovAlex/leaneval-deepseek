import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_critical_poly

/-!
# The boundary integral of `u ↦ (u - α)⁻¹` over the AFE rectangle `[-1,1] × [-T,T]`

For `α` in the open rectangle and `T > 0`, the function `u ↦ (u - α)⁻¹` has a single
simple pole inside `⟨-1,-T⟩ ⟨1,T⟩` with residue `1`, so its boundary integral equals `2πi`.

Proof: `rectBoundary` is covariant under translating both the rectangle and the integrand
(`rectBoundary_shifted_translate`), which reduces the statement to `∮_{∂R} u⁻¹ du = 2πi`
for the translated rectangle `R = ⟨-1-α.re, -T-α.im⟩ ⟨1-α.re, T-α.im⟩` containing `0` in
its interior (`rectBoundary_shifted_inv_general`).  That general rectangle is handled by a
chain decomposition in the vertical direction (`…_chain_y`, moving the horizontal cuts to
`±T₀` with `T₀ := min (-c) d / 2` so the two outer strips avoid `0`) followed by the same
decomposition in the horizontal direction (`…_chain_x`, cuts at `±1`), the four outer
strips being killed by Cauchy–Goursat (`…_goursat_*`), and the central rectangle
`⟨-1,-T₀⟩ ⟨1,T₀⟩` being the model value `PL.AfeRect.rectBoundary_inv_corners`.
-/

open MeasureTheory Complex
open scoped Real Interval
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Commons.NumberTheory.Zeta

noncomputable section

/-- Pointwise identity used for the horizontal edges of the translated rectangle. -/
lemma rectBoundary_shifted_sub_hor (x : ℝ) (p q : ℂ) :
    ((x - q.re : ℝ) : ℂ) + (((p - q).im : ℝ) : ℂ) * I
      = (x : ℂ) + ((p.im : ℝ) : ℂ) * I - q := by
  apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]

/-- Pointwise identity used for the vertical edges of the translated rectangle. -/
lemma rectBoundary_shifted_sub_vert (y : ℝ) (p q : ℂ) :
    (((p - q).re : ℝ) : ℂ) + ((y - q.im : ℝ) : ℂ) * I
      = ((p.re : ℝ) : ℂ) + (y : ℂ) * I - q := by
  apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]

/-- `rectBoundary` is covariant under translating the rectangle corners and the integrand:
the boundary integral of `u ↦ f (u - α)` over `⟨z,w⟩` equals that of `f` over `⟨z-α, w-α⟩`. -/
lemma rectBoundary_shifted_translate (z w α : ℂ) (f : ℂ → ℂ) :
    PL.AfeRect.rectBoundary (z - α) (w - α) f
      = PL.AfeRect.rectBoundary z w (fun u : ℂ => f (u - α)) := by
  unfold PL.AfeRect.rectBoundary
  simp only []
  have h1 : (∫ x : ℝ in (z - α).re..(w - α).re, f ((x : ℂ) + (((z - α).im : ℝ) : ℂ) * I))
      = ∫ x : ℝ in z.re..w.re, f ((x : ℂ) + ((z.im : ℝ) : ℂ) * I - α) := by
    have hsub := intervalIntegral.integral_comp_sub_right
      (f := fun x : ℝ => f ((x : ℂ) + (((z - α).im : ℝ) : ℂ) * I))
      (a := z.re) (b := w.re) (d := α.re)
    rw [← Complex.sub_re z α, ← Complex.sub_re w α] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro x _
    simp only []
    rw [rectBoundary_shifted_sub_hor]
  have h2 : (∫ x : ℝ in (z - α).re..(w - α).re, f ((x : ℂ) + (((w - α).im : ℝ) : ℂ) * I))
      = ∫ x : ℝ in z.re..w.re, f ((x : ℂ) + ((w.im : ℝ) : ℂ) * I - α) := by
    have hsub := intervalIntegral.integral_comp_sub_right
      (f := fun x : ℝ => f ((x : ℂ) + (((w - α).im : ℝ) : ℂ) * I))
      (a := z.re) (b := w.re) (d := α.re)
    rw [← Complex.sub_re z α, ← Complex.sub_re w α] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro x _
    simp only []
    rw [rectBoundary_shifted_sub_hor]
  have h3 : (∫ y : ℝ in (z - α).im..(w - α).im, f ((((w - α).re : ℝ) : ℂ) + (y : ℂ) * I))
      = ∫ y : ℝ in z.im..w.im, f (((w.re : ℝ) : ℂ) + (y : ℂ) * I - α) := by
    have hsub := intervalIntegral.integral_comp_sub_right
      (f := fun y : ℝ => f ((((w - α).re : ℝ) : ℂ) + (y : ℂ) * I))
      (a := z.im) (b := w.im) (d := α.im)
    rw [← Complex.sub_im z α, ← Complex.sub_im w α] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro y _
    simp only []
    rw [rectBoundary_shifted_sub_vert]
  have h4 : (∫ y : ℝ in (z - α).im..(w - α).im, f ((((z - α).re : ℝ) : ℂ) + (y : ℂ) * I))
      = ∫ y : ℝ in z.im..w.im, f (((z.re : ℝ) : ℂ) + (y : ℂ) * I - α) := by
    have hsub := intervalIntegral.integral_comp_sub_right
      (f := fun y : ℝ => f ((((z - α).re : ℝ) : ℂ) + (y : ℂ) * I))
      (a := z.im) (b := w.im) (d := α.im)
    rw [← Complex.sub_im z α, ← Complex.sub_im w α] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro y _
    simp only []
    rw [rectBoundary_shifted_sub_vert]
  rw [h1, h2, h3, h4]

/-- Clean form of the boundary integral of `u ↦ u⁻¹`: the four edges, written with
explicit real parametrisations. -/
lemma rectBoundary_shifted_clean (a b c d : ℝ) :
    PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹) =
      (∫ x : ℝ in a..b, ((x : ℂ) + (c : ℂ) * I)⁻¹)
      - (∫ x : ℝ in a..b, ((x : ℂ) + (d : ℂ) * I)⁻¹)
      + I • (∫ y : ℝ in c..d, ((b : ℂ) + (y : ℂ) * I)⁻¹)
      - I • (∫ y : ℝ in c..d, ((a : ℂ) + (y : ℂ) * I)⁻¹) := by
  unfold PL.AfeRect.rectBoundary
  simp only []

/-- Continuity of `y ↦ (t + iy)⁻¹` for `t ≠ 0` (a vertical line avoiding `0`). -/
lemma rectBoundary_shifted_cont_vert (t : ℝ) (ht : t ≠ 0) :
    Continuous (fun y : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro y hy
    have hre : t = 0 := by
      have := congrArg Complex.re hy
      simpa using this
    exact ht hre

/-- Continuity of `x ↦ (x + it)⁻¹` for `t ≠ 0` (a horizontal line avoiding `0`). -/
lemma rectBoundary_shifted_cont_horiz (t : ℝ) (ht : t ≠ 0) :
    Continuous (fun x : ℝ => ((x : ℂ) + (t : ℂ) * I)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x hx
    have him : t = 0 := by
      have := congrArg Complex.im hx
      simpa using this
    exact ht him

/-- Additivity of the boundary integral of `u ↦ u⁻¹` in the vertical direction: cutting
`[c,d]` at `-T₀` and `T₀` and reassembling, the shared horizontal edges cancel. -/
lemma rectBoundary_shifted_chain_y (a b c d T₀ : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹)
      = PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, -T₀⟩ (fun u : ℂ => u⁻¹)
        + PL.AfeRect.rectBoundary ⟨a, -T₀⟩ ⟨b, T₀⟩ (fun u : ℂ => u⁻¹)
        + PL.AfeRect.rectBoundary ⟨a, T₀⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹) := by
  rw [rectBoundary_shifted_clean a b c d, rectBoundary_shifted_clean a b c (-T₀),
    rectBoundary_shifted_clean a b (-T₀) T₀, rectBoundary_shifted_clean a b T₀ d]
  have hca := rectBoundary_shifted_cont_vert a ha
  have hcb := rectBoundary_shifted_cont_vert b hb
  have hv_a : (∫ y : ℝ in c..d, ((a : ℂ) + (y : ℂ) * I)⁻¹)
      = (∫ y : ℝ in c..(-T₀), ((a : ℂ) + (y : ℂ) * I)⁻¹)
        + (∫ y : ℝ in (-T₀)..T₀, ((a : ℂ) + (y : ℂ) * I)⁻¹)
        + (∫ y : ℝ in T₀..d, ((a : ℂ) + (y : ℂ) * I)⁻¹) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hca.intervalIntegrable c T₀) (hca.intervalIntegrable T₀ d),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hca.intervalIntegrable c (-T₀)) (hca.intervalIntegrable (-T₀) T₀)]
  have hv_b : (∫ y : ℝ in c..d, ((b : ℂ) + (y : ℂ) * I)⁻¹)
      = (∫ y : ℝ in c..(-T₀), ((b : ℂ) + (y : ℂ) * I)⁻¹)
        + (∫ y : ℝ in (-T₀)..T₀, ((b : ℂ) + (y : ℂ) * I)⁻¹)
        + (∫ y : ℝ in T₀..d, ((b : ℂ) + (y : ℂ) * I)⁻¹) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcb.intervalIntegrable c T₀) (hcb.intervalIntegrable T₀ d),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hcb.intervalIntegrable c (-T₀)) (hcb.intervalIntegrable (-T₀) T₀)]
  rw [hv_a, hv_b]
  ring

/-- Additivity of the boundary integral of `u ↦ u⁻¹` in the horizontal direction: cutting
`[a,b]` at `-1` and `1` and reassembling, the shared vertical edges cancel. -/
lemma rectBoundary_shifted_chain_x (a b c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹)
      = PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨-1, d⟩ (fun u : ℂ => u⁻¹)
        + PL.AfeRect.rectBoundary ⟨-1, c⟩ ⟨1, d⟩ (fun u : ℂ => u⁻¹)
        + PL.AfeRect.rectBoundary ⟨1, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹) := by
  rw [rectBoundary_shifted_clean a b c d, rectBoundary_shifted_clean a (-1) c d,
    rectBoundary_shifted_clean (-1) 1 c d, rectBoundary_shifted_clean 1 b c d]
  have hcc := rectBoundary_shifted_cont_horiz c hc
  have hcd := rectBoundary_shifted_cont_horiz d hd
  have hv_c : (∫ x : ℝ in a..b, ((x : ℂ) + (c : ℂ) * I)⁻¹)
      = (∫ x : ℝ in a..(-1), ((x : ℂ) + (c : ℂ) * I)⁻¹)
        + (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + (c : ℂ) * I)⁻¹)
        + (∫ x : ℝ in 1..b, ((x : ℂ) + (c : ℂ) * I)⁻¹) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcc.intervalIntegrable a 1) (hcc.intervalIntegrable 1 b),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hcc.intervalIntegrable a (-1)) (hcc.intervalIntegrable (-1) 1)]
  have hv_d : (∫ x : ℝ in a..b, ((x : ℂ) + (d : ℂ) * I)⁻¹)
      = (∫ x : ℝ in a..(-1), ((x : ℂ) + (d : ℂ) * I)⁻¹)
        + (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + (d : ℂ) * I)⁻¹)
        + (∫ x : ℝ in 1..b, ((x : ℂ) + (d : ℂ) * I)⁻¹) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcd.intervalIntegrable a 1) (hcd.intervalIntegrable 1 b),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hcd.intervalIntegrable a (-1)) (hcd.intervalIntegrable (-1) 1)]
  rw [hv_c, hv_d]
  ring

/-- Cauchy–Goursat: a rectangle lying strictly to the left of the imaginary axis avoids
the pole of `u ↦ u⁻¹`, so its boundary integral vanishes. -/
lemma rectBoundary_shifted_goursat_re_neg (a b c d : ℝ) (H : max a b < 0) :
    PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹) = 0 := by
  apply PL.AfeRect.rectBoundary_eq_zero_of_differentiableOn
  intro z hz
  have hzre : z.re ∈ [[a, b]] := (Complex.mem_reProdIm.mp hz).1
  have hzlt : z.re < 0 := by
    rcases Set.mem_uIcc.mp hzre with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact lt_of_le_of_lt h2 (lt_of_le_of_lt (le_max_right a b) H)
    · exact lt_of_le_of_lt h2 (lt_of_le_of_lt (le_max_left a b) H)
  have hz0 : z ≠ 0 := by
    intro hc
    have : z.re = 0 := congrArg Complex.re hc
    linarith
  exact ((differentiableAt_inv hz0).differentiableWithinAt)

/-- Cauchy–Goursat: a rectangle lying strictly to the right of the imaginary axis avoids
the pole of `u ↦ u⁻¹`, so its boundary integral vanishes. -/
lemma rectBoundary_shifted_goursat_re_pos (a b c d : ℝ) (H : 0 < min a b) :
    PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹) = 0 := by
  apply PL.AfeRect.rectBoundary_eq_zero_of_differentiableOn
  intro z hz
  have hzre : z.re ∈ [[a, b]] := (Complex.mem_reProdIm.mp hz).1
  have hzpos : 0 < z.re := by
    rcases Set.mem_uIcc.mp hzre with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact lt_of_lt_of_le H (le_trans (min_le_left a b) h1)
    · exact lt_of_lt_of_le H (le_trans (min_le_right a b) h1)
  have hz0 : z ≠ 0 := by
    intro hc
    have : z.re = 0 := congrArg Complex.re hc
    linarith
  exact ((differentiableAt_inv hz0).differentiableWithinAt)

/-- Cauchy–Goursat: a rectangle lying strictly below the real axis avoids the pole of
`u ↦ u⁻¹`, so its boundary integral vanishes. -/
lemma rectBoundary_shifted_goursat_im_neg (a b c d : ℝ) (H : max c d < 0) :
    PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹) = 0 := by
  apply PL.AfeRect.rectBoundary_eq_zero_of_differentiableOn
  intro z hz
  have hzim : z.im ∈ [[c, d]] := (Complex.mem_reProdIm.mp hz).2
  have hzlt : z.im < 0 := by
    rcases Set.mem_uIcc.mp hzim with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact lt_of_le_of_lt h2 (lt_of_le_of_lt (le_max_right c d) H)
    · exact lt_of_le_of_lt h2 (lt_of_le_of_lt (le_max_left c d) H)
  have hz0 : z ≠ 0 := by
    intro hc
    have : z.im = 0 := congrArg Complex.im hc
    linarith
  exact ((differentiableAt_inv hz0).differentiableWithinAt)

/-- Cauchy–Goursat: a rectangle lying strictly above the real axis avoids the pole of
`u ↦ u⁻¹`, so its boundary integral vanishes. -/
lemma rectBoundary_shifted_goursat_im_pos (a b c d : ℝ) (H : 0 < min c d) :
    PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹) = 0 := by
  apply PL.AfeRect.rectBoundary_eq_zero_of_differentiableOn
  intro z hz
  have hzim : z.im ∈ [[c, d]] := (Complex.mem_reProdIm.mp hz).2
  have hzpos : 0 < z.im := by
    rcases Set.mem_uIcc.mp hzim with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact lt_of_lt_of_le H (le_trans (min_le_left c d) h1)
    · exact lt_of_lt_of_le H (le_trans (min_le_right c d) h1)
  have hz0 : z ≠ 0 := by
    intro hc
    have : z.im = 0 := by simpa using congrArg Complex.im hc
    linarith
  exact ((differentiableAt_inv hz0).differentiableWithinAt)

/-- The boundary integral of `u ↦ u⁻¹` over any rectangle containing `0` in its interior
(with corners `⟨a,c⟩`, `⟨b,d⟩`, `a < 0 < b`, `c < 0 < d`) equals `2πi`. -/
theorem rectBoundary_shifted_inv_general (a b c d : ℝ) (ha : a < 0) (hb : 0 < b)
    (hc : c < 0) (hd : 0 < d) :
    PL.AfeRect.rectBoundary ⟨a, c⟩ ⟨b, d⟩ (fun u : ℂ => u⁻¹)
      = 2 * Real.pi * Complex.I := by
  have hmin : 0 < min (-c) d := lt_min (by linarith) hd
  set T₀ : ℝ := min (-c) d / 2 with hT₀def
  have hT₀pos : 0 < T₀ := by rw [hT₀def]; linarith
  have hT₀c : c < -T₀ := by
    rw [hT₀def]
    have := min_le_left (-c) d
    linarith
  have hT₀d : T₀ < d := by
    rw [hT₀def]
    have := min_le_right (-c) d
    linarith
  rw [rectBoundary_shifted_chain_y a b c d T₀ (ne_of_lt ha) (ne_of_gt hb)]
  rw [rectBoundary_shifted_goursat_im_neg a b c (-T₀) (by rw [max_lt_iff]; exact ⟨hc, by linarith⟩),
    rectBoundary_shifted_goursat_im_pos a b T₀ d (by rw [lt_min_iff]; exact ⟨hT₀pos, hd⟩)]
  rw [rectBoundary_shifted_chain_x a b (-T₀) T₀ (by linarith) (by linarith)]
  rw [rectBoundary_shifted_goursat_re_neg a (-1) (-T₀) T₀ (by rw [max_lt_iff]; exact ⟨ha, by norm_num⟩),
    rectBoundary_shifted_goursat_re_pos 1 b (-T₀) T₀ (by rw [lt_min_iff]; exact ⟨by norm_num, hb⟩)]
  rw [PL.AfeRect.rectBoundary_inv_corners T₀ hT₀pos]
  ring

/-- **Boundary integral of a shifted inverse.**  For `α` strictly inside the rectangle
`⟨-1,-T⟩ ⟨1,T⟩`, the boundary integral of `u ↦ (u - α)⁻¹` equals `2πi`. -/
theorem rectBoundary_shifted_inv (α : ℂ) (T : ℝ) (h0 : -1 < α.re) (h1 : α.re < 1)
    (hT : |α.im| < T) :
    PL.AfeRect.rectBoundary ⟨-1, -T⟩ ⟨1, T⟩ (fun u : ℂ => (u - α)⁻¹) = 2 * Real.pi * Complex.I := by
  have him := abs_lt.mp hT
  have hza : (⟨-1, -T⟩ : ℂ) - α = ⟨-1 - α.re, -T - α.im⟩ := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  have hwb : (⟨1, T⟩ : ℂ) - α = ⟨1 - α.re, T - α.im⟩ := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  rw [← rectBoundary_shifted_translate ⟨-1, -T⟩ ⟨1, T⟩ α (fun u : ℂ => u⁻¹), hza, hwb]
  exact rectBoundary_shifted_inv_general (-1 - α.re) (1 - α.re) (-T - α.im) (T - α.im)
    (by linarith) (by linarith) (by linarith [him.1]) (by linarith [him.2])

end

end Commons.NumberTheory.Zeta
