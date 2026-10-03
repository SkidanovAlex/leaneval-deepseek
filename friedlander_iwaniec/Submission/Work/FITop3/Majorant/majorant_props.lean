/-
# `Submission.Work.FITop3.Majorant.majorant_props` — the annulus majorant satisfies `IsMajorant`

The paper's majorant `f` of (5.17)/(5.19) is the product of two clamped quadratic ramps

  `majorant M u = sm ((u - M/4)/(3M/4)) · sm ((4M - u)/(2M))`

(`Submission.Work.FITop3.Smooth`): the first ramp rises from `0` at `u = M/4` to `1` at `M`, the
second falls from `1` at `2M` to `0` at `4M`.  Hence `f = 1` on the whole dyadic segment
`M ≤ u ≤ 2M`, `0 ≤ f ≤ 1`, and the support is `M/4 ≤ u ≤ 4M`.

The two discrete-derivative conditions are the product rule for finite differences.  With the two
step sizes `α = 1/(3M/4)` (the increment of the first ramp argument per unit of `u`) and
`β = 1/(2M)` (the decrement of the second), and using only

* `|Δ sm| ≤ 4δ` and `|Δ² sm| ≤ 12δ²` for `0 ≤ δ ≤ 1` (immediate from the quadratic estimates
  `2δ+2δ²` and `4δ²+8δ³` proved in `Submission.Work.FITop3.Smooth.sm_props`),

the first difference of the product is `≤ 4α + 4β = 22/(3M) ≤ 8/M` and the second is
`≤ 12α² + 32αβ + 12β² = 137/(3M²) ≤ 64/M²`.  Both are the constants written into
`Work.FITop3.IsMajorant`.

Everything is proved here from the ramp estimates of `Smooth.sm_props`; nothing else about `f` is
used, so the file is self-contained given the definition of `majorant`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props

set_option autoImplicit false

namespace Work.FITop3.Majorant

open Work.FITop3

noncomputable section

/-! ## 1. The ramp facts used (from `Smooth.sm_props`) -/

private lemma sm_nonneg (t : ℝ) : 0 ≤ Work.FITop3.sm t :=
  (Work.FITop3.Smooth.sm_props).1 t

private lemma sm_le_one (t : ℝ) : Work.FITop3.sm t ≤ 1 :=
  (Work.FITop3.Smooth.sm_props).2.1 t

private lemma sm_eq_zero_iff (t : ℝ) : Work.FITop3.sm t = 0 ↔ t ≤ 0 :=
  (Work.FITop3.Smooth.sm_props).2.2.1 t

private lemma sm_eq_one_iff (t : ℝ) : Work.FITop3.sm t = 1 ↔ 1 ≤ t :=
  (Work.FITop3.Smooth.sm_props).2.2.2.1 t

/-- `|sm (t+δ) - sm t| ≤ 4δ` for `0 ≤ δ ≤ 1`. -/
private lemma sm_step (t δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    |Work.FITop3.sm (t + δ) - Work.FITop3.sm t| ≤ 4 * δ := by
  have h := (Work.FITop3.Smooth.sm_props).2.2.2.2.1 t δ hδ
  nlinarith [sq_nonneg δ]

/-- `|Δ² sm| ≤ 12δ²` for `0 ≤ δ ≤ 1`. -/
private lemma sm_step2 (t δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    |Work.FITop3.sm (t + 2 * δ) - 2 * Work.FITop3.sm (t + δ) + Work.FITop3.sm t| ≤ 12 * δ ^ 2 := by
  have h := (Work.FITop3.Smooth.sm_props).2.2.2.2.2 t δ hδ
  nlinarith [sq_nonneg δ, mul_le_mul_of_nonneg_left hδ1 (sq_nonneg δ)]

/-! ## 2. The finite-difference product rules -/

/-- `Δ(fg) = Δf·g(1) + f(0)·Δg`. -/
private lemma abs_mul_sub_le {A B C D a b : ℝ}
    (hA : |A - B| ≤ a) (hC : |C - D| ≤ b) (hC1 : |C| ≤ 1) (hB1 : |B| ≤ 1) :
    |A * C - B * D| ≤ a + b := by
  have ha : 0 ≤ a := le_trans (abs_nonneg _) hA
  have key : A * C - B * D = (A - B) * C + B * (C - D) := by ring
  rw [key]
  calc |(A - B) * C + B * (C - D)| ≤ |(A - B) * C| + |B * (C - D)| := abs_add_le _ _
    _ = |A - B| * |C| + |B| * |C - D| := by rw [abs_mul, abs_mul]
    _ ≤ a * 1 + 1 * b := by
        apply add_le_add
        · exact mul_le_mul hA hC1 (abs_nonneg _) ha
        · exact mul_le_mul hB1 hC (abs_nonneg _) (by norm_num)
    _ = a + b := by ring

/-- `Δ²(fg) = Δ²f·g(2) + 2Δf·Δg + f(0)·Δ²g`. -/
private lemma abs_mul_second_diff_le {A0 A1 A2 B0 B1 B2 a a' b b' : ℝ}
    (hA : |A2 - 2 * A1 + A0| ≤ a) (hB : |B2 - 2 * B1 + B0| ≤ b)
    (hdA : |A1 - A0| ≤ a') (hdB : |B2 - B1| ≤ b')
    (hB2 : |B2| ≤ 1) (hA0 : |A0| ≤ 1) :
    |A2 * B2 - 2 * (A1 * B1) + A0 * B0| ≤ a + 2 * (a' * b') + b := by
  have ha : 0 ≤ a := le_trans (abs_nonneg _) hA
  have ha' : 0 ≤ a' := le_trans (abs_nonneg _) hdA
  have key : A2 * B2 - 2 * (A1 * B1) + A0 * B0
      = (A2 - 2 * A1 + A0) * B2 + 2 * ((A1 - A0) * (B2 - B1)) + A0 * (B2 - 2 * B1 + B0) := by
    ring
  rw [key]
  have h1 := abs_add_three ((A2 - 2 * A1 + A0) * B2) (2 * ((A1 - A0) * (B2 - B1)))
    (A0 * (B2 - 2 * B1 + B0))
  simp only [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)] at h1
  have e1 : |A2 - 2 * A1 + A0| * |B2| ≤ a * 1 := mul_le_mul hA hB2 (abs_nonneg _) ha
  have e2 : 2 * (|A1 - A0| * |B2 - B1|) ≤ 2 * (a' * b') := by
    have : |A1 - A0| * |B2 - B1| ≤ a' * b' := mul_le_mul hdA hdB (abs_nonneg _) ha'
    linarith
  have e3 : |A0| * |B2 - 2 * B1 + B0| ≤ 1 * b := mul_le_mul hA0 hB (abs_nonneg _) (by norm_num)
  linarith [h1, e1, e2, e3]

/-! ## 3. The two finite differences of `sm x · sm y` when the arguments move apart -/

/-- Moving the first argument up by `α` and the second down by `β` costs `4α + 4β`. -/
private lemma sm_prod_step (x y α β : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    |Work.FITop3.sm (x + α) * Work.FITop3.sm (y - β) - Work.FITop3.sm x * Work.FITop3.sm y|
      ≤ 4 * α + 4 * β := by
  have hA : |Work.FITop3.sm (x + α) - Work.FITop3.sm x| ≤ 4 * α := sm_step x α hα hα1
  have hC : |Work.FITop3.sm (y - β) - Work.FITop3.sm y| ≤ 4 * β := by
    have h := sm_step (y - β) β hβ hβ1
    rwa [show y - β + β = y by ring, abs_sub_comm] at h
  exact abs_mul_sub_le hA hC (by rw [abs_of_nonneg (sm_nonneg _)]; exact sm_le_one _)
    (by rw [abs_of_nonneg (sm_nonneg _)]; exact sm_le_one _)

/-- The second difference of the product, `12α² + 32αβ + 12β²`. -/
private lemma sm_prod_second_step (x y α β : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    |Work.FITop3.sm (x + 2 * α) * Work.FITop3.sm (y - 2 * β)
      - 2 * (Work.FITop3.sm (x + α) * Work.FITop3.sm (y - β))
      + Work.FITop3.sm x * Work.FITop3.sm y|
      ≤ 12 * α ^ 2 + 32 * α * β + 12 * β ^ 2 := by
  have hF : |Work.FITop3.sm (x + 2 * α) - 2 * Work.FITop3.sm (x + α) + Work.FITop3.sm x|
      ≤ 12 * α ^ 2 := sm_step2 x α hα hα1
  have hG : |Work.FITop3.sm (y - 2 * β) - 2 * Work.FITop3.sm (y - β) + Work.FITop3.sm y|
      ≤ 12 * β ^ 2 := by
    have h := sm_step2 (y - 2 * β) β hβ hβ1
    rw [show y - 2 * β + 2 * β = y by ring, show y - 2 * β + β = y - β by ring] at h
    rwa [show Work.FITop3.sm y - 2 * Work.FITop3.sm (y - β) + Work.FITop3.sm (y - 2 * β)
        = Work.FITop3.sm (y - 2 * β) - 2 * Work.FITop3.sm (y - β) + Work.FITop3.sm y by ring] at h
  have hdF : |Work.FITop3.sm (x + α) - Work.FITop3.sm x| ≤ 4 * α := sm_step x α hα hα1
  have hdG : |Work.FITop3.sm (y - 2 * β) - Work.FITop3.sm (y - β)| ≤ 4 * β := by
    have h := sm_step (y - 2 * β) β hβ hβ1
    rwa [show y - 2 * β + β = y - β by ring, abs_sub_comm] at h
  have hB2 : |Work.FITop3.sm (y - 2 * β)| ≤ 1 := by
    rw [abs_of_nonneg (sm_nonneg _)]; exact sm_le_one _
  have hA0 : |Work.FITop3.sm x| ≤ 1 := by
    rw [abs_of_nonneg (sm_nonneg _)]; exact sm_le_one _
  have hmain := abs_mul_second_diff_le hF hG hdF hdG hB2 hA0
  have heq : 12 * α ^ 2 + 2 * (4 * α * (4 * β)) + 12 * β ^ 2
      = 12 * α ^ 2 + 32 * α * β + 12 * β ^ 2 := by
    ring
  rwa [heq] at hmain

/-! ## 4. The two finite differences of the majorant itself -/

/-- `|Δ majorant| ≤ 4·(4/(3M)) + 4·(1/(2M)) = 22/(3M)` for `M ≥ 4`. -/
private lemma majorant_first_diff (M : ℝ) (hM : 4 ≤ M) (u : ℤ) :
    |Work.FITop3.majorant M (u + 1) - Work.FITop3.majorant M u|
      ≤ 4 * (1 / (3 * M / 4)) + 4 * (1 / (2 * M)) := by
  have hMpos : (0:ℝ) < M := by linarith
  have hα0 : (0:ℝ) ≤ 1 / (3 * M / 4) := by positivity
  have hα1 : (1:ℝ) / (3 * M / 4) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hβ0 : (0:ℝ) ≤ 1 / (2 * M) := by positivity
  have hβ1 : (1:ℝ) / (2 * M) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hxa : (((u + 1 : ℤ) : ℝ) - M / 4) / (3 * M / 4)
      = (((u : ℤ) : ℝ) - M / 4) / (3 * M / 4) + 1 / (3 * M / 4) := by
    have h2 : (((u + 1 : ℤ) : ℝ) - M / 4) = (((u : ℤ) : ℝ) - M / 4) + 1 := by push_cast; ring
    rw [h2, add_div]
  have hyb : (4 * M - ((u + 1 : ℤ) : ℝ)) / (2 * M)
      = (4 * M - ((u : ℤ) : ℝ)) / (2 * M) - 1 / (2 * M) := by
    have h2 : 4 * M - ((u + 1 : ℤ) : ℝ) = (4 * M - ((u : ℤ) : ℝ)) - 1 := by push_cast; ring
    rw [h2, sub_div]
  rw [Work.FITop3.majorant, Work.FITop3.majorant, hxa, hyb]
  exact sm_prod_step _ _ _ _ hα0 hα1 hβ0 hβ1

/-- `|Δ² majorant| ≤ 12·α² + 32·αβ + 12·β² = 137/(3M²)` with `α = 4/(3M)`, `β = 1/(2M)`. -/
private lemma majorant_second_diff (M : ℝ) (hM : 4 ≤ M) (u : ℤ) :
    |Work.FITop3.majorant M (u + 2) - 2 * Work.FITop3.majorant M (u + 1) + Work.FITop3.majorant M u|
      ≤ 12 * (1 / (3 * M / 4)) ^ 2 + 32 * (1 / (3 * M / 4)) * (1 / (2 * M))
        + 12 * (1 / (2 * M)) ^ 2 := by
  have hMpos : (0:ℝ) < M := by linarith
  have hα0 : (0:ℝ) ≤ 1 / (3 * M / 4) := by positivity
  have hα1 : (1:ℝ) / (3 * M / 4) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hβ0 : (0:ℝ) ≤ 1 / (2 * M) := by positivity
  have hβ1 : (1:ℝ) / (2 * M) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hxa : (((u + 1 : ℤ) : ℝ) - M / 4) / (3 * M / 4)
      = (((u : ℤ) : ℝ) - M / 4) / (3 * M / 4) + 1 / (3 * M / 4) := by
    have h2 : (((u + 1 : ℤ) : ℝ) - M / 4) = (((u : ℤ) : ℝ) - M / 4) + 1 := by push_cast; ring
    rw [h2, add_div]
  have hxa2 : (((u + 2 : ℤ) : ℝ) - M / 4) / (3 * M / 4)
      = (((u : ℤ) : ℝ) - M / 4) / (3 * M / 4) + 2 * (1 / (3 * M / 4)) := by
    have h2 : (((u + 2 : ℤ) : ℝ) - M / 4) = (((u : ℤ) : ℝ) - M / 4) + 2 := by push_cast; ring
    rw [h2, add_div]
    ring
  have hyb : (4 * M - ((u + 1 : ℤ) : ℝ)) / (2 * M)
      = (4 * M - ((u : ℤ) : ℝ)) / (2 * M) - 1 / (2 * M) := by
    have h2 : 4 * M - ((u + 1 : ℤ) : ℝ) = (4 * M - ((u : ℤ) : ℝ)) - 1 := by push_cast; ring
    rw [h2, sub_div]
  have hyb2 : (4 * M - ((u + 2 : ℤ) : ℝ)) / (2 * M)
      = (4 * M - ((u : ℤ) : ℝ)) / (2 * M) - 2 * (1 / (2 * M)) := by
    have h2 : 4 * M - ((u + 2 : ℤ) : ℝ) = (4 * M - ((u : ℤ) : ℝ)) - 2 := by push_cast; ring
    rw [h2, sub_div]
    ring
  rw [Work.FITop3.majorant, Work.FITop3.majorant, Work.FITop3.majorant, hxa, hxa2, hyb, hyb2]
  exact sm_prod_second_step _ _ _ _ hα0 hα1 hβ0 hβ1

/-! ## 5. The target -/

theorem majorant_props (Pa : Work.FITop.Params) (hM : 4 ≤ Pa.M) :
    Work.FITop3.IsMajorant Pa (Work.FITop3.majorant Pa.M) := by
  have hMpos : (0:ℝ) < Pa.M := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [Work.FITop3.majorant]
    exact mul_nonneg (sm_nonneg _) (sm_nonneg _)
  · intro u
    rw [Work.FITop3.majorant]
    exact mul_le_one₀ (sm_le_one _) (sm_nonneg _) (sm_le_one _)
  · intro w h1 h2
    rw [Work.FITop3.majorant]
    simp only [Int.cast_natCast] at h1 h2 ⊢
    have hx : 1 ≤ ((Work.FIPlan.gnorm w : ℝ) - Pa.M / 4) / (3 * Pa.M / 4) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * Pa.M / 4)]
      linarith
    have hy : 1 ≤ (4 * Pa.M - (Work.FIPlan.gnorm w : ℝ)) / (2 * Pa.M) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Pa.M)]
      linarith
    rw [(sm_eq_one_iff _).mpr hx, (sm_eq_one_iff _).mpr hy, one_mul]
  · intro u h
    rw [Work.FITop3.majorant] at h
    rw [mul_ne_zero_iff] at h
    constructor
    · have h1 : 0 < (((u : ℤ) : ℝ) - Pa.M / 4) / (3 * Pa.M / 4) := by
        by_contra hc
        exact h.1 ((sm_eq_zero_iff _).mpr (not_lt.mp hc))
      have h2 := (div_pos_iff_of_pos_right (by positivity : (0:ℝ) < 3 * Pa.M / 4)).mp h1
      linarith
    · have h1 : 0 < (4 * Pa.M - ((u : ℤ) : ℝ)) / (2 * Pa.M) := by
        by_contra hc
        exact h.2 ((sm_eq_zero_iff _).mpr (not_lt.mp hc))
      have h2 := (div_pos_iff_of_pos_right (by positivity : (0:ℝ) < 2 * Pa.M)).mp h1
      linarith
  · intro u
    refine le_trans (majorant_first_diff Pa.M hM u) ?_
    have hp : (0:ℝ) < Pa.M := hMpos
    field_simp
    linarith
  · intro u
    refine le_trans (majorant_second_diff Pa.M hM u) ?_
    have hp : (0:ℝ) < Pa.M := hMpos
    field_simp
    linarith

end

end Work.FITop3.Majorant
