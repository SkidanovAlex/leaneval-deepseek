import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.OffAxis.G72Defs
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.G72SmallSB
import Submission.Work.ZeroFreeTables.OffAxis.G72B2Cells
import Submission.Work.ZeroFreeTables.OffAxis.G72GridMain
import Submission.Work.ZeroFreeTables.OffAxis.G72LargeSigma
import Submission.Work.ZeroFreeTables.OffAxis.G72RA72Bound
import Submission.Work.ZeroFreeTables.OffAxis.G72TrigBound
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables

/-! ## The bridge: `tf72Fc` at `λ = 6/7` is `G72` at the rescaled argument

`tf72f 1` and `g72` agree on `[0,2]`, so the Laplace transform of the test function at the
self-similar scale `λ = 1` has the same real part as `G72`; and `tf72Fc` is scale-invariant
(`tf72Fc_scale`, HB Lemma 7.2's scaling). Two rewriting lemmas are also provided for the
arguments `(-a + iµ)/(6/7)` and `(iµ)/(6/7)` that occur in the target statement. -/

/-- `Re (tf72Fc 1 w) = Re (G72 w)`: on `[0,2]` the test function `tf72f 1` is `g72`. -/
theorem tf72Fc_one_re_eq_G72 (w : ℂ) :
    (tf72Fc 1 w).re = (G72 w).re := by
  unfold tf72Fc G72
  rw [show (2:ℝ)/1 = 2 by norm_num]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht2 : t ∈ Set.Icc (0:ℝ) (2/1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at ht
    rwa [show (2:ℝ)/1 = 2 by norm_num]
  show Complex.exp (-(w * (t:ℂ))) * ((tf72f 1 t : ℝ) : ℂ)
      = Complex.exp (-(w * (t:ℂ))) * ((g72 t : ℝ) : ℂ)
  rw [tf72f_eq_poly 1 (by norm_num) t ht2]
  unfold g72
  norm_num

/-- `Re (tf72Fc (6/7) z) = Re (G72 (z/(6/7)))`. -/
theorem tf72Fc_six_sevenths_re (z : ℂ) :
    (tf72Fc (6/7) z).re = (G72 (z / ((6/7 : ℝ) : ℂ))).re := by
  rw [tf72Fc_scale (6/7) (by norm_num) z, tf72Fc_one_re_eq_G72]

/-- `(-a + iµ) / (6/7) = -(7a/6) + i(7µ/6)`. -/
lemma div_six_sevenths (a μ : ℝ) :
    (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I) / ((6/7 : ℝ) : ℂ)
      = (((-(7*a/6) : ℝ)) : ℂ) + (((7*μ/6 : ℝ)) : ℂ) * Complex.I := by
  have h : (((6:ℝ)/7) : ℂ) ≠ 0 := by norm_num
  have h2 : ((6/7 : ℝ) : ℂ) = (((6:ℝ)/7) : ℂ) := by norm_num
  rw [h2, div_eq_mul_inv, show ((((6:ℝ)/7) : ℂ))⁻¹ = (((7:ℝ)/6) : ℂ) by norm_num]
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- `(iµ) / (6/7) = i(7µ/6)`. -/
lemma div_six_sevenths_I (μ : ℝ) :
    ((μ : ℂ) * Complex.I) / ((6/7 : ℝ) : ℂ) = (((7*μ/6 : ℝ)) : ℂ) * Complex.I := by
  have h : (((6:ℝ)/7) : ℂ) ≠ 0 := by norm_num
  have h2 : ((6/7 : ℝ) : ℂ) = (((6:ℝ)/7) : ℂ) := by norm_num
  rw [h2, div_eq_mul_inv, show ((((6:ℝ)/7) : ℂ))⁻¹ = (((7:ℝ)/6) : ℂ) by norm_num]
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-! ## Evenness in `σ`

Both (10.8) and the one-sided large-`µ` bound `Re F(-λ₁+iµ) ≤ f(0)/6` are even in the imaginary
part `µ`, so we may always reduce to `σ ≥ 0`. -/

/-- `Re G72(-s + iσ)` is even in `σ`. -/
lemma G72_re_neg_im (s σ : ℝ) :
    (G72 (((-s : ℝ) : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)).re
      = (G72 (((-s : ℝ) : ℂ) + (σ : ℝ) * Complex.I)).re := by
  rw [G72_re_eq_integral, G72_re_eq_integral]
  apply intervalIntegral.integral_congr
  intro y _
  have h1 : (((-s : ℝ) : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I).re = -s := by simp
  have h2 : (((-s : ℝ) : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I).im = -σ := by simp
  have h3 : (((-s : ℝ) : ℂ) + (σ : ℝ) * Complex.I).re = -s := by simp
  have h4 : (((-s : ℝ) : ℂ) + (σ : ℝ) * Complex.I).im = σ := by simp
  rw [h1, h2, h3, h4]
  simp

/-- `Isub s σ` is even in `σ`. -/
lemma Isub_neg (s σ : ℝ) : Isub s (-σ) = Isub s σ := by
  rw [Isub_eq_integral, Isub_eq_integral]
  apply intervalIntegral.integral_congr
  intro y _
  simp [Real.cos_neg]

/-! ## HB (10.8) at `λ = 6/7`, scale-free form -/

/-- **HB (10.8) at `λ = 6/7`, scale-free form**: `Isub s σ ≤ 16/105` for `0 ≤ s ≤ 1`, `0 ≤ σ`.

This is the numerical core of Heath-Brown's Lemma 10.2.  The quadrant is covered by the
`F`-method cells of `G72SmallS` (for `s ≤ 7/25`), `B2cell_1`–`B2cell_8`, the grid `grid_main`
and `G72LargeSigma`. -/
theorem Isub_le_ten_eight (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ0 : 0 ≤ σ) :
    Isub s σ ≤ 16/105 := by
  rcases le_or_gt s (7/25) with hs | hs
  · exact G72SmallS s σ hs0 hs hσ0
  · have hs' : (7:ℝ)/25 < s := hs
    rcases le_or_gt σ (51/20) with hσ | hσ
    · rcases le_or_gt s (3/10) with h | h
      · exact B2cell_1 s σ (le_of_lt hs') h hσ0 hσ
      · have h' : (3:ℝ)/10 < s := h
        rcases le_or_gt s (7/20) with h2 | h2
        · exact B2cell_2 s σ (le_of_lt h') h2 hσ0 hσ
        · have h2' : (7:ℝ)/20 < s := h2
          rcases le_or_gt s (1/2) with h3 | h3
          · exact B2cell_3 s σ (le_of_lt h2') h3 hσ0 hσ
          · have h3' : (1:ℝ)/2 < s := h3
            rcases le_or_gt s (3/5) with h4 | h4
            · exact B2cell_4 s σ (le_of_lt h3') h4 hσ0 hσ
            · have h4' : (3:ℝ)/5 < s := h4
              rcases le_or_gt s (7/10) with h5 | h5
              · exact B2cell_5 s σ (le_of_lt h4') h5 hσ0 hσ
              · have h5' : (7:ℝ)/10 < s := h5
                rcases le_or_gt s (4/5) with h6 | h6
                · exact B2cell_6 s σ (le_of_lt h5') h6 hσ0 (by linarith [hσ])
                · have h6' : (4:ℝ)/5 < s := h6
                  rcases le_or_gt s (9/10) with h7 | h7
                  · exact B2cell_7 s σ (le_of_lt h6') h7 hσ0 (by linarith [hσ])
                  · exact B2cell_8 s σ (le_of_lt h7) (by linarith [hs1]) hσ0 (by linarith [hσ])
    · have hσ' : (51:ℝ)/20 < σ := hσ
      rcases le_or_gt σ (18/5) with hσ2 | hσ2
      · rcases le_or_gt s (73/100) with h | h
        · exact grid_main s σ (le_of_lt hs') h (le_of_lt hσ') hσ2
        · have h' : (73:ℝ)/100 < s := h
          rcases le_or_gt s (4/5) with h5 | h5
          · exact B2cell_6 s σ (by linarith [h']) h5 hσ0 hσ2
          · have h5' : (4:ℝ)/5 < s := h5
            rcases le_or_gt s (9/10) with h6 | h6
            · exact B2cell_7 s σ (le_of_lt h5') h6 hσ0 hσ2
            · exact B2cell_8 s σ (le_of_lt h6) (by linarith [hs1]) hσ0 hσ2
      · exact G72LargeSigma (fun w hw => G72_eq_closed hw) G72ImagNonneg s σ hs0 hs1 (by linarith)

/-- **HB (10.8), scale-free form, with `σ` of either sign.** -/
theorem Isub_le_ten_eight_abs (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hσ : |σ| ≤ 14/3) : Isub s σ ≤ 16/105 := by
  rcases le_or_gt σ 0 with h | h
  · have h2 : 0 ≤ -σ := by linarith
    have h3 : Isub s (-σ) ≤ 16/105 := Isub_le_ten_eight s (-σ) hs0 hs1 h2
    rwa [Isub_neg] at h3
  · exact Isub_le_ten_eight s σ hs0 hs1 (le_of_lt h)

/-! ## HB (10.9) at `λ = 6/7`: large imaginary part

For `µ ≥ 4` (i.e. `σ ≥ 14/3` in the rescaled variable) Heath-Brown's integration by parts gives
`Re F(-λ₁+iµ) ≤ 8λ⁴(e²+1)|s|⁻⁴`, well below `f(0)/6 = 16/105`.  In the algebraic form of
`G72ReClosed0` the same bound is obtained from `G72RA72Bound` (the rational part), the amplitude
bound `G72TrigBound` for the trigonometric part, the case estimate `G72_LHS_le` for the
`s`-dependent piece and the elementary tail `4/σ⁴ + 4/σ⁶ ≤ 1/100`. -/

/-- **Large imaginary part**: `Re G72(-s+iσ) ≤ 16/105` for `0 ≤ s ≤ 1` and `σ ≥ 14/3`. -/
theorem G72_re_large_im (s σ : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hσ : 14/3 ≤ σ) :
    (G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re ≤ 16/105 := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hρ : s^2 + σ^2 ≠ 0 := by positivity
  have h36 : (36:ℝ)/10 ≤ σ := by linarith
  rw [G72ReClosed0 hρ]
  have hRA := G72RA72Bound s σ hs hs1 h36
  have hLHS := G72_LHS_le s σ hs hs1 h36
  have htrig := G72TrigBound s σ
  have htrig' : Real.exp (2*s) * (Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ)
      ≤ 4 * Real.exp (2*s) * ((1-s)^2 + σ^2) / (s^2 + σ^2)^3 := by
    have h1 : Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ
        ≤ 4 * ((1-s)^2 + σ^2) / (s^2 + σ^2)^3 := le_trans (le_abs_self _) htrig
    calc Real.exp (2*s) * (Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ)
        ≤ Real.exp (2*s) * (4 * ((1-s)^2 + σ^2) / (s^2 + σ^2)^3) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
      _ = 4 * Real.exp (2*s) * ((1-s)^2 + σ^2) / (s^2 + σ^2)^3 := by ring
  have htail : 4/σ^4 + 4/σ^6 ≤ 1/100 := by
    have hpos : (0:ℝ) < 14/3 := by norm_num
    have h4 : ((14:ℝ)/3)^4 ≤ σ^4 := pow_le_pow_left₀ hpos.le hσ 4
    have h6 : ((14:ℝ)/3)^6 ≤ σ^6 := pow_le_pow_left₀ hpos.le hσ 6
    have h1 : 4/σ^4 ≤ 4/(((14:ℝ)/3)^4) := div_le_div_of_nonneg_left (by norm_num) (by positivity) h4
    have h2 : 4/σ^6 ≤ 4/(((14:ℝ)/3)^6) := div_le_div_of_nonneg_left (by norm_num) (by positivity) h6
    have h3 : 4/(((14:ℝ)/3)^4) + 4/(((14:ℝ)/3)^6) ≤ 1/100 := by norm_num
    linarith [h1, h2, h3]
  linarith [hRA, hLHS, htrig', htail]

/-- **HB (10.9), scale-free form, `σ` of either sign**: for `|σ| ≥ 14/3`,
`Re G72(-s+iσ) ≤ 16/105`. -/
theorem G72_re_le_ten_eight (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : 14/3 ≤ |σ|) :
    (G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re ≤ 16/105 := by
  rcases le_or_gt σ 0 with h | h
  · have h2 : (14:ℝ)/3 ≤ -σ := by rw [abs_of_nonpos h] at hσ; linarith
    have h3 := G72_re_large_im s (-σ) hs0 hs1 h2
    rwa [G72_re_neg_im] at h3
  · have h2 : (14:ℝ)/3 ≤ σ := by rw [abs_of_pos h] at hσ; exact hσ
    exact G72_re_large_im s σ hs0 hs1 h2

/-! ## The target -/

theorem tf72Fc_ten_eight :
    (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → |μ| ≤ 4 →
      (Work.ZeroFreeTables.tf72Fc (6/7) (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        - 2 * (Work.ZeroFreeTables.tf72Fc (6/7) ((μ : ℂ) * Complex.I)).re ≤ 16/105)
    ∧ (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → 4 ≤ |μ| →
      (Work.ZeroFreeTables.tf72Fc (6/7) (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ 16/105) := by
  constructor
  · intro a μ ha ha2 hμ
    have hs0 : 0 ≤ 7*a/6 := by linarith
    have hs1 : 7*a/6 ≤ 1 := by linarith
    have hσ : |7*μ/6| ≤ 14/3 := by
      have h : |7*μ/6| = 7*|μ|/6 := by rw [abs_div, abs_mul]; norm_num
      rw [h]; linarith
    rw [tf72Fc_six_sevenths_re (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I),
      tf72Fc_six_sevenths_re ((μ : ℂ) * Complex.I),
      div_six_sevenths a μ, div_six_sevenths_I μ]
    exact Isub_le_ten_eight_abs (7*a/6) (7*μ/6) hs0 hs1 hσ
  · intro a μ ha ha2 hμ
    have hs0 : 0 ≤ 7*a/6 := by linarith
    have hs1 : 7*a/6 ≤ 1 := by linarith
    have hσ : (14:ℝ)/3 ≤ |7*μ/6| := by
      have h : |7*μ/6| = 7*|μ|/6 := by rw [abs_div, abs_mul]; norm_num
      rw [h]; linarith
    rw [tf72Fc_six_sevenths_re (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I), div_six_sevenths a μ]
    exact G72_re_le_ten_eight (7*a/6) (7*μ/6) hs0 hs1 hσ

end Work.ZeroFreeTables.OffAxis
end
