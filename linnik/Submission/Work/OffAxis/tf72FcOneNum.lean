import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.OffAxis.Tf72One.Core
import Submission.Work.OffAxis.Tf72One.C_le
import Submission.Work.OffAxis.Tf72One.R_le_crude
import Submission.Work.OffAxis.Tf72One.Isub_le_small_sigma
import Submission.Work.OffAxis.Tf72One.cell_0
import Submission.Work.OffAxis.Tf72One.cell_1
import Submission.Work.OffAxis.Tf72One.cell_2
import Submission.Work.OffAxis.Tf72One.cell_3
import Submission.Work.OffAxis.Tf72One.cell_4
import Submission.Work.OffAxis.Tf72One.cell_5
import Submission.Work.OffAxis.Tf72One.cell_6
import Submission.Work.OffAxis.Tf72One.cell_7
import Submission.Work.OffAxis.Tf72One.cell_8
import Submission.Work.OffAxis.Tf72One.cell_9
import Submission.Work.OffAxis.Tf72One.cell_10
import Submission.Work.OffAxis.Tf72One.cell_11

noncomputable section

namespace Work.OffAxis

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-- On the real part of `G72`, the imaginary part of the argument enters only through
`cos (z.im * y)`. -/
theorem G72_re_cos_form (a μ : ℝ) :
    (G72 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.exp (a * y) * Real.cos (μ * y) * g72 y := by
  rw [G72_re_eq_integral]
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  ring

/-- `Re G72(-a+iμ)` is even in `μ`. -/
theorem G72_re_even_aux (a μ : ℝ) :
    (G72 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
      = (G72 (((-a : ℝ) : ℂ) + ((|μ| : ℝ) : ℂ) * Complex.I)).re := by
  rw [G72_re_cos_form a μ, G72_re_cos_form a |μ|]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy0 : 0 ≤ y := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hy
    exact hy.1
  have h1 : |μ| * y = |μ * y| := by rw [abs_mul, abs_of_nonneg hy0]
  simp only [h1, Real.cos_abs]

/-- The grid part of HB (10.8): `Isub a σ ≤ 1/100` for `a ∈ [0,17/16]`, `σ ∈ [3/4,5]`. -/
theorem Isub_grid_aux : ∀ a σ : ℝ, 0 ≤ a → a ≤ 17/16 → 3/4 ≤ σ → σ ≤ 5 →
    Isub a σ ≤ 1/100 := by
  intro a σ ha0 ha hσ0 hσ1
  rcases le_or_gt σ (7/4) with h | h
  · exact Work.OffAxis.Tf72One.cell_0 a σ ha0 ha hσ0 h
  · rcases le_or_gt σ (5/2) with h2 | h2
    · exact Work.OffAxis.Tf72One.cell_1 a σ ha0 ha (le_of_lt h) h2
    · rcases le_or_gt σ 3 with h3 | h3
      · exact Work.OffAxis.Tf72One.cell_2 a σ ha0 ha (le_of_lt h2) h3
      · rcases le_or_gt σ (13/4) with h4 | h4
        · exact Work.OffAxis.Tf72One.cell_3 a σ ha0 ha (le_of_lt h3) h4
        · rcases le_or_gt σ (7/2) with h5 | h5
          · exact Work.OffAxis.Tf72One.cell_4 a σ ha0 ha (le_of_lt h4) h5
          · rcases le_or_gt σ (15/4) with h6 | h6
            · exact Work.OffAxis.Tf72One.cell_5 a σ ha0 ha (le_of_lt h5) h6
            · rcases le_or_gt σ 4 with h7 | h7
              · exact Work.OffAxis.Tf72One.cell_6 a σ ha0 ha (le_of_lt h6) h7
              · rcases le_or_gt σ (21/5) with h8 | h8
                · exact Work.OffAxis.Tf72One.cell_7 a σ ha0 ha (le_of_lt h7) h8
                · rcases le_or_gt σ (22/5) with h9 | h9
                  · exact Work.OffAxis.Tf72One.cell_8 a σ ha0 ha (le_of_lt h8) h9
                  · rcases le_or_gt σ (23/5) with h10 | h10
                    · exact Work.OffAxis.Tf72One.cell_9 a σ ha0 ha (le_of_lt h9) h10
                    · rcases le_or_gt σ (24/5) with h11 | h11
                      · exact Work.OffAxis.Tf72One.cell_10 a σ ha0 ha (le_of_lt h10) h11
                      · exact Work.OffAxis.Tf72One.cell_11 a σ ha0 ha (le_of_lt h11) hσ1

/-- **HB (10.8)/(10.9) verified for the Lemma 7.2 test function**, in the self-similar
normalisation `λ = 1` (`tf72Fc 1`, i.e. `Φ z = ∫₀² e^{-zt} f₁(t)dt`): the `max` in (10.8) is
negative on the compact range and (10.9) is small for `|μ| ≥ 4`. Both bounds carry a wide margin
(HB's own numbers: the worst grid value of (10.8) is `≤ 0`, while (10.9) gives
`≤ 8λ⁴(e²+1)μ^{-4} ≤ 8/45`), and the constants `1/100` and `1/10` are what the transfer to
`tf72T (6/7)` needs (see `Work.OffAxis.num_transfer`). Suggested route: HB's proof of (10.8) — the
derivative bounds (10.10)/(10.11) (`|Φ'(s)| ≤ ∫₀² x e^x f₁ ≤ 16/15` for `-1 ≤ Re s ≤ 0`,
`|Φ'(iμ)| ≤ ∫₀² x f₁ = 16/35`) give Lipschitz continuity, so a finite grid of values controls the
maximum, and the grid values are explicit integrals of the polynomial `f₁`; alternatively bound
`∫₀² (e^{au}-2)cos(μu) (1/30)(2-u)³(4+6u+u²) du` directly by Taylor bounds on `e^{au}`, `cos(μu)`
(the substitution `u = λt` in `tf72Fc_scale` puts it in this form) and integrate the resulting
polynomials exactly; for the second conjunct the `|μ| ≥ 4` case follows from HB's (10.9) expansion
`Re Φ(s) ≤ 8(e²+1)‖s‖^{-4}` for `Re s ≥ -1`, `4 ≤ |Im s|`. -/
theorem tf72FcOneNum :
    (∀ a μ : ℝ, 0 ≤ a → a ≤ 17/16 → |μ| ≤ 5 →
      (Work.ZeroFreeTables.tf72Fc 1 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        - 2 * (Work.ZeroFreeTables.tf72Fc 1 ((μ : ℂ) * Complex.I)).re ≤ 1/100)
    ∧ (∀ a μ : ℝ, 0 ≤ a → a ≤ 17/16 → 4 ≤ |μ| →
      (Work.ZeroFreeTables.tf72Fc 1 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ 1/10) := by
  have hbr : ∀ z : ℂ, Work.ZeroFreeTables.tf72Fc 1 z = Work.ZeroFreeTables.G72 z :=
    Work.OffAxis.Tf72One.tf72Fc_one_eq_G72
  constructor
  · intro a μ ha0 ha hμ
    have h1 : (Work.ZeroFreeTables.tf72Fc 1 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        = (G72 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re := by rw [hbr]
    have h2 : (Work.ZeroFreeTables.tf72Fc 1 ((μ : ℂ) * Complex.I)).re
        = (G72 ((μ : ℂ) * Complex.I)).re := by rw [hbr]
    rw [h1, h2]
    have hmain : Isub a |μ| ≤ 1/100 := by
      rcases le_or_gt |μ| (3/4) with h | h
      · exact Work.OffAxis.Tf72One.Isub_le_small_sigma a |μ| ha0 ha (by simpa [abs_abs] using h)
      · exact Isub_grid_aux a |μ| ha0 ha (le_of_lt h) hμ
    change Isub a μ ≤ 1/100
    rwa [Work.OffAxis.Tf72One.Isub_abs a μ]
  · intro a μ ha0 ha hμ
    have h1 : (Work.ZeroFreeTables.tf72Fc 1 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        = (G72 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re := by rw [hbr]
    rw [h1, G72_re_even_aux a μ]
    by_cases h5 : |μ| ≤ 5
    · have hcell : Isub a |μ| ≤ 1/100 :=
        Isub_grid_aux a |μ| ha0 ha (by linarith : (3:ℝ)/4 ≤ |μ|) h5
      have hC : (G72 (((|μ| : ℝ) : ℂ) * Complex.I)).re ≤ 10 / |μ| ^ 4 :=
        Work.OffAxis.Tf72One.C_le |μ| hμ
      have hsplit : (G72 (((-a : ℝ) : ℂ) + ((|μ| : ℝ) : ℂ) * Complex.I)).re
          = Isub a |μ| + 2 * (G72 (((|μ| : ℝ) : ℂ) * Complex.I)).re := by
        simp only [Isub]
        ring
      rw [hsplit]
      have hden : (256:ℝ) ≤ |μ| ^ 4 := by
        have h := pow_le_pow_left₀ (a := (4:ℝ)) (b := |μ|) (by norm_num) hμ 4
        norm_num at h
        exact h
      have hstep : 2 * (G72 (((|μ| : ℝ) : ℂ) * Complex.I)).re ≤ 20 / |μ| ^ 4 := by
        have h2 := mul_le_mul_of_nonneg_left hC (by norm_num : (0:ℝ) ≤ 2)
        rw [show 2 * (10 / |μ| ^ 4) = 20 / |μ| ^ 4 by ring] at h2
        exact h2
      have h20 : 20 / |μ| ^ 4 ≤ 20 / 256 := by
        have hpos : (0:ℝ) < |μ| ^ 4 := by positivity
        rw [div_le_iff₀ hpos]
        rw [show (20:ℝ)/256 = 5/64 by norm_num]
        nlinarith [hden]
      have hfin : (1:ℝ)/100 + 20/256 ≤ 1/10 := by norm_num
      linarith
    · have h5' : (5:ℝ) < |μ| := lt_of_not_ge h5
      exact Work.OffAxis.Tf72One.R_le_crude a |μ| ha0 ha (le_of_lt h5')

end Work.OffAxis
