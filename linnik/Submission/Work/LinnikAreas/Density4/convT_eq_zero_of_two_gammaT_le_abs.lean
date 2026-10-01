/-
# Area 4 / HB §12 — superadditivity of the support of the §7 test function

`gT θ lam` is supported in the *closed* interval `[-γ,γ]` (`γ = gammaT θ lam`), and it
vanishes at both endpoints `±γ` (there `ζ·(±γ) = ±θ`, so `cos(ζt) = cos θ`).  Hence its
support is contained in the *open* interval `(-γ,γ)`: `gT θ lam t = 0` whenever
`γ ≤ |t|`.

Consequently, for `|v| ≥ 2γ` the convolution integrand
`s ↦ gT θ lam s * gT θ lam (v - s)` vanishes *pointwise*: on the support of the first
factor (`|s| ≤ γ`) the reverse triangle inequality gives
`|v - s| ≥ |v| - |s| ≥ 2γ - γ = γ`, so the second factor vanishes.  The integral of a
pointwise-zero function is zero.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- `gT θ lam` vanishes at and beyond `|t| = gammaT θ lam`: the support of the §7 test
function is contained in the open interval `(-γ,γ)`.  At the endpoints `t = ±γ` one has
`zetaT θ lam * t = ±θ`, hence `cos (zetaT θ lam * t) = cos θ`. -/
lemma gT_eq_zero_of_gammaT_le_abs {θ lam t : ℝ} (hζ : zetaT θ lam ≠ 0)
    (hγ : 0 ≤ gammaT θ lam) (h : gammaT θ lam ≤ |t|) : gT θ lam t = 0 := by
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [gT, if_neg (not_le.mpr hlt)]
  · rw [gT, if_pos (le_of_eq heq.symm)]
    have ht : t = gammaT θ lam ∨ t = -gammaT θ lam := (abs_eq hγ).mp heq.symm
    rcases ht with ht | ht
    · rw [ht, gammaT, mul_div_cancel₀ θ hζ, sub_self, mul_zero]
    · rw [ht, mul_neg, gammaT, mul_div_cancel₀ θ hζ, Real.cos_neg, sub_self, mul_zero]

theorem convT_eq_zero_of_two_gammaT_le_abs {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    ∀ v : ℝ, 2 * gammaT θ lam ≤ |v| →
      (∫ s : ℝ, gT θ lam s * gT θ lam (v - s)) = 0 := by
  intro v hv
  have hζ : zetaT θ lam ≠ 0 := ne_of_gt (zetaT_pos hθ1 hθ2 hlam)
  have hγ : 0 ≤ gammaT θ lam := le_of_lt (gammaT_pos hθ1 hθ2 hlam)
  have hzero : ∀ s, gT θ lam s * gT θ lam (v - s) = 0 := by
    intro s
    by_cases hs : |s| ≤ gammaT θ lam
    · have hvs : gammaT θ lam ≤ |v - s| := by
        have h1 : |v| - |s| ≤ |v - s| := abs_sub_abs_le_abs_sub v s
        linarith
      rw [gT_eq_zero_of_gammaT_le_abs hζ hγ hvs]; ring
    · rw [gT, if_neg hs, zero_mul]
  rw [show (fun s : ℝ => gT θ lam s * gT θ lam (v - s)) = fun _ => (0:ℝ)
        from funext hzero]
  simp

end Work.LinnikAreas.Density4
