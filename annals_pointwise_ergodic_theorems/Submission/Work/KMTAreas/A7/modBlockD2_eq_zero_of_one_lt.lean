import Mathlib
import Submission.Work.KMTAreas.A7.lacModDiffDefs

namespace Work.KMTAreas.A7

/-- The second derivative of a modulated block vanishes as soon as `Φ`, `deriv Φ` and
`iteratedDeriv 2 Φ` all vanish outside `[-1,1]` and `s |ξ| > 1`, `s ≥ 0`: the argument `s ξ`
then lies where the three factors are zero. -/
theorem modBlockD2_eq_zero_of_one_lt {Φ : ℝ → ℂ}
    (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0)
    (hΦdsupp : ∀ u : ℝ, 1 ≤ |u| → deriv Φ u = 0)
    (hΦd2supp : ∀ u : ℝ, 1 ≤ |u| → iteratedDeriv 2 Φ u = 0)
    {s l ξ : ℝ} (hs : 0 ≤ s) (h : 1 < s * |ξ|) :
    modBlockD2 Φ s l ξ = 0 := by
  have h1 : 1 ≤ |s * ξ| := by
    rw [abs_mul, abs_of_nonneg hs]
    exact le_of_lt h
  rw [modBlockD2, hΦsupp (s * ξ) h1, hΦdsupp (s * ξ) h1, hΦd2supp (s * ξ) h1]
  ring

end Work.KMTAreas.A7
