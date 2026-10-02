import Mathlib
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Flower.PsiData
import Submission.Work.FatouCoord.Flower.LambdaBounds
import Submission.Work.FatouCoord.Petal.repelling_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The covering property of the repelling coordinate `Ψ`

`Psi_cover` is the last geometric field of `ParabolicFlower`: every sufficiently small `z ≠ 0`
lies either in the wide petal `WidePetal Ms`, or is hit by `Ψ` on an arbitrarily far left
half plane `{Re w < -Rpar}`.

The proof is a direct application of the (inverse) estimate `hVinv` for the chart conjugacy
`V`: if `z ∉ WidePetal Ms` is small, then `Y = -1/z` has `Re Y → -∞` and `‖Y‖ → ∞`, so
`hVinv` produces `x` with `x.re < -R`, `V x = Y`, and `‖x - (Y - (1-a) Λ Y)‖ ≤ 4`.  Since
`Re Y ≤ (Ms - 1/‖z‖)/2` is as negative as we like, the point `w = x - c` satisfies
`Ψ w = -1 / rV f V R (w + c) = -1 / V x = z` and `Re w < -Rpar`.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Flower

open Work.FatouCoord

noncomputable section

/-- If `z ≠ 0` is outside the wide petal `WidePetal M` and `M ‖z‖ < 1`, then
`Re (-1/z) ≤ (M - 1/‖z‖)/2`: for small `z` the chart value `-1/z` is far to the left.

Indeed `M < sgauge (-1/z)` fails, i.e. `(-1/z).re + |(-1/z).im| ≤ M`; writing
`u = (-1/z).re`, `|(-1/z).im| ≤ M - u`, the triangle inequality gives
`1/‖z‖ = ‖-1/z‖ ≤ |u| + (M - u)`.  If `u ≤ 0` this is `≤ M - 2u` and we are done; if `u > 0`
it is `≤ M`, forcing `M ‖z‖ ≥ 1`. -/
lemma re_neg_one_div_le_of_not_mem_WidePetal {M : ℝ} {z : ℂ} (hz : z ≠ 0)
    (h : z ∉ WidePetal M) (hMz : M * ‖z‖ < 1) :
    (-1 / z).re ≤ (M - 1 / ‖z‖) / 2 := by
  have hsg : sgauge (-1 / z) ≤ M := le_of_not_gt fun hlt => h ⟨hz, hlt⟩
  rw [sgauge] at hsg
  have hnorm : ‖(-1 : ℂ) / z‖ = 1 / ‖z‖ := by rw [norm_div, norm_neg, norm_one]
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases hcase : (-1 / z).re ≤ 0
  · have h1 : ‖(-1 / z)‖ ≤ -((-1 / z).re) + |(-1 / z).im| := by
      have h2 := Complex.norm_le_abs_re_add_abs_im (-1 / z)
      rw [abs_of_nonpos hcase] at h2
      linarith
    rw [hnorm] at h1
    linarith
  · push_neg at hcase
    have h1 : ‖(-1 / z)‖ ≤ (-1 / z).re + |(-1 / z).im| := by
      have h2 := Complex.norm_le_abs_re_add_abs_im (-1 / z)
      rw [abs_of_pos hcase] at h2
      linarith
    rw [hnorm] at h1
    have h4 : 1 / ‖z‖ ≤ M := by linarith
    rw [div_le_iff₀ hzp] at h4
    linarith

theorem Psi_cover {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    {R : ℝ} (V : ℂ → ℂ)
    (hVshift : ∀ w : ℂ, w.re < -R → V (w+1) = Work.FatouCoord.wMap f (V w))
    (hVinv : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ Y : ℂ, R₁ ≤ ‖Y‖ →
      (Y - (1 - a) * Work.FatouCoord.Petal.Lambda Y).re < -R₁ →
        ∃ x : ℂ, x.re < -R ∧ V x = Y ∧
          ‖x - (Y - (1 - a) * Work.FatouCoord.Petal.Lambda Y)‖ ≤ 4)
    {Ms : ℝ} (hMs : 1 ≤ Ms) (hMsr : 1 / r < Ms)
    {c : ℂ} (hc : star c = -c)
    {Ψ : ℂ → ℂ} (hΨc : ∀ w : ℂ, Ψ w = -1 / Work.FatouCoord.Flower.rV f V R (w + c)) :
    ∀ Rpar : ℝ, ∃ rr : ℝ, 0 < rr ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < rr →
      z ∈ Work.FatouCoord.Flower.WidePetal Ms ∨ ∃ w : ℂ, w.re < -Rpar ∧ Ψ w = z := by
  obtain ⟨R₁, hR₁pos, hR₁⟩ := hVinv
  intro Rpar
  -- the tail bound `‖1 - a‖ (log t + 2π) ≤ t/4` for the logarithmic error of `Λ`
  obtain ⟨T, hT⟩ := LambdaBounds.exists_lambda_growth (M := ‖(1 - a : ℂ)‖) (norm_nonneg _)
  -- the target depth
  set τ : ℝ := max R₁ (Rpar + 4) + 1 with hτ
  have hτR₁ : R₁ < τ := by rw [hτ]; linarith [le_max_left R₁ (Rpar + 4)]
  have hτRpar : Rpar + 4 < τ := by rw [hτ]; linarith [le_max_right R₁ (Rpar + 4)]
  -- the threshold for `‖-1/z‖`
  set s₀ : ℝ := max T (max R₁ (max (Ms + 1) (2 * Ms + 4 * τ + 1))) with hs₀
  have hs₀T : T ≤ s₀ := by rw [hs₀]; exact le_max_left _ _
  have hs₀R₁ : R₁ ≤ s₀ := by
    rw [hs₀]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hs₀M : Ms + 1 ≤ s₀ := by
    rw [hs₀]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hs₀big : 2 * Ms + 4 * τ + 1 ≤ s₀ := by
    rw [hs₀]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le (by linarith) hs₀M
  refine ⟨1 / s₀, by positivity, ?_⟩
  intro z hz0 hzlt
  by_cases hW : z ∈ WidePetal Ms
  · exact Or.inl hW
  right
  have hz : z ≠ 0 := norm_pos_iff.mp hz0
  have hzn : ‖(-1 : ℂ) / z‖ = 1 / ‖z‖ := by rw [norm_div, norm_neg, norm_one]
  -- `‖-1/z‖` exceeds the threshold
  have hs : s₀ < ‖(-1 : ℂ) / z‖ := by
    have h : 1 / (1 / s₀) < 1 / ‖z‖ := one_div_lt_one_div_of_lt (by positivity) hzlt
    rw [one_div_one_div] at h
    rw [hzn]; exact h
  have hz1 : ‖z‖ < 1 := by
    have h2 : 1 / s₀ ≤ 1 := by
      rw [div_le_one hs₀pos]; linarith
    linarith
  -- `Ms * ‖z‖ < 1`, so the geometric bound applies
  have hMz : Ms * ‖z‖ < 1 := by
    have h1 : Ms * ‖z‖ < Ms * (1 / s₀) := mul_lt_mul_of_pos_left hzlt (by linarith)
    have h2 : Ms * (1 / s₀) ≤ Ms / (Ms + 1) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) hs₀M
    have h3 : Ms / (Ms + 1) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  have hX : (-1 / z).re ≤ (Ms - 1 / ‖z‖) / 2 :=
    re_neg_one_div_le_of_not_mem_WidePetal hz hW hMz
  have hY1 : 1 ≤ ‖(-1 : ℂ) / z‖ := by
    rw [hzn, le_div_iff₀ hz0]
    linarith
  have hYre : (-1 / z).re ≤ (Ms - ‖(-1 : ℂ) / z‖) / 2 := by
    rw [hzn]; exact hX
  -- the logarithmic bound for `Λ`
  have hΛ : ‖Petal.Lambda (-1 / z)‖
      ≤ Real.log ‖(-1 : ℂ) / z‖ + 2 * Real.pi :=
    LambdaBounds.norm_Lambda_le_log hY1
  have hlog : ‖(1 - a : ℂ)‖ * (Real.log ‖(-1 : ℂ) / z‖ + 2 * Real.pi)
      ≤ ‖(-1 : ℂ) / z‖ / 4 :=
    hT _ (le_of_lt (lt_of_le_of_lt hs₀T hs))
  -- hence `Y - (1 - a) Λ Y` is far to the left
  have hkey : ((-1 / z) - (1 - a) * Petal.Lambda (-1 / z)).re
      ≤ (Ms - ‖(-1 : ℂ) / z‖) / 2 + ‖(-1 : ℂ) / z‖ / 4 := by
    have h1 : ((-1 / z) - (1 - a) * Petal.Lambda (-1 / z)).re
        ≤ (-1 / z).re + ‖(1 - a) * Petal.Lambda (-1 / z)‖ := by
      have h'' : -(((1 - a) * Petal.Lambda (-1 / z)).re)
          ≤ ‖(1 - a) * Petal.Lambda (-1 / z)‖ := by
        have h3 := Complex.abs_re_le_norm ((1 - a) * Petal.Lambda (-1 / z))
        linarith [neg_abs_le (((1 - a) * Petal.Lambda (-1 / z)).re)]
      have h : ((-1 / z) - (1 - a) * Petal.Lambda (-1 / z)).re
          = (-1 / z).re - ((1 - a) * Petal.Lambda (-1 / z)).re := by simp
      rw [h]
      linarith
    have h2 : ‖(1 - a) * Petal.Lambda (-1 / z)‖
        ≤ ‖(1 - a : ℂ)‖ * (Real.log ‖(-1 : ℂ) / z‖ + 2 * Real.pi) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hΛ (norm_nonneg _)
    linarith
  have hlarge : Ms / 2 - ‖(-1 : ℂ) / z‖ / 4 < -τ := by
    linarith [hs, hs₀big]
  have hre₁ : ((-1 / z) - (1 - a) * Petal.Lambda (-1 / z)).re < -R₁ := by linarith
  obtain ⟨x, hxre, hVx, hxdist⟩ := hR₁ (-1 / z) (le_of_lt (lt_of_le_of_lt hs₀R₁ hs)) hre₁
  have hcre : c.re = 0 := by
    have h := congrArg Complex.re hc
    simp at h
    linarith
  refine ⟨x - c, ?_, ?_⟩
  · have hre : (x - c).re = x.re := by rw [Complex.sub_re, hcre, sub_zero]
    rw [hre]
    have h1 : x.re ≤ ((-1 / z) - (1 - a) * Petal.Lambda (-1 / z)).re + 4 := by
      have h := Complex.re_le_norm (x - ((-1 / z) - (1 - a) * Petal.Lambda (-1 / z)))
      have h' : (x - ((-1 / z) - (1 - a) * Petal.Lambda (-1 / z))).re
          = x.re - ((-1 / z) - (1 - a) * Petal.Lambda (-1 / z)).re := by simp
      rw [h'] at h
      linarith
    linarith
  · rw [hΨc (x - c)]
    have hxc : x - c + c = x := by ring
    rw [hxc]
    have hrV : rV f V R x = -1 / z := by
      rw [rV_eq_of_re_lt hVshift hxre, hVx]
    rw [hrV]
    field_simp

end

end Work.FatouCoord.Flower
