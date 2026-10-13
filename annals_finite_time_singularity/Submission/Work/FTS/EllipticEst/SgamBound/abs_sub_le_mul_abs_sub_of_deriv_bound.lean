import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.SgamBound

/-- Lagrange mean-value bound on a sub-interval of `(0, π/2)`: if `u` is smooth on the open
strip `(0, π/2)` and `|u'| ≤ K` there, then for `0 < a ≤ b < π/2`
`|u b - u a| ≤ K * (b - a)`.

Proof: `exists_deriv_eq_slope` supplies `c ∈ (a, b)` with
`deriv u c = (u b - u a) / (b - a)`; multiply by `b - a > 0` and use `|deriv u c| ≤ K`
(the point `c` lies in `(0, π/2)`, since `Icc a b ⊆ Ioo 0 (π/2)`). -/
private lemma abs_sub_le_mul_of_deriv_bound_aux {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    {K a b : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2))
    (hb : b ∈ Set.Ioo 0 (Real.pi / 2)) (hab : a ≤ b)
    (hK : ∀ ξ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u ξ| ≤ K) :
    |u b - u a| ≤ K * (b - a) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- Nontrivial interval: Lagrange's mean value theorem.
    have hsub : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := Set.Icc_subset_Ioo ha.1 hb.2
    have hcont : ContinuousOn u (Set.Icc a b) := (hsm 1).continuousOn.mono hsub
    have hdiff : DifferentiableOn ℝ u (Set.Ioo a b) :=
      ((hsm 1).differentiableOn (by norm_num)).mono
        (Set.Ioo_subset_Ioo ha.1.le hb.2.le)
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hlt hcont hdiff
    have hcI : c ∈ Set.Ioo 0 (Real.pi / 2) := hsub ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    have hKc : |deriv u c| ≤ K := hK c hcI
    have hpos : 0 < b - a := sub_pos.mpr hlt
    have h2 : u b - u a = (b - a) * deriv u c := by
      rw [hcd]; field_simp
    rw [h2, abs_mul, abs_of_pos hpos, mul_comm K]
    exact mul_le_mul_of_nonneg_left hKc (le_of_lt hpos)
  · -- Degenerate interval: the two points coincide.
    subst heq
    simp

theorem abs_sub_le_mul_abs_sub_of_deriv_bound {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    {K θ θ₀ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2))
    (hK : ∀ ξ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u ξ| ≤ K) :
    |u θ - u θ₀| ≤ K * |θ - θ₀| := by
  rcases le_total θ₀ θ with hle | hle
  · -- `θ₀ ≤ θ`: apply the mean-value bound on `[θ₀, θ]`.
    have h := abs_sub_le_mul_of_deriv_bound_aux hsm hθ₀ hθ hle hK
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact h
  · -- `θ ≤ θ₀`: apply it on `[θ, θ₀]` and use symmetry of the absolute value.
    have h := abs_sub_le_mul_of_deriv_bound_aux hsm hθ hθ₀ hle hK
    rw [abs_sub_comm (u θ) (u θ₀), abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact h

end Work.FTS.EllipticEst.SgamBound
