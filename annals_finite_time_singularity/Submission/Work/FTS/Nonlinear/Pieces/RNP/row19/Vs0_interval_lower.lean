/-
# Row 19 — `V₀ = V(Φ̃_*)(0,·)` does not vanish at an interior angle without staying bounded
away from `0` on a whole interval

The coefficient of row 19 is `V(Φ̃_*)(z,θ) = ∂_θΦ̃_* - tan θ · Φ̃_*`, and the frozen part of the
estimate sees it only through its `z = 0` slice `V₀(θ) = V(Φ̃_*)(0,θ)`
(`Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0`).  This file records that `V₀` is *locally bounded
away from zero at every point where it is non-zero*: the defining expression is `C^∞` on the
half strip `(-1,∞) × (0,π/2)` (`Vs_smoothQuad`, proved in `Vs_lipschitz.lean`), so its `z = 0`
slice is continuous on `(0,π/2)`, and continuity plus `V₀(θ₀) ≠ 0` gives a whole interval
`(a,b) ∋ θ₀` with `|V₀(θ)| ≥ c₀ > 0`.

This is the standard "a continuous non-vanishing function is bounded away from zero locally"
step; it is what allows the row-19 piece `N₃^{**} = -2α·V(Φ̃_*)·D_zF_*` to be treated as
`sgn(V₀)·(nondegenerate)` on the support of the angular factor.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

/-- **`V₀ = V(Φ̃_*)(0,·)` is locally bounded away from `0` off its zero set.**  If `V₀` is
non-zero at an interior angle `θ₀ ∈ (0,π/2)`, then there is an interval `(a,b)` with
`0 < a < θ₀ < b < π/2` on which `|V₀| ≥ c₀` for some `c₀ > 0`.

Proof: `V = V(Φ̃_*)` is `C^∞` on the half strip `(-1,∞) × (0,π/2)` (`Vs_smoothQuad`), hence
`V₀` is continuous on `(0,π/2)` (currying the `z = 0` slice, `SmoothQuad.curry_θ`).  At the
point `θ₀` continuity with `ε := |V₀(θ₀)|/2 > 0` yields `δ > 0`; shrinking `δ` to
`r := min (δ/4) (min (θ₀/2) ((π/2-θ₀)/2))` keeps the interval `(θ₀-r, θ₀+r)` inside `(0,π/2)`,
and on it `|V₀(θ)| ≥ |V₀(θ₀)| - |V₀(θ) - V₀(θ₀)| ≥ |V₀(θ₀)|/2`. -/
theorem Vs0_interval_lower {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2))
    (hne : Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0 α Φs θ₀ ≠ 0) :
    ∃ a b c₀ : ℝ, 0 < a ∧ a < θ₀ ∧ θ₀ < b ∧ b < Real.pi / 2 ∧ 0 < c₀ ∧
      ∀ θ ∈ Set.Ioo a b, c₀ ≤ |Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0 α Φs θ| := by
  -- `V₀` is the `z = 0` slice of the `C^∞` function `V(Φ̃_*)` on the half strip
  have hV := Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Vs α Φs 0 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hV.curry_θ (show (-1 : ℝ) < 0 by norm_num)
  have hcontOn : ContinuousOn (Vs0 α Φs) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hcd.continuousOn
  have hca : ContinuousAt (Vs0 α Φs) θ₀ := hcontOn.continuousAt (isOpen_Ioo.mem_nhds hθ₀)
  have hc : 0 < |Vs0 α Φs θ₀| := abs_pos.mpr hne
  -- the `ε`-`δ` statement of continuity at `θ₀`, with `ε = |V₀(θ₀)|/2`
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousAt_iff.mp hca) (|Vs0 α Φs θ₀| / 2) (by linarith)
  obtain ⟨hθ0, hθ1⟩ := hθ₀
  -- shrink `δ` so that `(θ₀ - r, θ₀ + r) ⊆ (0, π/2) ∩ (θ₀ - δ, θ₀ + δ)`
  set r : ℝ := min (δ / 4) (min (θ₀ / 2) ((Real.pi / 2 - θ₀) / 2)) with hr
  have hr4 : 0 < δ / 4 := by linarith
  have h1 : 0 < θ₀ / 2 := by linarith
  have h2 : 0 < (Real.pi / 2 - θ₀) / 2 := by linarith
  have hrpos : 0 < r := by rw [hr]; exact lt_min hr4 (lt_min h1 h2)
  have hr_le1 : r ≤ δ / 4 := by rw [hr]; exact min_le_left _ _
  have hr_le2 : r ≤ θ₀ / 2 := by
    rw [hr]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le3 : r ≤ (Real.pi / 2 - θ₀) / 2 := by
    rw [hr]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨θ₀ - r, θ₀ + r, |Vs0 α Φs θ₀| / 2,
    by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
  intro θ hθ
  have hdist : dist θ θ₀ < δ := by
    rw [Real.dist_eq]
    have habs : |θ - θ₀| < r := abs_lt.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    linarith
  have hb := hδ hdist
  rw [Real.dist_eq, abs_sub_comm] at hb
  have htri : |Vs0 α Φs θ₀| ≤ |Vs0 α Φs θ₀ - Vs0 α Φs θ| + |Vs0 α Φs θ| := by
    have h := abs_add_le (Vs0 α Φs θ₀ - Vs0 α Φs θ) (Vs0 α Φs θ)
    rwa [sub_add_cancel] at h
  linarith

end Work.FTS.Nonlinear.Pieces.RNP.row19
