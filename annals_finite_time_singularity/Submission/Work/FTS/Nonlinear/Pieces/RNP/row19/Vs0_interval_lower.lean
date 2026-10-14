import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.Spaces.bt_integral_weight_id
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **radial profile** `2z(1−z)/(1+z)³` of `D_zF_*/(αΓ/c)`. -/
abbrev prof (z : ℝ) : ℝ := 2 * z * (1 - z) / (1 + z) ^ 3

/-- The radial profile as a function of the two self-similar variables (constant in `θ`). -/
abbrev proff : ℝ → ℝ → ℝ := fun z _ => 2 * z * (1 - z) / (1 + z) ^ 3

/-- The **angular factor** `V(Φ̃_*)(0,θ)·αΓ(α,θ)/c α` of the row-19 coefficient. -/
abbrev Ufun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ :=
  fun θ => Vs0 α Φs θ * (α * Work.Spaces.Gam α θ / Work.Spaces.c α)

/-- `D_zF_*(z,θ) = (αΓ(θ)/c)·prof(z)` for `z > -1`. -/
theorem Gs_eq_prof {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : -1 < z) :
    Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ
      = (α * Work.Spaces.Gam α θ / Work.Spaces.c α) * prof z := by
  rw [Work.FTS.Nonlinear.Pieces.RNP.Gs, Work.Construction.Dz_Fstar_eq hα hz, prof]
  ring


end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0_interval_lower =====
section

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
end
