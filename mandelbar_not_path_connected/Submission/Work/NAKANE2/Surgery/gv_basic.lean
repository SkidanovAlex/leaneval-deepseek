import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Basic properties of the Shishikura deformation `g_v = σ_v ∘ T_{c₀}`

For a surgery datum `D : Work.NAKANE2.SurgeryData c₀` and a vector `v : ℂ`, the deformed map

`g_v z = σ_v (T_{c₀} z) = T_{c₀} z + χ (T_{c₀} z) · v`

has the four elementary properties collected in `gv_basic`:

* it is `C¹` over `ℝ` (both `T_{c₀}` and the bump `χ` are smooth);
* `g_v 0 = c₀ + v`, because `T_{c₀} 0 = c₀` and `χ c₀ = 1`;
* it is **even**, `g_v (-z) = g_v z`, because `T_{c₀}` is even and `χ` only sees `T_{c₀} z`;
* outside the set `V = T_{c₀}⁻¹ (ball c₀ (2ρ))` it coincides with the undeformed map `T_{c₀}`,
  because there the bump vanishes: `χ` is supported in `ball c₀ rOut = ball c₀ ρ ⊆ ball c₀ (2ρ)`.
-/

namespace Work.NAKANE2.Surgery

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Smoothness of the two factors -/

/-- The `ℂ`-valued bump `chiC c₀ χ` is `C¹` over `ℝ`. -/
theorem gv_chiC_contDiff {c₀ : ℂ} (χ : ContDiffBump c₀) :
    ContDiff ℝ 1 (Work.NAKANE2.chiC c₀ χ) :=
  (((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff (n := (1 : ℕ∞))).comp
    (ContDiffBump.contDiff (n := (1 : ℕ∞)) χ))

/-- The antiholomorphic quadratic `T_{c₀}(z) = z̄² + c₀` is `C¹` over `ℝ`. -/
theorem gv_Tantibar_contDiff (c₀ : ℂ) :
    ContDiff ℝ 1 (fun z : ℂ => Tantibar c₀ z) := by
  rw [show (fun z : ℂ => Tantibar c₀ z) = fun z : ℂ => star z ^ 2 + c₀ from rfl]
  exact ((ContinuousLinearEquiv.contDiff Complex.conjCLE :
    ContDiff ℝ 1 (star : ℂ → ℂ)).pow 2).add contDiff_const

/-- `T_c` is an even function: `T_c (-z) = T_c z`. -/
theorem gv_Tantibar_neg (c z : ℂ) : Tantibar c (-z) = Tantibar c z := by
  simp only [Tantibar, map_neg, neg_sq]

/-! ## The four basic properties -/

theorem gv_basic {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) (v : ℂ) :
    ContDiff ℝ 1 (Work.NAKANE2.gv c₀ D.χ v) ∧ Work.NAKANE2.gv c₀ D.χ v 0 = c₀ + v ∧
      (∀ z : ℂ, Work.NAKANE2.gv c₀ D.χ v (-z) = Work.NAKANE2.gv c₀ D.χ v z) ∧
      (∀ z : ℂ, z ∉ Work.NAKANE2.V c₀ D.ρ →
        Work.NAKANE2.gv c₀ D.χ v z = LeanEval.ComplexAnalysis.Tantibar c₀ z) := by
  have hχcd : ContDiff ℝ 1 (Work.NAKANE2.chiC c₀ D.χ) := gv_chiC_contDiff D.χ
  have hT : ContDiff ℝ 1 (fun z : ℂ => Tantibar c₀ z) := gv_Tantibar_contDiff c₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `g_v = T_{c₀} + (χ ∘ T_{c₀}) · v` is a sum of smooth terms
    exact hT.add ((hχcd.comp hT).mul contDiff_const)
  · -- at the origin: `T_{c₀} 0 = c₀` and `χ c₀ = 1`
    have hone : Work.NAKANE2.chiC c₀ D.χ c₀ = 1 := by
      have h := ContDiffBump.one_of_mem_closedBall D.χ (x := c₀)
        (by rw [Metric.mem_closedBall, dist_self]; exact le_of_lt D.χ.rIn_pos)
      change ((D.χ c₀ : ℝ) : ℂ) = 1
      rw [h, Complex.ofReal_one]
    rw [Work.NAKANE2.gv_apply, Work.Bottcher.Tantibar_zero, hone, one_mul]
  · -- evenness, inherited from `T_{c₀}`
    intro z
    rw [Work.NAKANE2.gv_apply, Work.NAKANE2.gv_apply]
    simp only [gv_Tantibar_neg]
  · -- outside `V` the bump vanishes, so `g_v` is the undeformed map
    intro z hz
    have hnot : Tantibar c₀ z ∉ Metric.ball c₀ (2 * D.ρ) := fun hmem =>
      hz (Work.NAKANE2.mem_V.mpr hmem)
    have hle : D.χ.rOut ≤ dist (Tantibar c₀ z) c₀ := by
      rw [Metric.mem_ball, not_lt] at hnot
      rw [D.hrOut]; linarith [D.hρ]
    have hzero : Work.NAKANE2.chiC c₀ D.χ (Tantibar c₀ z) = 0 := by
      have h := ContDiffBump.zero_of_le_dist D.χ hle
      change ((D.χ (Tantibar c₀ z) : ℝ) : ℂ) = 0
      rw [h, Complex.ofReal_zero]
    rw [Work.NAKANE2.gv_apply, hzero, zero_mul, add_zero]

end Work.NAKANE2.Surgery
