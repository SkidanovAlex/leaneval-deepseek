import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt

open Set

/-- **A `Jet` is continuous on the box `Iz ×ˢ Iθ` at every strip time.**

The joint `α`-Hölder clause of `Work.FTS.Regularity.Jet` controls
`|h z θ τ - h z' θ' τ'|` by `N · (|z-z'| + |θ-θ'| + |τ-τ'|)^α`.  At fixed `τ` this is the
`α`-Hölder (hence, since `α > 0`, continuous) estimate for the slice `(z,θ) ↦ h z θ τ` on the
box `Iz ×ˢ Iθ = [0,∞) × [0,π/2]`: the product metric `dist a b = max |Δz| |Δθ|` dominates half
the `ℓ¹`-distance used by the Hölder clause, and `x ↦ x^α` is increasing on `[0,∞)` for `α > 0`.

Only the shape `0 ≤ N ∧ _ ∧ (Hölder clause)` of `Jet` is used, so this applies to each of the
three jets `g`, `∂_zg`, `∂_τg` bundled in the regularity packages. -/
theorem continuousOn_box_of_jet {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α S N h) (hα : 0 < α) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2 τ) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  obtain ⟨hN0, _, hNh⟩ := H
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hN1 : 0 < N + 1 := by linarith
  have hden : 0 < 2 * (N + 1) := by linarith
  have hq : 0 < ε / (2 * (N + 1)) := div_pos hε hden
  refine ⟨(ε / (2 * (N + 1))) ^ (α⁻¹) / 2, ?_, ?_⟩
  · exact div_pos (Real.rpow_pos_of_pos hq α⁻¹) (by norm_num)
  · intro a ha hab
    have haz : 0 ≤ a.1 := ha.1
    have hbz : 0 ≤ b.1 := hb.1
    have hdx : |a.1 - b.1| ≤ dist a b := by
      have h := le_max_left (dist a.1 b.1) (dist a.2 b.2)
      simp only [Prod.dist_eq, Real.dist_eq] at h ⊢
      exact h
    have hdy : |a.2 - b.2| ≤ dist a b := by
      have h := le_max_right (dist a.1 b.1) (dist a.2 b.2)
      simp only [Prod.dist_eq, Real.dist_eq] at h ⊢
      exact h
    have hsum0 : 0 ≤ |a.1 - b.1| + |a.2 - b.2| := by positivity
    have hsum : |a.1 - b.1| + |a.2 - b.2| ≤ 2 * dist a b := by linarith
    have hΔ : |h a.1 a.2 τ - h b.1 b.2 τ| ≤ N * (|a.1 - b.1| + |a.2 - b.2|) ^ α := by
      have hh := hNh a.1 b.1 a.2 b.2 τ τ haz hbz ha.2 hb.2 hτ hτ
      simpa using hh
    have hle : |a.1 - b.1| + |a.2 - b.2| < (ε / (2 * (N + 1))) ^ (α⁻¹) := by
      have h2 : 2 * ((ε / (2 * (N + 1))) ^ (α⁻¹) / 2) = (ε / (2 * (N + 1))) ^ (α⁻¹) := by ring
      linarith
    have hlt : (|a.1 - b.1| + |a.2 - b.2|) ^ α < ε / (2 * (N + 1)) := by
      calc (|a.1 - b.1| + |a.2 - b.2|) ^ α
          < ((ε / (2 * (N + 1))) ^ (α⁻¹)) ^ α := Real.rpow_lt_rpow hsum0 hle hα
        _ = ε / (2 * (N + 1)) := Real.rpow_inv_rpow hq.le hα.ne'
    rw [Real.dist_eq]
    calc |h a.1 a.2 τ - h b.1 b.2 τ|
        ≤ N * (|a.1 - b.1| + |a.2 - b.2|) ^ α := hΔ
      _ ≤ (N + 1) * (|a.1 - b.1| + |a.2 - b.2|) ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hsum0 α)
      _ < (N + 1) * (ε / (2 * (N + 1))) := mul_lt_mul_of_pos_left hlt hN1
      _ = ε / 2 := by field_simp
      _ < ε := by linarith

/-- **The box-continuity clause `PsiWt` of the `FireFix` assembly**: the profile `g` of a
corrected regularity package `RegPkg'` is continuous on `Iz ×ˢ Iθ` at every strip time.

Immediate from the joint `α`-Hölder field `RegPkg'.hg` of the package and
`continuousOn_box_of_jet`. -/
theorem continuousOn_box_of_regPkg {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 τ)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  obtain ⟨N, hN⟩ := h.hg
  exact continuousOn_box_of_jet hN h.hα hτ

end Work.FTS.FireFix.Clauses.PsiWt
