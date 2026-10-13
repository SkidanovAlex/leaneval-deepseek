import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS_RegExport.RXT (cz cth om)

/-- Helper: on the logarithmic coordinates `z = e^s`, `θ = arctan(e^ψ)` the hypotheses `hVb`,
`hRb`, `h0` transfer verbatim to the pulled-back coefficients, because `cz s > 0`,
`cth ψ ∈ (0, π/2)` and `om α s ψ > 0`. -/
theorem pw_bounds {n : ℕ} {w R : Fin n → ℝ → ℝ → ℝ → ℝ} {Vz b : ℝ → ℝ → ℝ → ℝ}
    {S M C K₀ Kσ α : ℝ} (hα : 0 < α) (hS : 0 < S)
    (hVb : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |Vz z θ τ| ≤ M ∧ |b z θ τ| ≤ M)
    (hRb : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |R k z θ τ| ≤ C * ∑ j, |w j z θ τ| + Kσ * Work.FTS.RegExportIface.ω α z θ)
    (h0 : ∀ k z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |w k z θ 0| ≤ K₀ * Work.FTS.RegExportIface.ω α z θ) :
    (∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) S → |coefA Vz s ψ τ| ≤ 2 * |M|) ∧
    (∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) S → |coefB b s ψ τ| ≤ 2 * |M|) ∧
    (∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) S → |coefC α Vz b s ψ τ| ≤ (2 + 4 * α) * |M|) ∧
    (∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) S →
      |srcF α (R k) s ψ τ| ≤ max C 0 * ∑ j, |pw α (w j) s ψ τ| + max Kσ 0) ∧
    (∀ k s ψ, |pw α (w k) s ψ 0| ≤ max K₀ 0) := by
  have h2pos : (0:ℝ) < 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `coefA Vz = Vz`
    intro s ψ τ hτ
    obtain ⟨hV, _⟩ := hVb (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
    simp only [coefA]
    linarith [abs_nonneg M, le_abs_self M]
  · -- `coefB b = 2b`
    intro s ψ τ hτ
    obtain ⟨_, hb⟩ := hVb (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
    simp only [coefB, abs_mul, abs_of_pos h2pos]
    linarith [abs_nonneg M, le_abs_self M]
  · -- `coefC α Vz b = 2Vz/(1+z) + 2α·c2m(θ)·b`
    intro s ψ τ hτ
    obtain ⟨hV, hb⟩ := hVb (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
    have hcz : 0 < cz s := cz_pos s
    have hden : 0 < 1 + cz s := by linarith
    have hc2 : |Work.Construction.c2m (cth ψ)| ≤ 2 := c2m_abs_le_two _
    have hc2nn : 0 ≤ |Work.Construction.c2m (cth ψ)| := abs_nonneg _
    have hbnn : 0 ≤ |b (cz s) (cth ψ) τ| := abs_nonneg _
    have hbM : |b (cz s) (cth ψ) τ| ≤ |M| := le_trans hb (le_abs_self M)
    -- the first summand
    have hA1 : |2 * Vz (cz s) (cth ψ) τ / (1 + cz s)| ≤ 2 * |M| := by
      simp only [abs_div, abs_mul, abs_of_pos h2pos, abs_of_pos hden]
      have hstep : 2 * |Vz (cz s) (cth ψ) τ| / (1 + cz s) ≤ 2 * |Vz (cz s) (cth ψ) τ| := by
        rw [div_le_iff₀ hden]
        nlinarith [abs_nonneg (Vz (cz s) (cth ψ) τ)]
      have hVM : |Vz (cz s) (cth ψ) τ| ≤ |M| := le_trans hV (le_abs_self M)
      linarith
    -- the second summand
    have hA2 : |α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)|
        ≤ 4 * α * |M| := by
      simp only [abs_mul, abs_of_pos hα, abs_of_pos h2pos]
      have hprod : |Work.Construction.c2m (cth ψ)| * |b (cz s) (cth ψ) τ| ≤ 2 * |M| :=
        mul_le_mul hc2 hbM hbnn (by norm_num)
      have hfac : 0 ≤ 2 * α := by linarith
      have := mul_le_mul_of_nonneg_left hprod hfac
      nlinarith [this]
    simp only [coefC]
    calc |2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
            + α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)|
        ≤ |2 * Vz (cz s) (cth ψ) τ / (1 + cz s)|
            + |α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)| := abs_add_le _ _
      _ ≤ 2 * |M| + 4 * α * |M| := by linarith
      _ = (2 + 4 * α) * |M| := by ring
  · -- the source `srcF α (R k) = R k / om`
    intro k s ψ τ hτ
    obtain hR := hRb k (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
    have hom : 0 < om α s ψ := om_pos (α := α) hα
    have hXnn : 0 ≤ ∑ j, |pw α (w j) s ψ τ| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hsum : ∑ j, |w j (cz s) (cth ψ) τ|
        = om α s ψ * (∑ j, |pw α (w j) s ψ τ|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [pw, abs_div, abs_of_pos hom, mul_div_cancel₀ _ hom.ne']
    have key : |srcF α (R k) s ψ τ| ≤ C * (∑ j, |pw α (w j) s ψ τ|) + Kσ := by
      simp only [srcF, abs_div, abs_of_pos hom]
      rw [div_le_iff₀ hom]
      have heq : C * (∑ j, |w j (cz s) (cth ψ) τ|)
            + Kσ * Work.FTS.RegExportIface.ω α (cz s) (cth ψ)
          = (C * (∑ j, |pw α (w j) s ψ τ|) + Kσ) * om α s ψ := by
        rw [hsum]
        simp only [om]
        ring
      rw [← heq]
      exact hR
    calc |srcF α (R k) s ψ τ| ≤ C * (∑ j, |pw α (w j) s ψ τ|) + Kσ := key
      _ ≤ max C 0 * (∑ j, |pw α (w j) s ψ τ|) + max Kσ 0 := by
            have hC : C * (∑ j, |pw α (w j) s ψ τ|)
                ≤ max C 0 * (∑ j, |pw α (w j) s ψ τ|) :=
              mul_le_mul_of_nonneg_right (le_max_left C 0) hXnn
            linarith [le_max_left Kσ 0]
  · -- the initial datum
    intro k s ψ
    have h := h0 k (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)
    have hom : 0 < om α s ψ := om_pos (α := α) hα
    have homnn : 0 ≤ om α s ψ := le_of_lt hom
    simp only [pw, abs_div, abs_of_pos hom]
    rw [div_le_iff₀ hom]
    calc |w k (cz s) (cth ψ) 0| ≤ K₀ * om α s ψ := by simpa only [om] using h
      _ ≤ max K₀ 0 * om α s ψ :=
            mul_le_mul_of_nonneg_right (le_max_left K₀ 0) homnn

end Work.FTS_RegExport.RXT.Sys
