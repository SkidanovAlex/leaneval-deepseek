import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Bounds` — the pointwise bounds on the pulled-back coefficients

`|a| ≤ M`, `|b| ≤ 2M`, `|c| ≤ M(3+4α)`, `|f| ≤ Kσ` for `τ ∈ (0,S]`, and `|φ(·,0)| ≤ K₀` — the
numerical hypotheses of the cone maximum principle, in the pulled-back variables.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ### The pointwise bounds on the pulled-back coefficients -/

theorem trA_bound {S M : ℝ} {Vz : ℝ → ℝ → ℝ → ℝ}
    (hVz : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      0 ≤ Vz z θ τ ∧ Vz z θ τ ≤ M) :
    ∀ s ψ τ, 0 < τ → τ ≤ S → |trA Vz s ψ τ| ≤ M := by
  intro s ψ τ hτ0 hτS
  have hτ : τ ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hτ0, hτS⟩
  have h := hVz (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
  show |Vz (cz s) (cth ψ) τ| ≤ M
  rw [abs_of_nonneg h.1]
  exact h.2

theorem trB_bound {S M : ℝ} {Vθ : ℝ → ℝ → ℝ → ℝ}
    (hVθ : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |Vθ z θ τ| ≤ M * Real.sin (2 * θ)) :
    ∀ s ψ τ, 0 < τ → τ ≤ S → |trB Vθ s ψ τ| ≤ 2 * M := by
  intro s ψ τ hτ0 hτS
  have hτ : τ ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hτ0, hτS⟩
  have h := hVθ (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
  have hs2 : 0 < Real.sin (2 * cth ψ) := cth_sin_two_pos ψ
  have h' : |trB Vθ s ψ τ| = 2 * |Vθ (cz s) (cth ψ) τ| / Real.sin (2 * cth ψ) := by
    show |2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ)| = _
    rw [abs_div, abs_mul, abs_of_pos hs2, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h']
  have h2 : 2 * |Vθ (cz s) (cth ψ) τ| / Real.sin (2 * cth ψ)
      ≤ 2 * (M * Real.sin (2 * cth ψ)) / Real.sin (2 * cth ψ) := by
    gcongr
  have h3 : 2 * (M * Real.sin (2 * cth ψ)) / Real.sin (2 * cth ψ) = 2 * M := by
    field_simp
  linarith [h2, h3.le]

theorem trC_bound {S M α : ℝ} (hα : 0 < α) {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ}
    (hVz : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      0 ≤ Vz z θ τ ∧ Vz z θ τ ≤ M)
    (hVθ : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |Vθ z θ τ| ≤ M * Real.sin (2 * θ))
    (hcs : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |cs z θ τ| ≤ M) :
    ∀ s ψ τ, 0 < τ → τ ≤ S → |trC α Vz Vθ cs s ψ τ| ≤ M * (3 + 4 * α) := by
  intro s ψ τ hτ0 hτS
  have hτ : τ ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hτ0, hτS⟩
  have hz := cz_pos s
  have hθ0 := cth_pos ψ
  have hθπ := cth_lt ψ
  have hvz := hVz (cz s) (cth ψ) τ hz hθ0 hθπ hτ
  have hc := hcs (cz s) (cth ψ) τ hz hθ0 hθπ hτ
  have hM0 : 0 ≤ M := le_trans hvz.1 hvz.2
  have hα0 : 0 ≤ α := hα.le
  have hc2 : |Work.Construction.c2m (cth ψ)| ≤ 2 := c2m_abs_le_two (cth ψ)
  have hb : |2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ)| ≤ 2 * M :=
    trB_bound hVθ s ψ τ hτ0 hτS
  have hz2 : 0 ≤ 2 * Vz (cz s) (cth ψ) τ / (1 + cz s) :=
    div_nonneg (by linarith [hvz.1]) (by have := cz_pos s; linarith)
  have hz2' : 2 * Vz (cz s) (cth ψ) τ / (1 + cz s) ≤ 2 * M := by
    rw [div_le_iff₀ (by have := cz_pos s; linarith : (0:ℝ) < 1 + cz s)]
    nlinarith [hvz.1, hvz.2, cz_pos s]
  have h3 : |α * Work.Construction.c2m (cth ψ)
      * (2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ))| ≤ 4 * α * M := by
    rw [abs_mul, abs_mul, abs_of_nonneg hα0]
    calc α * |Work.Construction.c2m (cth ψ)|
        * |2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ)|
        ≤ α * 2 * (2 * M) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hc2 hα0) hb (abs_nonneg _)
            (mul_nonneg hα0 (by norm_num))
      _ = 4 * α * M := by ring
  have hsum : |cs (cz s) (cth ψ) τ + 2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
        + α * Work.Construction.c2m (cth ψ) * (2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ))|
      ≤ M + 2 * M + 4 * α * M := by
    have h1 := abs_add_le (cs (cz s) (cth ψ) τ + 2 * Vz (cz s) (cth ψ) τ / (1 + cz s))
      (α * Work.Construction.c2m (cth ψ) * (2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ)))
    have h2 := abs_add_le (cs (cz s) (cth ψ) τ) (2 * Vz (cz s) (cth ψ) τ / (1 + cz s))
    rw [abs_of_nonneg hz2] at h2
    linarith [h1, h2, hc, hz2', h3]
  show |cs (cz s) (cth ψ) τ + 2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
      + α * Work.Construction.c2m (cth ψ) * (2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ))|
      ≤ M * (3 + 4 * α)
  nlinarith [hsum]

theorem trF_bound {S Kσ α : ℝ} (hα : 0 < α) {σ : ℝ → ℝ → ℝ → ℝ}
    (hσ : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |σ z θ τ| ≤ Kσ * Work.FTS.RegExportIface.ω α z θ) :
    ∀ s ψ τ, 0 < τ → τ ≤ S → |trF α σ s ψ τ| ≤ Kσ := by
  intro s ψ τ hτ0 hτS
  have hτ : τ ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hτ0, hτS⟩
  have hω : 0 < om α s ψ := om_pos hα
  have h := hσ (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
  have h' : |σ (cz s) (cth ψ) τ| / om α s ψ ≤ Kσ * om α s ψ / om α s ψ :=
    div_le_div_of_nonneg_right h hω.le
  have h'' : Kσ * om α s ψ / om α s ψ = Kσ := by field_simp
  show |σ (cz s) (cth ψ) τ / om α s ψ| ≤ Kσ
  rw [abs_div, abs_of_pos hω]
  linarith [h', h''.le]

theorem phi_zero_bound {α K₀ : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ → ℝ}
    (h0 : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |u z θ 0| ≤ K₀ * Work.FTS.RegExportIface.ω α z θ) :
    ∀ s ψ, |phi α u s ψ 0| ≤ K₀ := by
  intro s ψ
  have hω : 0 < om α s ψ := om_pos hα
  have h := h0 (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)
  have h' : |u (cz s) (cth ψ) 0| / om α s ψ ≤ K₀ * om α s ψ / om α s ψ :=
    div_le_div_of_nonneg_right h hω.le
  have h'' : K₀ * om α s ψ / om α s ψ = K₀ := by field_simp
  show |u (cz s) (cth ψ) 0 / om α s ψ| ≤ K₀
  rw [abs_div, abs_of_pos hω]
  linarith [h', h''.le]

end Work.FTS_RegExport.RXT
