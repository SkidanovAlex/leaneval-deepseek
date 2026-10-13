import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option linter.unusedVariables false in
theorem notIntegrableOn_Itheta_of_rpow_lower {p C : ℝ} {h : ℝ → ℝ}
    (hC : 0 < C) (hp : p ≤ -1) (hh0 : ∀ θ, 0 ≤ h θ)
    (hlower : ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi / 2 ∧
      ∀ θ ∈ Set.Ioo (0 : ℝ) ε, C * θ ^ p ≤ h θ) :
    ¬ MeasureTheory.IntegrableOn h Work.Spaces.Iθ := by
  -- `θ ↦ C θ^p` is, on any `(0,e)` with `e ≤ 1`, pointwise ≥ `C/θ`, which is not integrable.
  obtain ⟨ε, hεpos, hεle, hlow⟩ := hlower
  intro hint
  set e : ℝ := min ε 1 with he
  have he_pos : 0 < e := lt_min hεpos zero_lt_one
  have he_le_eps : e ≤ ε := min_le_left _ _
  have he_le_one : e ≤ 1 := min_le_right _ _
  have he_le_pi : e ≤ Real.pi / 2 := le_trans he_le_eps hεle
  have hsub : Set.Ioo (0 : ℝ) e ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2.le he_le_pi⟩
  have hint' : MeasureTheory.Integrable h (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) e)) :=
    hint.mono_set hsub
  have hdom : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) e)),
      ‖(fun x : ℝ => C * x⁻¹) x‖ ≤ h x := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := lt_of_lt_of_le hx.2 he_le_one
    have hxe : x < ε := lt_of_lt_of_le hx.2 he_le_eps
    have hle : x ^ (-1 : ℝ) ≤ x ^ p :=
      (Real.rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1).2 hp
    have h1 : C * x ^ (-1 : ℝ) ≤ C * x ^ p := mul_le_mul_of_nonneg_left hle hC.le
    rw [Real.rpow_neg_one x] at h1
    have h2 : C * x ^ p ≤ h x := hlow x ⟨hx0, hxe⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (mul_pos hC (inv_pos.mpr hx0)))]
    exact le_trans h1 h2
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => C * x⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) e)) :=
    (measurable_const.mul measurable_inv).aestronglyMeasurable
  have hint2 : MeasureTheory.Integrable (fun x : ℝ => C * x⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) e)) :=
    hint'.mono' hmeas hdom
  have hint3 : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Set.Ioo (0 : ℝ) e) := by
    have h2 : MeasureTheory.Integrable (fun x : ℝ => C⁻¹ * (C * x⁻¹))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) e)) := hint2.const_mul C⁻¹
    refine h2.congr ?_
    filter_upwards with x
    rw [Real.rpow_neg_one]
    field_simp
  have hfin := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1 : ℝ)) he_pos).1 hint3
  exact absurd hfin (by norm_num)

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
