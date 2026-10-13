import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

/-- If `g` dominates `c * θ ^ r` (with `c > 0`, `r ≤ -1`) on a right neighbourhood `(0, δ)` of the
origin, then `g` is not integrable on `(0, ε)` for `ε ≥ δ > 0`: the singularity of `θ ^ r` at `0`
is non-integrable. -/
theorem not_integrableOn_of_rpow_le (g : ℝ → ℝ) {ε δ r c : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε) (hr : r ≤ -1) (hc : 0 < c)
    (hle : ∀ θ ∈ Set.Ioo (0:ℝ) δ, c * θ ^ r ≤ g θ) :
    ¬ MeasureTheory.IntegrableOn g (Set.Ioo (0:ℝ) ε) := by
  intro h
  -- restrict the assumed integrability to the inner interval `(0, δ)`
  have hsub : Set.Ioo (0:ℝ) δ ⊆ Set.Ioo (0:ℝ) ε :=
    fun θ hθ => ⟨hθ.1, lt_of_lt_of_le hθ.2 hδε⟩
  have hg : MeasureTheory.IntegrableOn g (Set.Ioo (0:ℝ) δ) := h.mono_set hsub
  -- `θ ↦ θ ^ r` is continuous (hence a.e. strongly measurable) on `(0, δ)`
  have hcont : ContinuousOn (fun θ : ℝ => θ ^ r) (Set.Ioo (0:ℝ) δ) :=
    continuousOn_id.rpow_const (fun θ hθ => Or.inl (ne_of_gt hθ.1))
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => c * θ ^ r)
      (volume.restrict (Set.Ioo (0:ℝ) δ)) :=
    (continuousOn_const.mul hcont).aestronglyMeasurable measurableSet_Ioo
  -- on `(0, δ)` the coercive bound gives `‖c * θ ^ r‖ ≤ ‖g θ‖`
  have hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0:ℝ) δ)), ‖c * θ ^ r‖ ≤ ‖g θ‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hθr : 0 < θ ^ r := Real.rpow_pos_of_pos hθ.1 r
    have hpos : 0 < c * θ ^ r := mul_pos hc hθr
    have hle' : c * θ ^ r ≤ g θ := hle θ hθ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos,
      abs_of_nonneg (le_trans hpos.le hle')]
    exact hle'
  have hF : Integrable (fun θ : ℝ => c * θ ^ r) (volume.restrict (Set.Ioo (0:ℝ) δ)) :=
    hg.norm.mono' hmeas hae
  -- rescale to get integrability of `θ ↦ θ ^ r` itself
  have hG : MeasureTheory.IntegrableOn (fun θ : ℝ => c⁻¹ * (c * θ ^ r)) (Set.Ioo (0:ℝ) δ) :=
    hF.const_mul c⁻¹
  have hpow : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ r) (Set.Ioo (0:ℝ) δ) :=
    MeasureTheory.IntegrableOn.congr_fun hG
      (fun θ hθ => by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul])
      measurableSet_Ioo
  -- but `θ ↦ θ ^ r` is integrable on `(0, δ)` only when `-1 < r`
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mp hpow
  linarith

end Work.Coercivity
