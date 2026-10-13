import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.I1cb

/-- For `k > 0` and `δ > 0` the function `θ ↦ k / θ` is not integrable on `(0, δ)`: the
singularity at `0` is too strong.  This is the sharp criterion
`intervalIntegral.integrableOn_Ioo_rpow_iff` (`x ↦ x ^ s` is integrable on `(0, δ)` exactly
when `-1 < s`) applied to `s = -1`. -/
theorem not_integrableOn_div_id_Ioo {k δ : ℝ} (hk : 0 < k) (hδ : 0 < δ) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => k / θ) (Set.Ioo 0 δ) := by
  intro h
  -- rewrite the integrand as `k * θ ^ (-1)`
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => k * θ ^ (-1:ℝ)) (Set.Ioo 0 δ) :=
    h.congr_fun (fun θ _ => by
      show k / θ = k * θ ^ (-1:ℝ)
      rw [div_eq_mul_inv, Real.rpow_neg_one]) measurableSet_Ioo
  -- divide by the non-zero constant `k`
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (-1:ℝ)) (Set.Ioo 0 δ) := by
    have hfun : (fun θ : ℝ => k⁻¹ * (k * θ ^ (-1:ℝ))) = fun θ : ℝ => θ ^ (-1:ℝ) := by
      funext θ
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hk), one_mul]
    rw [← hfun]
    exact h1.integrable.const_mul k⁻¹
  -- but `(-1) < -(1 : ℝ)` is false
  have h3 := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1:ℝ)) hδ).mp h2
  exact absurd h3 (lt_irrefl (-1:ℝ))

/-- **Vanishing at the left endpoint.**  If `F → c` as `θ → 0⁺` and `|F θ| ≤ C sin(2θ)|G θ|`
on `(0, d)` with `G` integrable on `(0, d)`, then `c = 0`.

Indeed, if `c ≠ 0` then `|F θ| ≥ |c|/2` near `0⁺`, so the pointwise bound forces
`|G θ| ≥ |c| / (4 C θ)` there; the right-hand side is not integrable on `(0, δ)` (it behaves
like `1/θ`), while `G` is — a contradiction.  When `C = 0` the bound forces `F = 0` on
`(0, d)`, hence `c = 0` by uniqueness of limits. -/
theorem boundary_vanish_left {F G : ℝ → ℝ} {c d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hlim : Filter.Tendsto F (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c))
    (hbd : ∀ θ ∈ Set.Ioo 0 d, |F θ| ≤ C * Real.sin (2*θ) * |G θ|)
    (hint : MeasureTheory.IntegrableOn G (Set.Ioo 0 d)) : c = 0 := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · -- degenerate case `C = 0`: `F` vanishes on `(0, d)`, so `c = 0`
    have hev : F =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] (fun _ : ℝ => (0:ℝ)) := by
      filter_upwards [Ioo_mem_nhdsGT hd] with θ hθ
      have h := hbd θ hθ
      rw [← hC0, zero_mul, zero_mul] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg (F θ)))
    have h0 : Filter.Tendsto (fun _ : ℝ => (0:ℝ)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c) :=
      Filter.Tendsto.congr' hev hlim
    exact tendsto_nhds_unique h0 tendsto_const_nhds
  · -- case `C > 0`
    by_contra hcne
    have hcabs : 0 < |c| := abs_pos.mpr hcne
    -- `F` stays away from `0` near `0⁺`
    have hF_large : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0), |c|/2 ≤ |F θ| := by
      have hball : Metric.ball c (|c|/2) ∈ nhds c := Metric.ball_mem_nhds c (by positivity)
      filter_upwards [hlim hball] with θ hθ
      rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hθ
      have h1 : |c| - |F θ| ≤ |c - F θ| := abs_sub_abs_le_abs_sub c (F θ)
      rw [abs_sub_comm] at h1
      linarith
    obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hF_large
    -- cut down to a small interval `(0, δ)`, `δ ≤ min ε d 1`
    set δ : ℝ := min (min ε d) 1 with hδdef
    have hδpos : 0 < δ := lt_min (lt_min hε hd) one_pos
    have hδd : δ ≤ d := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδε : δ ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ1 : δ ≤ 1 := min_le_right _ _
    -- on `(0, δ)` the pointwise bound forces `|G θ| ≥ (|c| / (4C)) / θ`
    have hGlarge : ∀ θ ∈ Set.Ioo (0:ℝ) δ, |c|/(4*C) / θ ≤ |G θ| := by
      intro θ hθ
      have hθ0 : 0 < θ := hθ.1
      have hθδ : θ < δ := hθ.2
      have hθd : θ ∈ Set.Ioo 0 d := ⟨hθ0, lt_of_lt_of_le hθδ hδd⟩
      have hFge : |c|/2 ≤ |F θ| := hεsub ⟨hθ0, lt_of_lt_of_le hθδ hδε⟩
      have hb := hbd θ hθd
      have hsinpos : 0 < Real.sin (2*θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three, hδ1])
      have hsinle : Real.sin (2*θ) ≤ 2*θ := Real.sin_le (by linarith)
      have hkey : |c| ≤ 4*C*θ*|G θ| := by
        nlinarith [hFge, hb, hsinle, hCpos, hθ0, abs_nonneg (G θ), hsinpos, hcabs]
      rw [div_le_iff₀ hθ0]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4*C)]
      linarith [hkey]
    -- `θ ↦ k / θ` would be integrable on `(0, δ)` by domination from `G`,
    -- contradicting its non-integrability
    have hk : 0 < |c|/(4*C) := div_pos hcabs (by positivity)
    have hGint : MeasureTheory.IntegrableOn G (Set.Ioo (0:ℝ) δ) :=
      hint.mono_set (Set.Ioo_subset_Ioo_right hδd)
    have hkint : MeasureTheory.IntegrableOn (fun θ : ℝ => |c|/(4*C) / θ) (Set.Ioo (0:ℝ) δ) := by
      refine MeasureTheory.Integrable.mono hGint.integrable
        ((Measurable.div measurable_const measurable_id).aestronglyMeasurable) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_of_nonneg (div_nonneg hk.le (le_of_lt hθ.1)), Real.norm_eq_abs]
      exact hGlarge θ hθ
    exact not_integrableOn_div_id_Ioo hk hδpos hkint

end Work.FTS.EllipticEst.H2W.I1cb
