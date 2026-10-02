import Mathlib
import Submission.Work.ThomBordism.Grassmann.NuRadialDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

/-- The inverse radial map `nuRadialInv k ν` is continuous, for a continuous fibrewise norm `ν`
that is non-negative and vanishes exactly on the zero section.  (Positive homogeneity is *not*
needed for this direction.) -/
theorem continuous_nuRadialInv (X : Type*) [TopologicalSpace X] (k : ℕ)
    (ν : X × EuclideanSpace ℝ (Fin k) → ℝ) (hcont : Continuous ν)
    (hnonneg : ∀ z, 0 ≤ ν z)
    (hzero : ∀ (x : X) (v : EuclideanSpace ℝ (Fin k)), ν (x, v) = 0 ↔ v = 0) :
    Continuous (nuRadialInv k ν) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.2 = 0
  · have hz0 : nuRadialInv k ν z = 0 := by simp [nuRadialInv, hz]
    rw [ContinuousAt, hz0, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδpos, U, hU, hUle⟩ := exists_nhds_le_nu k ν hcont hnonneg hzero z.1
    have hεδ : 0 < ε * δ := mul_pos hε hδpos
    have hmem : U ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε * δ) ∈ 𝓝 z := by
      rw [nhds_prod_eq]
      have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε * δ) ∈ 𝓝 z.2 := by
        rw [hz]; exact Metric.ball_mem_nhds 0 hεδ
      exact Filter.prod_mem_prod hU hball
    refine Filter.mem_of_superset hmem (fun z' hz' => ?_)
    obtain ⟨hx, hw⟩ := Set.mem_prod.mp hz'
    rw [Metric.mem_ball, dist_zero_right] at hw
    change dist (nuRadialInv k ν z') 0 < ε
    rw [dist_zero_right]
    by_cases hw0 : z'.2 = 0
    · rw [show nuRadialInv k ν z' = 0 from by
        rw [show z' = (z'.1, 0) from Prod.ext rfl hw0]; simp [nuRadialInv]]
      rw [norm_zero]; exact hε
    · have hunit : ‖‖z'.2‖⁻¹ • z'.2‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
      have hδle : δ ≤ ν (z'.1, ‖z'.2‖⁻¹ • z'.2) := hUle z'.1 hx _ hunit
      have hνpos : 0 < ν (z'.1, ‖z'.2‖⁻¹ • z'.2) := lt_of_lt_of_le hδpos hδle
      have hle : (ν (z'.1, ‖z'.2‖⁻¹ • z'.2))⁻¹ ≤ δ⁻¹ :=
        (inv_le_inv₀ hνpos hδpos).mpr hδle
      rw [nuRadialInv, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (hnonneg _))]
      calc (ν (z'.1, ‖z'.2‖⁻¹ • z'.2))⁻¹ * ‖z'.2‖
          ≤ δ⁻¹ * ‖z'.2‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ < δ⁻¹ * (ε * δ) := mul_lt_mul_of_pos_left hw (inv_pos.mpr hδpos)
        _ = ε := by field_simp
  · have hzδ : ‖z.2‖⁻¹ • z.2 ≠ 0 := by
      rw [smul_ne_zero_iff]
      exact ⟨inv_ne_zero (norm_ne_zero_iff.mpr hz), hz⟩
    have hcont1 : ContinuousAt (fun z : X × EuclideanSpace ℝ (Fin k) =>
        ν (z.1, ‖z.2‖⁻¹ • z.2)) z := by
      have hpair : ContinuousAt (fun z : X × EuclideanSpace ℝ (Fin k) =>
          (z.1, ‖z.2‖⁻¹ • z.2)) z :=
        (continuous_fst.continuousAt (x := z)).prodMk
          ((((continuous_snd.norm).continuousAt (x := z)).inv₀
            (norm_ne_zero_iff.mpr hz)).smul (continuous_snd.continuousAt (x := z)))
      exact (hcont.continuousAt.comp hpair)
    have hcont2 : ContinuousAt (fun z : X × EuclideanSpace ℝ (Fin k) =>
        (ν (z.1, ‖z.2‖⁻¹ • z.2))⁻¹) z :=
      hcont1.inv₀ (fun h => hzδ ((hzero z.1 (‖z.2‖⁻¹ • z.2)).mp h))
    exact hcont2.smul (continuous_snd.continuousAt (x := z))

end

end Work.ThomBordism.Grassmann
