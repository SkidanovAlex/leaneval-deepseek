import Mathlib

set_option linter.style.haveILetI false

open scoped Topology
open Filter

namespace Work.Drive.Final

/-- Given `V : ℝ² → ℝ` with `V 0 = 0` and Fréchet derivative `fst` at the origin, and an injective
linear map `T : ℝ² → ℝ²`, there is a point `ξ` with positive first coordinate, at which `V` is
positive and whose image under `T` lies in the open double cone `|y| < |x|`.

Proof: since `T` is injective on the finite-dimensional space `ℝ²` it is surjective, so
`T ⁻¹' {w | |w.2| < |w.1|}` is a nonempty open (hence not contained in the line `x = 0`) set; it is
moreover symmetric, so it contains some `v` with `v.1 > 0`. Along the ray `t ↦ t • v` we then have
`T (t • v) = t • T v`, still in the double cone, and `V (t • v) / t → v.1 > 0` as `t → 0⁺`, so for
small positive `t` the point `t • v` has all the required properties. -/
theorem exists_mem_doubleCone_of_fderivFst (V : ℝ × ℝ → ℝ) (hV0 : V 0 = 0)
    (hV : HasFDerivAt V (ContinuousLinearMap.fst ℝ ℝ ℝ) 0)
    (T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hTinj : Function.Injective T) :
    ∃ ξ : ℝ × ℝ, 0 < ξ.1 ∧ 0 < V ξ ∧ |(T ξ).2| < |(T ξ).1| := by
  have hsurj : Function.Surjective T := by
    have h : Function.Injective (T : (ℝ×ℝ) →ₗ[ℝ] (ℝ×ℝ)) := hTinj
    exact LinearMap.surjective_of_injective h
  have hC_open : IsOpen {w : ℝ×ℝ | |w.2| < |w.1|} :=
    isOpen_lt continuous_snd.abs continuous_fst.abs
  have hU_open : IsOpen (T ⁻¹' {w : ℝ×ℝ | |w.2| < |w.1|}) := hC_open.preimage T.continuous
  have hU_ne : (T ⁻¹' {w : ℝ×ℝ | |w.2| < |w.1|}).Nonempty := by
    obtain ⟨w, hw⟩ := hsurj (1,0)
    exact ⟨w, by rw [Set.mem_preimage, hw]; norm_num⟩
  have hex : ∃ v : ℝ×ℝ, v.1 ≠ 0 ∧ |(T v).2| < |(T v).1| := by
    by_contra h
    have h' : ∀ v, |(T v).2| < |(T v).1| → v.1 = 0 := by
      intro v hv
      by_contra hv0
      exact h ⟨v, hv0, hv⟩
    obtain ⟨v0, hv0⟩ := hU_ne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open v0 hv0
    have hmem1 : ((v0.1 + ε/2, v0.2) : ℝ×ℝ) ∈ Metric.ball v0 ε := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      rw [show v0.1 + ε/2 - v0.1 = ε/2 by ring, show v0.2 - v0.2 = 0 by ring,
          abs_of_pos (half_pos hε), abs_zero]
      exact max_lt (by linarith) (by linarith)
    have hmem2 : ((v0.1 - ε/2, v0.2) : ℝ×ℝ) ∈ Metric.ball v0 ε := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      rw [show v0.1 - ε/2 - v0.1 = -(ε/2) by ring, show v0.2 - v0.2 = 0 by ring,
          abs_neg, abs_of_pos (half_pos hε), abs_zero]
      exact max_lt (by linarith) (by linarith)
    have e1 : v0.1 + ε/2 = 0 := h' _ (hball hmem1)
    have e2 : v0.1 - ε/2 = 0 := h' _ (hball hmem2)
    linarith
  obtain ⟨v, hv1, hvC⟩ := hex
  have hpos : ∃ u : ℝ×ℝ, 0 < u.1 ∧ |(T u).2| < |(T u).1| := by
    rcases lt_or_gt_of_ne hv1 with hlt | hgt
    · refine ⟨-v, ?_, ?_⟩
      · simpa using neg_pos.mpr hlt
      · simpa [map_neg] using hvC
    · exact ⟨v, hgt, hvC⟩
  obtain ⟨v, hv1pos, hvC⟩ := hpos
  have hcurve : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const v
  have hV' : HasFDerivAt V (ContinuousLinearMap.fst ℝ ℝ ℝ) ((0:ℝ) • v) := by simpa using hV
  have hcomp : HasDerivAt (fun t : ℝ => V (t • v)) v.1 0 :=
    hV'.comp_hasDerivAt (f := fun t : ℝ => t • v) (f' := v) 0 hcurve
  have hslope := hcomp.tendsto_slope_zero_right
  have hslope' : Tendsto (fun t : ℝ => V (t • v) / t) (𝓝[>] (0:ℝ)) (𝓝 v.1) := by
    have heq : (fun t : ℝ => V (t • v) / t) =ᶠ[𝓝[>] (0:ℝ)]
        (fun t : ℝ => t⁻¹ • (V ((0 + t) • v) - V ((0:ℝ) • v))) := by
      filter_upwards with t
      simp [hV0, smul_eq_mul, div_eq_inv_mul]
    exact Filter.Tendsto.congr' heq.symm hslope
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ 0 < V (t • v) / t :=
    (show ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t from self_mem_nhdsWithin).and
      (hslope'.eventually (eventually_gt_nhds hv1pos))
  haveI : (𝓝[>] (0:ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  obtain ⟨t, ht_pos, ht_div⟩ := hev.exists
  refine ⟨t • v, ?h1, ?h2, ?h3⟩
  · simpa only [Prod.smul_fst, smul_eq_mul] using mul_pos ht_pos hv1pos
  · have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have hVt : V (t • v) = t * (V (t • v) / t) := by
      rw [mul_comm, div_mul_cancel₀ _ ht_ne]
    have := mul_pos ht_pos ht_div
    rwa [← hVt] at this
  · have hT : T (t • v) = t • T v := map_smul T t v
    simp only [hT, Prod.smul_snd, Prod.smul_fst, smul_eq_mul, abs_mul, abs_of_pos ht_pos]
    exact mul_lt_mul_of_pos_left hvC ht_pos

end Work.Drive.Final
