import Mathlib
import Submission.Work.Diff.EXT.AuxL.norm_hasDerivAt_zero_le
import Submission.Work.Diff.EXT.AuxL.opNorm_le_of_pos_fst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter Set
open scoped Topology

namespace Work.Diff.EXT.AuxL

theorem norm_fderiv_leftEndpoint_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {σ T : ℝ} (hσT : σ < T) {U : Set E} {y₀ : E} (hU : U ∈ nhds y₀)
    {Φ : ℝ × E → W} {M : ℝ} (hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℝ Φ ((Set.Ioo σ T) ×ˢ U))
    (hbd : ∀ p ∈ (Set.Ioo σ T) ×ˢ U, ‖fderiv ℝ Φ p‖ ≤ M) :
    ‖fderiv ℝ Φ (σ, y₀)‖ ≤ 3 * M := by
  by_cases hd : DifferentiableAt ℝ Φ (σ, y₀)
  · have key : ∀ v : ℝ × E, 0 < v.1 → ‖fderiv ℝ Φ (σ, y₀) v‖ ≤ M * ‖v‖ := by
      intro v hv
      obtain ⟨V, hVU, hVopen, hy₀V⟩ := mem_nhds_iff.mp hU
      have hcont : Tendsto (fun t : ℝ => y₀ + t • v.2) (𝓝 (0:ℝ)) (𝓝 y₀) := by
        have hc : Continuous fun t : ℝ => y₀ + t • v.2 := by fun_prop
        simpa using hc.tendsto 0
      have hb : ∃ b : ℝ, 0 < b ∧ ∀ t ∈ Set.Ioo (-b) b, y₀ + t • v.2 ∈ V := by
        obtain ⟨b, hbpos, hbV⟩ := Metric.mem_nhds_iff.mp (hcont.eventually (hVopen.mem_nhds hy₀V))
        refine ⟨b, hbpos, fun t ht => hbV ?_⟩
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact abs_lt.mpr ht
      obtain ⟨b, hbpos, hbV⟩ := hb
      have ha : 0 < (T - σ) / v.1 := div_pos (sub_pos.mpr hσT) hv
      set ε : ℝ := min ((T - σ) / v.1) b with hεdef
      have hε : 0 < ε := lt_min ha hbpos
      have hOpen : IsOpen ((Set.Ioo σ T) ×ˢ V) := isOpen_Ioo.prod hVopen
      have hdiff' : DifferentiableOn ℝ Φ ((Set.Ioo σ T) ×ˢ V) :=
        hdiff.mono (Set.prod_mono Subset.rfl hVU)
      set c : ℝ → ℝ × E := fun t => (σ + t * v.1, y₀ + t • v.2) with hcdef
      have hmem : ∀ t ∈ Set.Ioo (0:ℝ) ε, c t ∈ (Set.Ioo σ T) ×ˢ V := by
        intro t ht
        obtain ⟨ht0, htε⟩ := ht
        have htv : 0 < t * v.1 := mul_pos ht0 hv
        refine ⟨⟨?_, ?_⟩, hbV t ⟨?_, ?_⟩⟩
        · show σ < σ + t * v.1
          linarith
        · have h1 : t * v.1 < ((T - σ) / v.1) * v.1 :=
            mul_lt_mul_of_pos_right (lt_of_lt_of_le htε (min_le_left _ _)) hv
          rw [div_mul_cancel₀ _ (ne_of_gt hv)] at h1
          linarith
        · linarith
        · exact lt_of_lt_of_le htε (min_le_right _ _)
      have hcd : ∀ t : ℝ, HasDerivAt c v t := by
        intro t
        have h1 : HasDerivAt (fun t : ℝ => σ + t * v.1) v.1 t := by
          simpa [id] using ((hasDerivAt_id t).mul_const v.1).const_add σ
        have h2 : HasDerivAt (fun t : ℝ => y₀ + t • v.2) v.2 t := by
          simpa [id] using ((hasDerivAt_id t).smul_const (v.2)).const_add y₀
        simpa [c] using h1.prodMk h2
      set g : ℝ → W := fun t => Φ (c t) with hgdef
      have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt g ((fderiv ℝ Φ (c t)) v) t := by
        intro t ht
        have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (c t)) (c t) :=
          DifferentiableOn.hasFDerivAt hdiff' (hOpen.mem_nhds (hmem t ht))
        exact hΦ.comp_hasDerivAt t (hcd t)
      have hbound : ∀ t ∈ Set.Ioo (0:ℝ) ε, ‖(fderiv ℝ Φ (c t)) v‖ ≤ M * ‖v‖ := by
        intro t ht
        have hmemt : c t ∈ (Set.Ioo σ T) ×ˢ U := ⟨(hmem t ht).1, hVU (hmem t ht).2⟩
        calc ‖(fderiv ℝ Φ (c t)) v‖ ≤ ‖fderiv ℝ Φ (c t)‖ * ‖v‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right (hbd (c t) hmemt) (norm_nonneg v)
      have hg0 : HasDerivAt g ((fderiv ℝ Φ (σ, y₀)) v) 0 := by
        have hΦ0 : HasFDerivAt Φ (fderiv ℝ Φ (c 0)) (c 0) := by
          have h0 : c 0 = ((σ, y₀) : ℝ × E) := by simp [c]
          rw [h0]
          exact hd.hasFDerivAt
        have h := hΦ0.comp_hasDerivAt (0:ℝ) (hcd 0)
        simpa [g, c, Function.comp_def] using h
      exact norm_hasDerivAt_zero_le hε (mul_nonneg hM (norm_nonneg v)) hg0 hderiv hbound
    have hle : ‖fderiv ℝ Φ (σ, y₀)‖ ≤ M := opNorm_le_of_pos_fst _ key
    linarith
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp only [norm_zero]
    linarith

end Work.Diff.EXT.AuxL
