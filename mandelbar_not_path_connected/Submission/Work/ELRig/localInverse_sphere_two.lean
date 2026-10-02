import Mathlib
import Submission.Work.ELRig.analytic_local_crossing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Metric
open scoped Topology

/-- Local structure of the level sets of `t ↦ ‖k (1 + t) - p‖` near a point with `k 1 = p`
and `k' 1 ≠ 0`: there is a radius `ε` on which the norm is strictly increasing to the right of
`0` and strictly decreasing to the left of `0`, and each level below the values at `±ε` is hit
exactly once on either side.  The hard analytic content (strict monotonicity from
`AnalyticAt ℂ k 1` with `deriv k 1 ≠ 0`) is `Work.ELRig.alc_core`. -/
theorem localInverse_sphere_two {k : ℂ → ℂ} {p : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (han : AnalyticOnNhd ℂ k (Metric.ball 1 δ)) (hk1 : k 1 = p) (hd : deriv k 1 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      StrictMonoOn (fun t : ℝ => ‖k (1 + t) - p‖) (Set.Icc 0 ε) ∧
      StrictAntiOn (fun t : ℝ => ‖k (1 + t) - p‖) (Set.Icc (-ε) 0) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < ‖k (1 + ε) - p‖ → ρ < ‖k (1 - ε) - p‖ →
        (∃! t : ℝ, t ∈ Set.Ioo (0 : ℝ) ε ∧ ‖k (1 + t) - p‖ = ρ) ∧
        (∃! t : ℝ, t ∈ Set.Ioo (-ε) 0 ∧ ‖k (1 + t) - p‖ = ρ)) := by
  -- `k` is analytic at `1`, hence so is `z ↦ k (1 + z) - p` at `0`, with `0 ↦ 0` and nonzero
  -- derivative there.
  have h1mem : (1 : ℂ) ∈ Metric.ball 1 δ := by
    rw [Metric.mem_ball, dist_self]; exact hδ
  have hkan : AnalyticAt ℂ k 1 := han 1 h1mem
  have htrans : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0 := by
    have h1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 0 := analyticAt_const
    have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
    exact h1.add hid
  have hGan : AnalyticAt ℂ (fun z : ℂ => k (1 + z) - p) 0 :=
    (AnalyticAt.comp_of_eq (y := (1 : ℂ)) (f := fun z : ℂ => 1 + z) (x := (0 : ℂ))
      hkan htrans (by simp)).sub analyticAt_const
  have hG0 : (fun z : ℂ => k (1 + z) - p) 0 = 0 := by simp [hk1]
  have hGd : deriv (fun z : ℂ => k (1 + z) - p) 0 ≠ 0 := by
    rw [deriv_sub_const, deriv_comp_const_add]
    simpa using hd
  obtain ⟨δc, hδcpos, _c, _hcpos, _hlow, hmono, hanti⟩ := alc_core hGan hG0 hGd
  -- the target function is the one `alc_core` speaks about
  have hVA : (fun t : ℝ => ‖k (1 + t) - p‖) =
      (fun t : ℝ => ‖(fun z : ℂ => k (1 + z) - p) (t : ℂ)‖) := by
    funext t; simp
  refine ⟨min δc (δ / 2), ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min hδcpos (by linarith)
  · have h : min δc (δ / 2) ≤ δ / 2 := min_le_right _ _
    linarith
  · rw [hVA]
    exact hmono.mono (fun x hx => ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩)
  · rw [hVA]
    exact hanti.mono (fun x hx => ⟨le_trans (neg_le_neg (min_le_left _ _)) hx.1, hx.2⟩)
  · intro ρ hρ hρ1 hρ2
    set ε : ℝ := min δc (δ / 2) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hδcpos (by linarith)
    have hεδ : ε < δ := by rw [hεdef]; have := min_le_right δc (δ / 2); linarith
    have hεle : ε ≤ δc := by rw [hεdef]; exact min_le_left _ _
    -- continuity on `[-ε, ε]`, from `AnalyticOnNhd.continuousOn`
    have hcontA : ContinuousOn
        (fun t : ℝ => ‖(fun z : ℂ => k (1 + z) - p) (t : ℂ)‖) (Set.Icc (-ε) ε) := by
      have hmap : ContinuousOn (fun t : ℝ => (1 : ℂ) + (t : ℂ)) (Set.Icc (-ε) ε) := by
        fun_prop
      have hmaps : Set.MapsTo (fun t : ℝ => (1 : ℂ) + (t : ℂ)) (Set.Icc (-ε) ε)
          (Metric.ball (1 : ℂ) δ) := by
        intro t ht
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : (1 : ℂ) + (t : ℂ) - 1 = (t : ℂ) := by ring
        rw [h1]
        have ht' : |t| ≤ ε := by rw [Set.mem_Icc] at ht; exact abs_le.mpr ht
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith
      have hk : ContinuousOn (fun t : ℝ => k ((1 : ℂ) + (t : ℂ))) (Set.Icc (-ε) ε) :=
        han.continuousOn.comp hmap hmaps
      have hk' : ContinuousOn (fun t : ℝ => k ((1 : ℂ) + (t : ℂ)) - p) (Set.Icc (-ε) ε) :=
        hk.sub continuousOn_const
      simpa using hk'.norm
    have hmonoA : StrictMonoOn
        (fun t : ℝ => ‖(fun z : ℂ => k (1 + z) - p) (t : ℂ)‖) (Set.Icc 0 ε) :=
      hmono.mono (fun x hx => ⟨hx.1, le_trans hx.2 hεle⟩)
    have hantiA : StrictAntiOn
        (fun t : ℝ => ‖(fun z : ℂ => k (1 + z) - p) (t : ℂ)‖) (Set.Icc (-ε) 0) :=
      hanti.mono (fun x hx => ⟨le_trans (neg_le_neg hεle) hx.1, hx.2⟩)
    have hv0 : (fun t : ℝ => ‖k (1 + t) - p‖) 0 = 0 := by simp [hk1]
    have hcont0 : ContinuousOn (fun t : ℝ => ‖k (1 + t) - p‖) (Set.Icc 0 ε) := by
      rw [hVA]
      exact hcontA.mono (Set.Icc_subset_Icc (by linarith) (le_refl ε))
    have hcontneg : ContinuousOn (fun t : ℝ => ‖k (1 + t) - p‖) (Set.Icc (-ε) 0) := by
      rw [hVA]
      exact hcontA.mono (Set.Icc_subset_Icc (le_refl (-ε)) (by linarith))
    have hmonoV : StrictMonoOn (fun t : ℝ => ‖k (1 + t) - p‖) (Set.Icc 0 ε) := by
      rw [hVA]; exact hmonoA
    have hantiV : StrictAntiOn (fun t : ℝ => ‖k (1 + t) - p‖) (Set.Icc (-ε) 0) := by
      rw [hVA]; exact hantiA
    have hρ2' : ρ < (fun t : ℝ => ‖k (1 + t) - p‖) (-ε) := by
      simpa [Complex.ofReal_neg, sub_eq_add_neg] using hρ2
    exact ⟨alc_existsUnique_Ioo_of_strictMonoOn hεpos hcont0 hmonoV hv0 hρ (by simpa using hρ1),
           alc_existsUnique_Ioo_of_strictAntiOn hεpos hcontneg hantiV hv0 hρ hρ2'⟩

end Work.ELRig
