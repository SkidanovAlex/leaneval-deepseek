import Mathlib
import Submission.Work.NAKANE.PotentialTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.PhiProper

/-- **`Φ` is proper over the exterior disc.** For `K` compact with `1 < ‖w‖` for all `w ∈ K`, the set of parameters outside the mandelbar with `Φ c ∈ K` is compact. (`Mb` is the mandelbar, `Φ = Work.ParamRays.Phi`.) -/
theorem isCompact_Phi_preimage {K : Set ℂ} (hK : IsCompact K)
    (hK1 : ∀ w ∈ K, 1 < ‖w‖) :
    IsCompact {c : ℂ | c ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
      Work.ParamRays.Phi c ∈ K} := by
  -- A strict positive lower bound for `‖w‖` on `K`.
  obtain ⟨a, ha1, haK⟩ := hK.exists_forall_le' (f := fun w : ℂ => ‖w‖)
    continuous_norm.continuousOn (a := (1 : ℝ)) hK1
  have ha0 : (0 : ℝ) < a := by linarith
  set t : ℝ := Real.log a / 2 with ht
  have ht0 : 0 < t := by rw [ht]; exact div_pos (Real.log_pos ha1) (by norm_num)
  -- The closed set `A = {c | t ≤ paramPotential c}`; it is disjoint from the mandelbar.
  set A : Set ℂ := {c : ℂ | t ≤ Work.ParamRays.paramPotential c} with hAdef
  have hAclosed : IsClosed A := by
    rw [hAdef]
    exact isClosed_le continuous_const Work.NAKANE.continuous_paramPotential
  have hAsub : A ⊆ {c : ℂ | c ∉ LeanEval.ComplexAnalysis.Mandelbar} := by
    intro c hc
    rw [hAdef] at hc
    change t ≤ Work.ParamRays.paramPotential c at hc
    intro hcMb
    have h0 : Work.ParamRays.paramPotential c = 0 :=
      (Work.ParamRays.paramPotential_eq_zero_iff c).mpr hcMb
    rw [h0] at hc
    linarith
  have hcontA : ContinuousOn Work.ParamRays.Phi A :=
    Work.NAKANE.continuousOn_Phi.mono hAsub
  -- The set in question is exactly `A ∩ Φ ⁻¹' K`.
  have hset : {c : ℂ | c ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
      Work.ParamRays.Phi c ∈ K} = A ∩ Work.ParamRays.Phi ⁻¹' K := by
    ext c
    constructor
    · intro hc
      refine ⟨?_, hc.2⟩
      rw [hAdef]
      change t ≤ Work.ParamRays.paramPotential c
      have hbound : a ≤ ‖Work.ParamRays.Phi c‖ := haK (Work.ParamRays.Phi c) hc.2
      have hmod := Work.ParamRays.norm_Phi_eq_exp Work.Bottcher.bottcherExists_crit hc.1
      rw [hmod] at hbound
      have hlog : Real.log a ≤ 2 * Work.ParamRays.paramPotential c := by
        have := Real.log_le_log ha0 hbound
        rwa [Real.log_exp] at this
      rw [ht]
      linarith
    · rintro ⟨hA, hPK⟩
      refine ⟨?_, hPK⟩
      intro hcMb
      rw [hAdef] at hA
      change t ≤ Work.ParamRays.paramPotential c at hA
      have h0 : Work.ParamRays.paramPotential c = 0 :=
        (Work.ParamRays.paramPotential_eq_zero_iff c).mpr hcMb
      rw [h0] at hA
      linarith
  rw [hset]
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · exact hcontA.preimage_isClosed_of_isClosed hAclosed hK.isClosed
  · obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    obtain ⟨C, hC, hCs⟩ := Filter.mem_cocompact.mp Work.NAKANE.Phi_lower_bound_atTop
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : ℂ)
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max (2 * M) R)).subset ?_
    rintro c ⟨_hA, hPK⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hKbound : ‖Work.ParamRays.Phi c‖ ≤ M := by
      have h := hM hPK
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    by_cases hcC : c ∈ C
    · have h := hR hcC
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact le_trans h (le_max_right _ _)
    · have h : ‖c‖ / 2 ≤ ‖Work.ParamRays.Phi c‖ := hCs hcC
      have h2 : ‖c‖ ≤ 2 * M := by linarith
      exact le_trans h2 (le_max_left _ _)

end Work.NAKANE.PhiProper
