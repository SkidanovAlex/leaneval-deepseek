import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Far

open Filter Set

/-- Route: pick `N` with `farRadius (‖c₀‖+1) < ‖critZ c₀ N‖`
(`Work.NAKANE.BottcherJoint.exists_far_iterate`); by continuity the same holds for `c` near `c₀`.
For such `c`: `Phi c = varphiCrit c c` (`Work.NAKANE.Phi_eq_varphiCrit`),
`(varphiCrit c c)^(4^N) = varphiCrit c (critZ c N)` (`varphiCrit_functional_iterate` with
`Work.ParamRays.self_mem_critDomain`), and `varphiCrit c (critZ c N) = bottcher c (critZ c N)`
(`Work.NAKANE.jointVarphi_eq_jointBottcher_of_far'`).
NOTE: the small ball must also avoid the closed set `Mb`, since `Phi = 0` on `Mb`. -/
theorem phi_eq_root_comp_near {c₀ : ℂ} (hc₀ : c₀ ∉ Work.NAKANE2.Mb) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℂ, ‖c - c₀‖ < ε →
      (Work.NAKANE2.Phi c) ^ (4 ^ N) = Work.Bottcher.bottcher c (Work.NAKANE2.critZ c N) := by
  classical
  -- The parameter bound used throughout: `‖c‖ ≤ C = ‖c₀‖ + 1` on a small ball.
  set C : ℝ := ‖c₀‖ + 1 with hCdef
  have hCc₀ : ‖c₀‖ ≤ C := by rw [hCdef]; linarith
  -- ## Step 1: an escape gap at `c₀` and the resulting far iterate `N`.
  have hcrit : c₀ ∈ Work.ParamRays.critDomain c₀ := Work.ParamRays.self_mem_critDomain hc₀
  rw [Work.ParamRays.mem_critDomain] at hcrit
  set s : ℝ := (Work.ParamRays.greenFun c₀ c₀ - Work.ParamRays.paramPotential c₀) / 2 with hsdef
  have hspos : 0 < s := by rw [hsdef]; linarith
  obtain ⟨N, hN⟩ :=
    Work.NAKANE.BottcherJoint.exists_far_iterate (C := C) (B := ‖c₀‖) (s := s) hspos
  have hfar₀ : Work.NAKANE.farRadius C < ‖Work.NAKANE2.critZ c₀ N‖ :=
    hN c₀ c₀ hCc₀ le_rfl (by rw [hsdef]; linarith)
  -- ## Step 2: by continuity `‖critZ c N‖` stays far in a ball around `c₀`.
  have hcont : Continuous fun c : ℂ => Work.NAKANE2.critZ c N := by
    have h := (Work.NAKANE.continuous_joint_pMap_iterate N).comp
      (continuous_id.prodMk continuous_id)
    exact h
  have hopen : IsOpen {c : ℂ | Work.NAKANE.farRadius C < ‖Work.NAKANE2.critZ c N‖} :=
    isOpen_lt continuous_const hcont.norm
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hfar₀)
  -- ## Step 3: the closed set `Mb` is avoided near `c₀`.
  have hMb_open : IsOpen (Work.NAKANE2.Mb)ᶜ := Work.NAKANE.isClosed_Mb.isOpen_compl
  obtain ⟨ε₃, hε₃pos, hε₃⟩ := Metric.mem_nhds_iff.mp (hMb_open.mem_nhds hc₀)
  refine ⟨N, min ε₁ (min 1 ε₃), lt_min hε₁pos (lt_min one_pos hε₃pos), ?_⟩
  intro c hc
  have hc₁ : ‖c - c₀‖ < ε₁ := lt_of_lt_of_le hc (min_le_left _ _)
  have hc₂ : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc₃ : ‖c - c₀‖ < ε₃ := lt_of_lt_of_le hc (le_trans (min_le_right _ _) (min_le_right _ _))
  have hfar : Work.NAKANE.farRadius C < ‖Work.NAKANE2.critZ c N‖ :=
    hε₁ (by rw [Metric.mem_ball, dist_eq_norm]; exact hc₁)
  have hcC : ‖c‖ ≤ C := by
    have h1 : ‖c‖ ≤ ‖c₀‖ + ‖c - c₀‖ := by
      calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ = ‖c₀‖ + ‖c - c₀‖ := by ring
    rw [hCdef]; linarith
  have hcMb : c ∉ Work.NAKANE2.Mb :=
    hε₃ (by rw [Metric.mem_ball, dist_eq_norm]; exact hc₃)
  -- ## Step 4: assemble.
  calc (Work.NAKANE2.Phi c) ^ (4 ^ N)
      = (Work.Bottcher.varphiCrit c c) ^ (4 ^ N) := by
        rw [Work.NAKANE2.Phi_eq_varphiCrit hcMb]
    _ = Work.Bottcher.varphiCrit c (Work.NAKANE2.critZ c N) := by
        rw [Work.NAKANE.varphiCrit_functional_iterate
          (Work.ParamRays.self_mem_critDomain hcMb) N]
        rfl
    _ = Work.Bottcher.bottcher c (Work.NAKANE2.critZ c N) := by
        have h := Work.NAKANE.jointVarphi_eq_jointBottcher_of_far' hcC hfar
        rwa [Work.NAKANE.jointVarphi_apply, Work.NAKANE.jointBottcher_apply] at h

end Work.NAKANE2.Far
