import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.IFT.Basic
import Submission.Work.NAKANE2.Far.phi_eq_root_comp_near
import Submission.Work.NAKANE2.FarN.farB_strict

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Far

open Filter Set
open scoped Topology

/-- Strengthening of `Work.NAKANE2.Far.phi_eq_root_comp_near`: the iterate `N` can be chosen so
that the `N`-th critical-orbit point of `c₀` already lies in the far region
`{‖·‖ > farRadius (‖c₀‖ + 1)}`.  (This is the very estimate that the proof of
`phi_eq_root_comp_near` produces on the way; we simply keep it in the statement.) -/
theorem phi_eq_root_comp_near_far {c₀ : ℂ} (hc₀ : c₀ ∉ Work.NAKANE2.Mb) :
    ∃ N : ℕ, Work.NAKANE.farRadius (‖c₀‖ + 1) < ‖Work.NAKANE2.critZ c₀ N‖ ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℂ, ‖c - c₀‖ < ε →
        (Work.NAKANE2.Phi c) ^ (4 ^ N) = Work.Bottcher.bottcher c (Work.NAKANE2.critZ c N) := by
  classical
  set C : ℝ := ‖c₀‖ + 1 with hCdef
  have hCc₀ : ‖c₀‖ ≤ C := by rw [hCdef]; linarith
  have hcrit : c₀ ∈ Work.ParamRays.critDomain c₀ := Work.ParamRays.self_mem_critDomain hc₀
  rw [Work.ParamRays.mem_critDomain] at hcrit
  set s : ℝ := (Work.ParamRays.greenFun c₀ c₀ - Work.ParamRays.paramPotential c₀) / 2 with hsdef
  have hspos : 0 < s := by rw [hsdef]; linarith
  obtain ⟨N, hN⟩ :=
    Work.NAKANE.BottcherJoint.exists_far_iterate (C := C) (B := ‖c₀‖) (s := s) hspos
  have hfar₀ : Work.NAKANE.farRadius C < ‖Work.NAKANE2.critZ c₀ N‖ :=
    hN c₀ c₀ hCc₀ le_rfl (by rw [hsdef]; linarith)
  have hfar₀' : Work.NAKANE.farRadius (‖c₀‖ + 1) < ‖Work.NAKANE2.critZ c₀ N‖ := by
    rw [← hCdef]; exact hfar₀
  have hcont : Continuous fun c : ℂ => Work.NAKANE2.critZ c N := by
    have h := (Work.NAKANE.continuous_joint_pMap_iterate N).comp
      (continuous_id.prodMk continuous_id)
    exact h
  have hopen : IsOpen {c : ℂ | Work.NAKANE.farRadius C < ‖Work.NAKANE2.critZ c N‖} :=
    isOpen_lt continuous_const hcont.norm
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hfar₀)
  have hMb_open : IsOpen (Work.NAKANE2.Mb)ᶜ := Work.NAKANE.isClosed_Mb.isOpen_compl
  obtain ⟨ε₃, hε₃pos, hε₃⟩ := Metric.mem_nhds_iff.mp (hMb_open.mem_nhds hc₀)
  refine ⟨N, hfar₀', min ε₁ (min 1 ε₃), lt_min hε₁pos (lt_min one_pos hε₃pos), ?_⟩
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

/-! ## Strict differentiability of the parameter Böttcher map -/

/-- Route: `Phi c₀ ≠ 0` and `1 < ‖Phi c₀‖` (`Work.ParamRays.one_lt_norm_Phi`, off the mandelbar).
With `m = 4^N` and `phi_eq_root_comp_near`, `(Phi c)^m = B c` near `c₀` where `B` is strictly
differentiable at `c₀` (`exists_hasStrictFDerivAt_farB`).  Let `r` be the local inverse of
`w ↦ w^m` at `Phi c₀` (`HasStrictFDerivAt.to_localInverse` for
`HasStrictDerivAt (fun w => w^m) (m * (Phi c₀)^(m-1)) (Phi c₀)`, nonzero since `Phi c₀ ≠ 0`);
then `Phi = r ∘ B` near `c₀` because `Phi` is continuous and the local inverse is injective on its
source.  Conclude by the chain rule. -/
theorem phi_hasStrictFDerivAt {c₀ : ℂ} (hc₀ : c₀ ∉ Work.NAKANE2.Mb) :
    ∃ L : ℂ →L[ℝ] ℂ, HasStrictFDerivAt Work.NAKANE2.Phi L c₀ := by
  classical
  obtain ⟨N, hfar, ε, hεpos, hnear⟩ := phi_eq_root_comp_near_far hc₀
  obtain ⟨L_B, hB⟩ := Work.NAKANE2.FarN.farB_hasStrictFDerivAt (N := N) (c₀ := c₀) hfar
  set a : ℂ := Work.NAKANE2.Phi c₀ with hadef
  have hlt : 1 < ‖a‖ := Work.NAKANE.one_lt_norm_Phi hc₀
  have ha_ne : a ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hlt)
  set m : ℕ := 4 ^ N with hmdef
  have hm_ne : ((m : ℕ) : ℂ) ≠ 0 := by
    rw [hmdef]; exact Nat.cast_ne_zero.mpr (pow_ne_zero N (by norm_num))
  have hderiv_ne : ((m : ℂ) * a ^ (m - 1)) ≠ 0 :=
    mul_ne_zero hm_ne (pow_ne_zero _ ha_ne)
  have hsd : HasStrictDerivAt (fun w : ℂ => w ^ m) ((m : ℂ) * a ^ (m - 1)) a := by
    simpa using hasStrictDerivAt_pow m a
  let e : ℂ ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 ((m : ℂ) * a ^ (m - 1)) hderiv_ne)
  have hf : HasStrictFDerivAt (fun w : ℂ => w ^ m) (e : ℂ →L[ℂ] ℂ) a :=
    hsd.hasStrictFDerivAt_equiv hderiv_ne
  have hleft : ∀ᶠ x in 𝓝 a, HasStrictFDerivAt.localInverse (fun w : ℂ => w ^ m) e a hf (x ^ m) = x :=
    HasStrictFDerivAt.eventually_left_inverse (f := fun w : ℂ => w ^ m) (f' := e) hf
  have hInv : HasStrictFDerivAt (HasStrictFDerivAt.localInverse (fun w : ℂ => w ^ m) e a hf)
      (((e.symm : ℂ →L[ℂ] ℂ)).restrictScalars ℝ) (a ^ m) :=
    (HasStrictFDerivAt.to_localInverse (f := fun w : ℂ => w ^ m) (f' := e) hf).restrictScalars ℝ
  -- the far relation at `c₀` itself
  have hBc₀ : Work.Bottcher.bottcher c₀ (Work.NAKANE2.critZ c₀ N) = a ^ m := by
    have h := hnear c₀ (by simpa using hεpos)
    rw [← hadef] at h
    exact h.symm
  have hInv' : HasStrictFDerivAt (HasStrictFDerivAt.localInverse (fun w : ℂ => w ^ m) e a hf)
      (((e.symm : ℂ →L[ℂ] ℂ)).restrictScalars ℝ)
      (Work.Bottcher.bottcher c₀ (Work.NAKANE2.critZ c₀ N)) := hBc₀ ▸ hInv
  have hcomp : HasStrictFDerivAt
      (fun c => HasStrictFDerivAt.localInverse (fun w : ℂ => w ^ m) e a hf
        (Work.Bottcher.bottcher c (Work.NAKANE2.critZ c N)))
      ((((e.symm : ℂ →L[ℂ] ℂ)).restrictScalars ℝ).comp L_B) c₀ :=
    hInv'.comp c₀ hB
  -- `Phi` agrees with the composite near `c₀`
  have hcont : ContinuousAt Work.NAKANE2.Phi c₀ :=
    Work.NAKANE.continuousOn_Phi.continuousAt ((Work.NAKANE.isClosed_Mb.isOpen_compl).mem_nhds hc₀)
  have hball : Metric.ball c₀ ε ∈ 𝓝 c₀ := Metric.ball_mem_nhds c₀ hεpos
  have hpow : ∀ᶠ c in 𝓝 c₀,
      (Work.NAKANE2.Phi c) ^ m = Work.Bottcher.bottcher c (Work.NAKANE2.critZ c N) := by
    filter_upwards [hball] with c hc
    exact hnear c (by rw [Metric.mem_ball, dist_eq_norm] at hc; exact hc)
  have hev : (fun c => HasStrictFDerivAt.localInverse (fun w : ℂ => w ^ m) e a hf
        (Work.Bottcher.bottcher c (Work.NAKANE2.critZ c N))) =ᶠ[𝓝 c₀] Work.NAKANE2.Phi := by
    filter_upwards [hcont.tendsto hleft, hpow] with c hc1 hc2
    rw [← hc2]; exact hc1
  exact ⟨_, hcomp.congr_of_eventuallyEq hev⟩

end Work.NAKANE2.Far
