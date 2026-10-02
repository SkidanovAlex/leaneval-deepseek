import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Analysis.MorseLambda

open scoped ContDiff Topology

open scoped ContDiff in
theorem lambda_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Pin : E ≃L[ℝ] E) :
    ∃ e : OpenPartialHomeomorph (E →L[ℝ] E) (E →L[ℝ] E),
      0 ∈ e.source ∧ e 0 = 0 ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ S ∈ e.source, e S = 2 • S + S * (Pin : E →L[ℝ] E) * S) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let F : (E →L[ℝ] E) → (E →L[ℝ] E) := fun S => 2 • S + S * (Pin : E →L[ℝ] E) * S
  have hF : ContDiff ℝ ∞ F := by dsimp only [F]; fun_prop
  let L₀ : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := (2:ℝ) • (1 : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E))
  have hlin : HasFDerivAt (fun S : E →L[ℝ] E => 2 • S) L₀ 0 := by
    have h : HasFDerivAt (fun S : E →L[ℝ] E => L₀ S) L₀ 0 :=
      ContinuousLinearMap.hasFDerivAt L₀ (x := (0 : E →L[ℝ] E))
    have hfun : (fun S : E →L[ℝ] E => L₀ S) = (fun S : E →L[ℝ] E => 2 • S) := by
      funext S; simp [L₀, two_smul]
    rwa [hfun] at h
  have hquad : HasFDerivAt (fun S : E →L[ℝ] E => S * (Pin : E →L[ℝ] E) * S)
      (0 : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, mul_zero, sub_zero, zero_apply]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0 : E →L[ℝ] E)
        (show 0 < c / (‖(Pin : E →L[ℝ] E)‖ + 1) by positivity)] with h hh
    rw [Metric.mem_ball, dist_zero_right] at hh
    calc ‖(h * (Pin : E →L[ℝ] E)) * h‖
        ≤ ‖h * (Pin : E →L[ℝ] E)‖ * ‖h‖ := norm_mul_le _ _
      _ ≤ (‖h‖ * ‖(Pin : E →L[ℝ] E)‖) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le h _) (norm_nonneg h)
      _ = ‖(Pin : E →L[ℝ] E)‖ * ‖h‖ * ‖h‖ := by ring
      _ ≤ c * ‖h‖ := by
          have hr : ‖h‖ < c / (‖(Pin : E →L[ℝ] E)‖ + 1) := hh
          rw [lt_div_iff₀ (by positivity : (0:ℝ) < ‖(Pin : E →L[ℝ] E)‖ + 1)] at hr
          have step : ‖(Pin : E →L[ℝ] E)‖ * ‖h‖ ≤ c := by
            nlinarith [hr, norm_nonneg h]
          exact mul_le_mul_of_nonneg_right step (norm_nonneg h)
  have hFd : HasFDerivAt F L₀ 0 := by
    have h := hlin.add hquad
    have hfun : ((fun S : E →L[ℝ] E => 2 • S) + (fun S : E →L[ℝ] E => S * (Pin : E →L[ℝ] E) * S))
        = (fun S : E →L[ℝ] E => 2 • S + S * (Pin : E →L[ℝ] E) * S) := by
      funext S; rfl
    rw [hfun] at h
    dsimp only [F]
    simpa using h
  have hInv : L₀.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (1/2:ℝ) • (1 : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)))
    · ext x; simp [L₀, smul_smul]
    · ext x; simp [L₀, smul_smul]
  let f' : (E →L[ℝ] E) ≃L[ℝ] (E →L[ℝ] E) := Classical.choose hInv
  have hf' : (f' : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) = L₀ := Classical.choose_spec hInv
  have hFd' : HasFDerivAt F (f' : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) 0 := by rw [hf']; exact hFd
  have hcd : ContDiffAt ℝ ∞ F 0 := hF.contDiffAt
  let e0 : OpenPartialHomeomorph (E →L[ℝ] E) (E →L[ℝ] E) := hcd.toOpenPartialHomeomorph F hFd' hn
  have hmem0 : (0 : E →L[ℝ] E) ∈ e0.source := hcd.mem_toOpenPartialHomeomorph_source hFd' hn
  have hOpenInv : IsOpen {g : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) | g.IsInvertible} := by
    have h := ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E →L[ℝ] E) (F := E →L[ℝ] E)
    rwa [show Set.range ((↑) : ((E →L[ℝ] E) ≃L[ℝ] (E →L[ℝ] E)) → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E))
        = {g | g.IsInvertible} from by ext g; rfl] at h
  have hOpen : IsOpen {x : E →L[ℝ] E | (fderiv ℝ F x).IsInvertible} :=
    hOpenInv.preimage (hF.continuous_fderiv hn)
  let s : Set (E →L[ℝ] E) := {x | (fderiv ℝ F x).IsInvertible}
  have hs : IsOpen s := hOpen
  let e : OpenPartialHomeomorph (E →L[ℝ] E) (E →L[ℝ] E) := e0.restrOpen s hs
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : E →L[ℝ] E) ∈ e.source
    exact ⟨hmem0, by show (fderiv ℝ F 0).IsInvertible; rw [hFd.fderiv]; exact hInv⟩
  · show e 0 = 0
    change F 0 = 0
    simp [F]
  · show ContDiffOn ℝ ∞ ⇑e e.source
    change ContDiffOn ℝ ∞ F e.source
    exact hF.contDiffOn
  · show ContDiffOn ℝ ∞ ⇑e.symm e.target
    intro a ha
    have hxsrc : e.symm a ∈ e.source := e.map_target ha
    have hss : e.source ⊆ s := by
      show e0.source ∩ s ⊆ s
      exact Set.inter_subset_right
    have hsa : (fderiv ℝ F (e.symm a)).IsInvertible := hss hxsrc
    obtain ⟨A, hA⟩ := hsa
    refine (e.contDiffAt_symm (f₀' := A) ha ?_ ?_).contDiffWithinAt
    · rw [hA]
      exact (hF.contDiffAt.differentiableAt hn).hasFDerivAt
    · exact hF.contDiffAt
  · intro S hS
    change F S = 2 • S + S * (Pin : E →L[ℝ] E) * S
    rfl

end Work.Analysis.MorseLambda
