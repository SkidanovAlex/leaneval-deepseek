/-
# Vendored copies of the auxiliary compactness lemmas of `Work.Asymptotics.KernelBoundAux`

`Work.Asymptotics.KernelBoundAux` declares `Work.Asymptotics.continuous_scale` and a few other
names that are also declared in `Work.Asymptotics.MiddleRange.Basic`, so the two modules cannot be
imported together (Lean rejects the duplicate declaration).  The proof of the CKMRV cusp-`0`
bound `KMinusCuspBallBound` only needs the few lemmas copied here (`continuous_psi2`,
`continuous_psi4`, `bound_on_ball`, `bound_on_ball_real`, `exists_delta_Aj` and their
dependencies), so we vendor those into the namespace `Work.Asymptotics.MFix`, which is
import-compatible with the `MiddleRange` family.
-/
import Mathlib
import Submission.Work.Kernels.All

namespace Work.Asymptotics.MFix

open UpperHalfPlane

noncomputable section

private lemma continuous_jInvariantFun :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ) := by
  have h4 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ) :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous
  have hΔ : Continuous (fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ) :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have h : Work.Kernels.jInvariantFun =
      fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := by
    funext τ; rfl
  rw [h]
  exact (h4.pow 3).div hΔ (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)

lemma continuous_UFun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.UFun τ) :=
  (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4

lemma continuous_WFun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.WFun τ) :=
  (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4

lemma continuous_VFun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.VFun τ) :=
  (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4

lemma continuous_xi2Fun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.xi2Fun τ) := by
  have h : Work.Kernels.xi2Fun =
      fun τ : UpperHalfPlane => Work.Kernels.UFun τ + Work.Kernels.WFun τ := by
    funext τ; rfl
  rw [h]; exact continuous_UFun.add continuous_WFun

lemma continuous_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.psi2 ℓ τ) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.psi2 ℓ τ) =
      fun τ => Work.Kernels.xi2Fun τ * ℓ.L τ +
        (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi2Fun τ * ℓ.L τ +
        (SlashAction.map (2:ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
  rw [h]
  exact (continuous_xi2Fun.mul ℓ.holo.continuous).add
    ((continuous_UFun.add continuous_VFun).neg.mul ℓ.holo_S.continuous)

lemma continuous_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.psi4 ℓ τ) := by
  have hξ4 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.xi4Fun τ) := by
    have h' : Work.Kernels.xi4Fun = fun τ : UpperHalfPlane =>
        Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2 := by
      funext τ; rfl
    rw [h']; exact ((continuous_UFun.pow 2).add (continuous_WFun.pow 2)).sub
      ((continuous_VFun.pow 2).const_mul 2)
  have h : (fun τ : UpperHalfPlane => Work.Kernels.psi4 ℓ τ) =
      fun τ => Work.Kernels.xi4Fun τ * ℓ.L τ +
        (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2) *
          ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi4Fun τ * ℓ.L τ +
        (SlashAction.map (4:ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi4S_apply τ]
  rw [h]
  exact (hξ4.mul ℓ.holo.continuous).add
    (((continuous_UFun.pow 2).add (continuous_VFun.pow 2)).sub
      ((continuous_WFun.pow 2).const_mul 2) |>.mul ℓ.holo_S.continuous)

/-- A continuous complex-valued function is bounded on a closed ball. -/

lemma bound_on_ball {τ₀ : UpperHalfPlane} {R : ℝ} {f : UpperHalfPlane → ℂ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ‖f τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (x := τ₀) (r := R)).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun τ hτ => le_trans (hC τ hτ) (le_max_left _ _)⟩

/-- A continuous real-valued function is bounded above on a closed ball. -/

lemma bound_on_ball_real {τ₀ : UpperHalfPlane} {R : ℝ} {f : UpperHalfPlane → ℝ}
    (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → f τ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (x := τ₀) (r := R)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun τ hτ => ?_⟩
  have h := hC τ hτ
  rw [Real.norm_eq_abs] at h
  exact le_trans (le_abs_self _) (le_trans h (le_max_left _ _))

/-- The uniform lower bound `δ ≤ ‖Δ τ‖` on a closed ball, together with the uniform upper
bound `‖j τ‖ ≤ Aj` (the compactness input of both cusp estimates). -/

lemma exists_delta_Aj {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ δ Aj : ℝ, 0 < δ ∧ 0 ≤ Aj ∧
      (∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → δ ≤ ‖Work.Kernels.DeltaFun τ‖) ∧
      (∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ‖Work.Kernels.jInvariantFun τ‖ ≤ Aj) := by
  obtain ⟨τm, hτm_mem, hτm_min⟩ :=
    (isCompact_closedBall (x := τ₀) (r := R)).exists_isMinOn
      ⟨τ₀, Metric.mem_closedBall_self hR.le⟩
      ((Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous.norm).continuousOn)
  obtain ⟨Aj, hAj0, hAj⟩ := bound_on_ball (τ₀ := τ₀) (R := R) continuous_jInvariantFun
  exact ⟨‖Work.Kernels.DeltaFun τm‖, Aj,
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τm), hAj0,
    fun τ hτ => hτm_min hτ, hAj⟩

/-! ## Generic arithmetic helpers (kept as separate lemmas so that the big kernel terms
never enter the unification problems) -/

end

end Work.Asymptotics.MFix
