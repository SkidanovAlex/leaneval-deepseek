/-
# The cusp-`i∞` expansion of the kernel on the closed tangency region `ctanCl`

The difference `K^{(d)}(τ,it) - Aexp (Gcusp ℓ d) τ t` between the CKMRV kernel along the contour
and its non-decaying cusp part decays like `e^{-πt}` uniformly on the closed tangency region
`ctanCl` of `Work.Asymptotics.HalfFunnel.tangLayerDefs`, for `t ≥ 3/2`.

## Architecture

Identical to `Work.Asymptotics.arcT_tail` / `Work.Asymptotics.HalfFunnel.lowBad_Aexp_tail`:

* the *large-`t`* part is the cusp expansion `Work.Asymptotics.kernel_axis_bound` on the compact
  set `ctanCl` (no `⊆ 𝒟` hypothesis: `ctanCl` touches the boundary of the fundamental domain);
* for the remaining window `3/2 ≤ t ≤ max T 3/2` the difference is bounded because on that
  compact window the contour points `i t` avoid the whole `SL(2,ℤ)`-orbit of `τ ∈ ctanCl`:
  `Work.Asymptotics.HalfFunnel.tangOrbitHeight` says every orbit point of `τ ∈ ctanCl` has
  height `< 3/2`, so `j τ ≠ j (i t)` (`jInvariantFun_ne_iAxisFun_of_mem_ctanCl`).  Hence
  `K^{(d)}` is continuous there (`Work.Asymptotics.continuousOn_Kfun_clean`, via
  `exists_bound_Kfun_off_coincidence`), and `Aexp` is continuous because its coefficient
  functions `Gcusp ℓ d i j` are (`continuous_Gcusp_tang`).
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitHeight
import Submission.Work.Asymptotics.HalfFunnel.lowBad_Aexp_tail
import Submission.Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
import Submission.Work.Asymptotics.cuspExpansionKernel
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.HalfFunnel

open Work.Kernels

lemma jInvariantFun_ne_iAxisFun_of_mem_ctanCl {τ : ℍ} (hτ : τ ∈ ctanCl) {t : ℝ}
    (ht : 3 / 2 ≤ t) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (iAxisFun t) := by
  intro h
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have him : (iAxisFun t).im = t := by rw [iAxisFun_im, max_eq_left ht1]
  have hτ' : (γ⁻¹ • τ).im = t := by
    rw [← hγ, inv_smul_smul]
    exact him
  have hlt := tangOrbitHeight τ hτ γ⁻¹
  rw [hτ'] at hlt
  linarith

/-! ## Continuity of the coefficient functions `Gcusp ℓ d i j` -/

lemma continuous_psi2_tang (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) := by
  have hxi2 : Continuous (fun τ : ℍ => Work.Kernels.xi2Fun τ) := by
    have h : (fun τ : ℍ => Work.Kernels.xi2Fun τ) =
        fun τ => Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
    rw [h]
    exact ((Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4).add
      ((Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4)
  have hU : Continuous (fun τ : ℍ => Work.Kernels.UFun τ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
  have hV : Continuous (fun τ : ℍ => Work.Kernels.VFun τ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
  have h : (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) = fun τ : ℍ =>
      Work.Kernels.xi2Fun τ * ℓ.L τ +
        (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi2Fun τ * ℓ.L τ +
      (SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
  rw [h]
  exact (hxi2.mul ℓ.holo.continuous).add (((hU.add hV).neg).mul ℓ.holo_S.continuous)

lemma continuous_psi4_tang (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := by
  have hxi4 : Continuous (fun τ : ℍ => Work.Kernels.xi4Fun τ) := by
    have h : (fun τ : ℍ => Work.Kernels.xi4Fun τ) = fun τ =>
        Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2 := rfl
    rw [h]
    have hU : Continuous (fun τ : ℍ => Work.Kernels.UFun τ) :=
      (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
    have hW : Continuous (fun τ : ℍ => Work.Kernels.WFun τ) :=
      (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4
    have hV : Continuous (fun τ : ℍ => Work.Kernels.VFun τ) :=
      (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
    exact ((hU.pow 2).add (hW.pow 2)).sub ((hV.pow 2).const_mul 2)
  have hU : Continuous (fun τ : ℍ => Work.Kernels.UFun τ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
  have hV : Continuous (fun τ : ℍ => Work.Kernels.VFun τ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
  have hW : Continuous (fun τ : ℍ => Work.Kernels.WFun τ) :=
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4
  have h : (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) = fun τ =>
      Work.Kernels.xi4Fun τ * ℓ.L τ +
        (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
          * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi4Fun τ * ℓ.L τ +
      (SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi4S_apply τ]
  rw [h]
  exact (hxi4.mul ℓ.holo.continuous).add
    (((hU.pow 2).add (hV.pow 2)).sub ((hW.pow 2).const_mul 2) |>.mul ℓ.holo_S.continuous)

lemma continuous_Gcusp8_tang (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Continuous (fun τ : ℍ => Work.Asymptotics.Gcusp8 ℓ i j τ) := by
  have hphi : ∀ k : Fin 3, Continuous (fun τ : ℍ => Work.Kernels.phiVec τ k) :=
    fun k => (Work.Kernels.KernelGrowth.PhiVec_InP k).1.continuous
  have hE4 : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
    (ModularForm.holo' ModularForm.E₄).continuous
  have hE6 : Continuous (fun τ : ℍ => Work.Kernels.E6Fun τ) :=
    (ModularForm.holo' ModularForm.E₆).continuous
  have hpsi4 : Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := continuous_psi4_tang ℓ
  unfold Work.Asymptotics.Gcusp8
  split_ifs <;> fun_prop

lemma continuous_Gcusp24_tang (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Continuous (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ i j τ) := by
  have hphi : ∀ k : Fin 3, Continuous (fun τ : ℍ => Work.Kernels.phiVec τ k) :=
    fun k => (Work.Kernels.KernelGrowth.PhiVec_InP k).1.continuous
  have hE4 : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
    (ModularForm.holo' ModularForm.E₄).continuous
  have hE6 : Continuous (fun τ : ℍ => Work.Kernels.E6Fun τ) :=
    (ModularForm.holo' ModularForm.E₆).continuous
  have hDel : Continuous (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
    (CuspForm.holo' CuspForm.discriminant).continuous
  have hpsi2 : Continuous (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) := continuous_psi2_tang ℓ
  have hpsi4 : Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := continuous_psi4_tang ℓ
  unfold Work.Asymptotics.Gcusp24
  split_ifs <;> fun_prop

lemma continuous_Gcusp_tang (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (_hd : d = 8 ∨ d = 24)
    (i j : Fin 2) : Continuous (fun τ : ℍ => Work.Asymptotics.Gcusp ℓ d i j τ) := by
  have h8 : Continuous (fun τ : ℍ => Work.Asymptotics.Gcusp8 ℓ i j τ) := continuous_Gcusp8_tang ℓ i j
  have h24 : Continuous (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ i j τ) :=
    continuous_Gcusp24_tang ℓ i j
  unfold Work.Asymptotics.Gcusp
  split_ifs with h
  · exact h8
  · exact h24

lemma continuous_Aexp_tang (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Continuous (fun p : ℍ × ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) p.1 p.2) := by
  have hGc : ∀ i j : Fin 2, Continuous (fun τ : ℍ => Work.Asymptotics.Gcusp ℓ d i j τ) :=
    fun i j => continuous_Gcusp_tang ℓ d hd i j
  unfold Work.Asymptotics.Aexp
  fun_prop

theorem tangTailExpansion (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.HalfFunnel.ctanCl → 3 / 2 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨C₀, M₀, T, hC₀, hM₀, hTpos, htail⟩ := kernel_axis_bound ℓ d hd isCompact_ctanCl
  set T₁ : ℝ := max T (3 / 2) with hT₁def
  have hT₁ge : (3 / 2 : ℝ) ≤ T₁ := le_max_right _ _
  -- the compact set of contour points in the window
  set Tset : Set ℍ := iAxisFun '' Set.Icc (3 / 2 : ℝ) T₁ with hTsetdef
  have hTset_compact : IsCompact Tset := isCompact_Icc.image continuous_iAxisFun
  have hsep : ∀ (τ : ℍ), τ ∈ ctanCl → ∀ (z : ℍ), z ∈ Tset →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    rintro τ hτ z ⟨t, ht, rfl⟩
    exact jInvariantFun_ne_iAxisFun_of_mem_ctanCl hτ ht.1
  obtain ⟨CK, hCKpos, hCK⟩ := exists_bound_Kfun_off_coincidence ℓ d hd isCompact_ctanCl hTset_compact hsep
  obtain ⟨B, hB⟩ := (isCompact_ctanCl.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuous_Aexp_tang ℓ d hd).continuousOn
  -- the pointwise bound on the window
  have hwin : ∀ (τ : ℍ) (t : ℝ), τ ∈ ctanCl → t ∈ Set.Icc (3 / 2 : ℝ) T₁ →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ CK + B := by
    intro τ t hτ ht
    have ht1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    rw [Work.Kernels.Kaxis, dif_pos htpos]
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · rw [show Work.Kernels.imagAxis t htpos = iAxisFun t from
        (iAxisFun_eq_imagAxis ht1).symm]
      exact hCK τ hτ (iAxisFun t) ⟨t, ht, rfl⟩
    · exact hB (τ, t) ⟨hτ, ht⟩
  set C : ℝ := max C₀ ((CK + B) * Real.exp (Real.pi * T₁)) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCle : C₀ ≤ C := by
    rw [hCdef]; linarith [le_max_left C₀ ((CK + B) * Real.exp (Real.pi * T₁))]
  have hCge : (CK + B) * Real.exp (Real.pi * T₁) ≤ C := by
    rw [hCdef]; linarith [le_max_right C₀ ((CK + B) * Real.exp (Real.pi * T₁))]
  refine ⟨C, M₀, 0, hCpos, hM₀, le_refl 0, fun τ t hτ ht => ?_⟩
  have ht32 : (3 / 2 : ℝ) ≤ t := ht
  rcases le_or_gt t T with htT | htT
  · have hmem : t ∈ Set.Icc (3 / 2 : ℝ) T₁ := ⟨ht32, le_trans htT (le_max_left T (3 / 2))⟩
    have hb := hwin τ t hτ hmem
    have h0 : CK + B = ((CK + B) * Real.exp (Real.pi * T₁)) * Real.exp (-(Real.pi * T₁)) := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have h1 : (1 : ℝ) ≤ 1 + t := by linarith
    have hMa : (1 : ℝ) ≤ (1 + t) ^ M₀ := Real.one_le_rpow h1 hM₀
    have hexp : Real.exp (-(Real.pi * T₁)) ≤ Real.exp (-(Real.pi * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, le_trans htT (le_max_left T (3 / 2))]
    rw [h0] at hb
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ ((CK + B) * Real.exp (Real.pi * T₁)) * Real.exp (-(Real.pi * T₁)) := hb
      _ ≤ C * Real.exp (-(Real.pi * T₁)) :=
          mul_le_mul_of_nonneg_right hCge (Real.exp_pos _).le
      _ ≤ C * ((1 + t) ^ M₀ * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_left
            (le_trans hexp (le_mul_of_one_le_left (Real.exp_pos _).le hMa)) hCpos.le
      _ = C * (1 + t) ^ M₀ * Real.exp (-(Real.pi * (t - 0))) := by rw [sub_zero]; ring
  · have hb := htail τ hτ t (le_of_lt htT)
    refine le_trans hb ?_
    have hCp : C₀ * (1 + t) ^ M₀ ≤ C * (1 + t) ^ M₀ :=
      mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg (by linarith) M₀)
    calc C₀ * (1 + t) ^ M₀ * Real.exp (-(Real.pi * t))
        = (C₀ * (1 + t) ^ M₀) * Real.exp (-(Real.pi * t)) := rfl
      _ ≤ (C * (1 + t) ^ M₀) * Real.exp (-(Real.pi * t)) :=
          mul_le_mul_of_nonneg_right hCp (Real.exp_pos _).le
      _ = C * (1 + t) ^ M₀ * Real.exp (-(Real.pi * (t - 0))) := by rw [sub_zero]

end Work.Asymptotics.HalfFunnel
