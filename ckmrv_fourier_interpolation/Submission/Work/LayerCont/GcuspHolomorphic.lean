import Mathlib
import Submission.Work.LayerCont.CuspExpansionKernelClosure

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane ModularForm ModularGroup MeasureTheory Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

/-- Holomorphy of `psi2` (mirror of the continuity lemma in
`Work.Asymptotics.HalfFunnel.tangTailExpansion`). -/
theorem mdifferentiable_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    MDiff (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) := by
  have hxi2 : MDiff (fun τ : ℍ => Work.Kernels.xi2Fun τ) := by
    have h : (fun τ : ℍ => Work.Kernels.xi2Fun τ) =
        fun τ => Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
    rw [h]
    exact ((Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.pow 4).add
      (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.pow 4))
  have hU : MDiff (fun τ : ℍ => Work.Kernels.UFun τ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.pow 4)
  have hV : MDiff (fun τ : ℍ => Work.Kernels.VFun τ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.pow 4)
  have h : (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) = fun τ : ℍ =>
      Work.Kernels.xi2Fun τ * ℓ.L τ +
        (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi2Fun τ * ℓ.L τ +
      (SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
  rw [h]
  exact (hxi2.mul ℓ.holo).add (((hU.add hV).neg).mul ℓ.holo_S)

/-- Holomorphy of `psi4`. -/
theorem mdifferentiable_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    MDiff (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := by
  have hxi4 : MDiff (fun τ : ℍ => Work.Kernels.xi4Fun τ) := by
    have h : (fun τ : ℍ => Work.Kernels.xi4Fun τ) = fun τ =>
        Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2 := rfl
    rw [h]
    exact (((Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.pow 4).pow 2).add
      ((Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.pow 4).pow 2)).sub
      (((Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.pow 4).pow 2).const_smul (2:ℂ))
  have hU : MDiff (fun τ : ℍ => Work.Kernels.UFun τ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.pow 4)
  have hV : MDiff (fun τ : ℍ => Work.Kernels.VFun τ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.pow 4)
  have hW : MDiff (fun τ : ℍ => Work.Kernels.WFun τ) :=
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.pow 4)
  have h : (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) = fun τ =>
      Work.Kernels.xi4Fun τ * ℓ.L τ +
        (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
          * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi4Fun τ * ℓ.L τ +
      (SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi4S_apply τ]
  rw [h]
  exact (hxi4.mul ℓ.holo).add
    (((hU.pow 2).add (hV.pow 2)).sub ((hW.pow 2).const_smul (2:ℂ)) |>.mul ℓ.holo_S)

/-- Holomorphy of the `d = 8` cusp coefficient functions. -/
theorem mdifferentiable_Gcusp8 (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    MDiff (fun τ : ℍ => Work.Asymptotics.Gcusp8 ℓ i j τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  change DifferentiableOn ℂ
    (fun z : ℂ => Work.Asymptotics.Gcusp8 ℓ i j (UpperHalfPlane.ofComplex z)) {z | 0 < z.im}
  have hphi : ∀ k : Fin 3, DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.phiVec (UpperHalfPlane.ofComplex z) k) {z | 0 < z.im} :=
    fun k => UpperHalfPlane.mdifferentiable_iff.mp (Work.Kernels.KernelGrowth.PhiVec_InP k).1
  have hE4 : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.E4Fun (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularForm.holo' ModularForm.E₄)
  have hE6 : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.E6Fun (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularForm.holo' ModularForm.E₆)
  have hpsi4 : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.psi4 ℓ (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_psi4 ℓ)
  simp only [Work.Asymptotics.Gcusp8]
  split_ifs <;> fun_prop

/-- Holomorphy of the `d = 24` cusp coefficient functions. -/
theorem mdifferentiable_Gcusp24 (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    MDiff (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ i j τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  change DifferentiableOn ℂ
    (fun z : ℂ => Work.Asymptotics.Gcusp24 ℓ i j (UpperHalfPlane.ofComplex z)) {z | 0 < z.im}
  have hphi : ∀ k : Fin 3, DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.phiVec (UpperHalfPlane.ofComplex z) k) {z | 0 < z.im} :=
    fun k => UpperHalfPlane.mdifferentiable_iff.mp (Work.Kernels.KernelGrowth.PhiVec_InP k).1
  have hE4 : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.E4Fun (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularForm.holo' ModularForm.E₄)
  have hE6 : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.E6Fun (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularForm.holo' ModularForm.E₆)
  have hDel : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (CuspForm.holo' CuspForm.discriminant)
  have hpsi2 : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.psi2 ℓ (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_psi2 ℓ)
  have hpsi4 : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.psi4 ℓ (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_psi4 ℓ)
  simp only [Work.Asymptotics.Gcusp24]
  split_ifs <;> fun_prop

/-- Holomorphy of the cusp coefficient functions. -/
theorem mdifferentiable_Gcusp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (_hd : d = 8 ∨ d = 24)
    (i j : Fin 2) : MDiff (fun τ : ℍ => Work.Asymptotics.Gcusp ℓ d i j τ) := by
  by_cases h : d = 8
  · rw [show (fun τ : ℍ => Work.Asymptotics.Gcusp ℓ d i j τ)
        = (fun τ : ℍ => Work.Asymptotics.Gcusp8 ℓ i j τ) from by
      funext τ
      unfold Work.Asymptotics.Gcusp
      rw [if_pos h]]
    exact mdifferentiable_Gcusp8 ℓ i j
  · rw [show (fun τ : ℍ => Work.Asymptotics.Gcusp ℓ d i j τ)
        = (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ i j τ) from by
      funext τ
      unfold Work.Asymptotics.Gcusp
      rw [if_neg h]]
    exact mdifferentiable_Gcusp24 ℓ i j

/-- Holomorphy of the cusp model `Aexp` in the `τ` variable, for fixed `t`. -/
theorem mdifferentiable_Aexp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (t : ℝ) : MDiff (fun τ : ℍ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  change DifferentiableOn ℂ
    (fun z : ℂ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
      (UpperHalfPlane.ofComplex z) t) {z | 0 < z.im}
  have hGc : ∀ i j : Fin 2, DifferentiableOn ℂ
      (fun z : ℂ => Work.Asymptotics.Gcusp ℓ d i j (UpperHalfPlane.ofComplex z))
      {z | 0 < z.im} :=
    fun i j => UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_Gcusp ℓ d hd i j)
  unfold Work.Asymptotics.Aexp
  fun_prop

/-- The `z`-form of the previous lemma: `Aexp (Gcusp ℓ d) (ofComplex z) t` is complex
differentiable in `z`. -/
theorem differentiableAt_Aexp_ofComplex (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (t : ℝ) (τ : ℍ) :
    DifferentiableAt ℂ (fun z : ℂ =>
      Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (UpperHalfPlane.ofComplex z) t) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.mp (mdifferentiable_Aexp ℓ d hd t).mdifferentiableAt

/-- Continuity of `Aexp` in the contour variable `t`, for fixed `τ`. -/
theorem continuous_Aexp_snd (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) : Continuous (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) :=
  (Work.Asymptotics.HalfFunnel.continuous_Aexp_tang ℓ d hd).comp
    (continuous_const.prodMk continuous_id)

/-- Measurability of `Aexp` in the contour variable `t`, for fixed `τ`. -/
theorem measurable_Aexp_snd (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) : Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) :=
  (continuous_Aexp_snd ℓ d hd τ).measurable

end Work.LayerCont
