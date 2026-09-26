/-
# Moderate growth of the coefficient functions `𝒢_{k,j}` of the cusp expansion

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, *Universal optimality of the E8 and Leech
lattices and interpolation formulas*, Ann. of Math. 196 (2022)) expand the kernel
`z ↦ K^{(d)}(τ,z)` at the cusp `z = i∞` and obtain coefficient functions `𝒢_{k,j}` of `τ`
(§4.5).  This file proves that the explicit coefficient functions `Work.Asymptotics.Gcusp ℓ d i j`
of `Work.Asymptotics.Kaxis_local_tail` have moderate growth on `𝒟`
(`Work.Kernels.ModerateGrowthOn DomainD`), which is the hypothesis `hG` of
`Work.Asymptotics.Kaxis_local_tail` and hence of the layer estimates
`Work.Asymptotics.paperLayer_local_seminorm` and friends.

Every atom occurring in `Gcusp` -- `φ_k(τ)` (`Work.Kernels.phiVec`), `E₄`, `E₆`, `Δ`, and
`ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`, `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` -- lies in the class `𝒫` of
`Work.Kernels.InP` (holomorphic of moderate growth on all of `ℍ`), and `cuspL ℓ` is a constant.
Since `𝒫` is closed under `+`, `-`, `*`, scalar multiples and division by constants, each of the
(explicitly written) sums and products defining `Gcusp8` and `Gcusp24` lies in `𝒫`; restricting
the resulting moderate growth from `Set.univ` to `DomainD` gives the claim.
-/
import Mathlib
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Kernels.KernelGrowth.KMinusClear_growth_tau

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-! ## Elementary closure helpers for `𝒫` -/

/-- `𝒫` is closed under multiplication by a constant on the right. -/
private lemma InP_mul_const {F : ℍ → ℂ} (c : ℂ) (h : Work.Kernels.InP F) :
    Work.Kernels.InP (fun τ => F τ * c) := by
  have h' : Work.Kernels.InP (fun τ => c * F τ) := h.const_mul c
  have heq : (fun τ : ℍ => c * F τ) = (fun τ : ℍ => F τ * c) := by
    funext τ; ring
  rwa [heq] at h'

/-- `𝒫` is closed under division by a constant. -/
private lemma InP_div_const {F : ℍ → ℂ} (c : ℂ) (h : Work.Kernels.InP F) :
    Work.Kernels.InP (fun τ => F τ / c) := by
  have h' : Work.Kernels.InP (fun τ => F τ * c⁻¹) := InP_mul_const c⁻¹ h
  simpa [div_eq_mul_inv] using h'

/-! ## The atoms `ξ₂, ξ₄, ψ₂, ψ₄` lie in `𝒫` -/

private lemma InP_xi2 : Work.Kernels.InP Work.Kernels.xi2Fun := by
  have h : Work.Kernels.xi2Fun = fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
  rw [h]
  exact (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.pow 4).add
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.pow 4)

private lemma InP_xi4 : Work.Kernels.InP Work.Kernels.xi4Fun := by
  have h : Work.Kernels.xi4Fun = fun τ : ℍ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 -
      2 * Work.Kernels.VFun τ ^ 2 := rfl
  rw [h]
  exact ((Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.pow 4).pow 2).add
      ((Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.pow 4).pow 2) |>.sub
    (Work.Kernels.InP.const_mul 2 ((Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.pow 4).pow 2))

private lemma InP_psi2 (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.InP (Work.Kernels.psi2 ℓ) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  have h : Work.Kernels.psi2 ℓ = fun τ : ℍ => Work.Kernels.xi2Fun τ * ℓ.L τ +
      (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
  rw [h]
  exact (InP_xi2.mul hL).add ((InP_xi2.slash (2 : ℤ) ModularGroup.S).mul hLS)

private lemma InP_psi4 (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.InP (Work.Kernels.psi4 ℓ) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  have h : Work.Kernels.psi4 ℓ = fun τ : ℍ => Work.Kernels.xi4Fun τ * ℓ.L τ +
      (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
  rw [h]
  exact (InP_xi4.mul hL).add ((InP_xi4.slash (4 : ℤ) ModularGroup.S).mul hLS)

/-! ## The coefficient functions -/

/-- `Gcusp8 ℓ i j ∈ 𝒫`. -/
private lemma InP_Gcusp8 (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Work.Kernels.InP (Work.Asymptotics.Gcusp8 ℓ i j) := by
  by_cases hi : i = 1
  · rw [show Work.Asymptotics.Gcusp8 ℓ i j = fun _ : ℍ => (0 : ℂ) from by
      funext τ; simp only [Work.Asymptotics.Gcusp8, if_pos hi]]
    exact Work.Kernels.InP.zero
  · by_cases hj : j = 0
    · rw [show Work.Asymptotics.Gcusp8 ℓ i j =
        (fun τ : ℍ => (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ * (-Complex.I)
          + Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) / 2) from by
        funext τ; simp only [Work.Asymptotics.Gcusp8, if_neg hi, if_pos hj]]
      have h0 : Work.Kernels.InP (fun τ : ℍ =>
          Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ * (-Complex.I)) :=
        InP_mul_const (-Complex.I) ((Work.Kernels.KernelGrowth.PhiVec_InP 0).mul
          Work.Kernels.ClassicalFacts.E6Fun_mem_InP)
      have h1 : Work.Kernels.InP (fun τ : ℍ =>
          Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) :=
        InP_div_const (Real.pi : ℂ) (InP_mul_const (Work.Asymptotics.cuspL ℓ)
          Work.Kernels.ClassicalFacts.E4Fun_mem_InP)
      have h2 : Work.Kernels.InP (fun τ : ℍ =>
          Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) :=
        InP_div_const (2 * (Real.pi : ℂ)) (InP_psi4 ℓ)
      exact InP_div_const 2 ((h0.add h1).sub h2)
    · rw [show Work.Asymptotics.Gcusp8 ℓ i j =
        (fun τ : ℍ => ((Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
          - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
          + Complex.I * Work.Kernels.E4Fun τ) / 2) from by
        funext τ; simp only [Work.Asymptotics.Gcusp8, if_neg hi, if_neg hj]]
      have h0 : Work.Kernels.InP (fun τ : ℍ =>
          (Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
            - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)) :=
        Work.Kernels.InP.const_mul ((Real.pi : ℂ) / 3)
          (((Work.Kernels.KernelGrowth.PhiVec_InP 0).mul
              Work.Kernels.ClassicalFacts.E6Fun_mem_InP).sub
            ((Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
              Work.Kernels.ClassicalFacts.E4Fun_mem_InP))
      have h1 : Work.Kernels.InP (fun τ : ℍ => Complex.I * Work.Kernels.E4Fun τ) :=
        Work.Kernels.InP.const_mul Complex.I Work.Kernels.ClassicalFacts.E4Fun_mem_InP
      exact InP_div_const 2 (h0.add h1)

/-- `Gcusp24 ℓ i j ∈ 𝒫`: the four branches of the explicit formula are sums and products of
atoms of `𝒫`. -/
private lemma InP_Gcusp24 (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Work.Kernels.InP (Work.Asymptotics.Gcusp24 ℓ i j) := by
  have key : Work.Kernels.InP (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ i j τ) := by
    by_cases h00 : i = 0 ∧ j = 0
    · -- branch `(0,0)`
      simp only [Work.Asymptotics.Gcusp24, if_pos h00]
      refine InP_div_const 2 ?_
      have h0 : Work.Kernels.InP (fun τ : ℍ =>
          -(13 * Complex.I / 12) * (Work.Kernels.phiVec τ 0 *
            (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))) :=
        Work.Kernels.InP.const_mul (-(13 * Complex.I / 12))
          ((Work.Kernels.KernelGrowth.PhiVec_InP 0).mul
            (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2 |>.mul
              Work.Kernels.ClassicalFacts.E6Fun_mem_InP))
      have h1 : Work.Kernels.InP (fun τ : ℍ =>
          Complex.I / 6 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) :=
        Work.Kernels.InP.const_mul (Complex.I / 6)
          ((Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
            (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3))
      have h2 : Work.Kernels.InP (fun τ : ℍ =>
          168 * Complex.I * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)) :=
        Work.Kernels.InP.const_mul (168 * Complex.I)
          ((Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
            Work.Kernels.ClassicalFacts.DeltaFun_mem_InP)
      have h3 : Work.Kernels.InP (fun τ : ℍ =>
          Complex.I / 12 * (Work.Kernels.phiVec τ 2 *
            (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) :=
        Work.Kernels.InP.const_mul (Complex.I / 12)
          ((Work.Kernels.KernelGrowth.PhiVec_InP 2).mul
            (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.mul
              Work.Kernels.ClassicalFacts.E6Fun_mem_InP))
      have h4 : Work.Kernels.InP (fun τ : ℍ =>
          720 * Work.Kernels.DeltaFun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) :=
        InP_div_const (Real.pi : ℂ) (InP_mul_const (Work.Asymptotics.cuspL ℓ)
          (Work.Kernels.InP.const_mul 720 Work.Kernels.ClassicalFacts.DeltaFun_mem_InP))
      have h5 : Work.Kernels.InP (fun τ : ℍ =>
          36 * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)) :=
        InP_div_const (Real.pi : ℂ)
          (Work.Kernels.InP.const_mul 36 Work.Kernels.ClassicalFacts.DeltaFun_mem_InP)
      have h6 : Work.Kernels.InP (fun τ : ℍ =>
          Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) :=
        InP_div_const (Real.pi : ℂ) (InP_mul_const (Work.Asymptotics.cuspL ℓ)
          (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3))
      have h7 : Work.Kernels.InP (fun τ : ℍ =>
          7 * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)) /
            (24 * (Real.pi : ℂ))) :=
        InP_div_const (24 * (Real.pi : ℂ)) (Work.Kernels.InP.const_mul 7
          ((InP_psi2 ℓ).mul (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.mul
            Work.Kernels.ClassicalFacts.E6Fun_mem_InP)))
      have h8 : Work.Kernels.InP (fun τ : ℍ =>
          5 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2) / (24 * (Real.pi : ℂ))) :=
        InP_div_const (24 * (Real.pi : ℂ)) (Work.Kernels.InP.const_mul 5
          ((InP_psi4 ℓ).mul (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2)))
      refine Work.Kernels.InP.sub ?_ h8
      refine Work.Kernels.InP.sub ?_ h7
      refine Work.Kernels.InP.add ?_ h6
      refine Work.Kernels.InP.sub ?_ h5
      refine Work.Kernels.InP.sub ?_ h4
      refine Work.Kernels.InP.sub ?_ h3
      refine Work.Kernels.InP.sub ?_ h2
      exact Work.Kernels.InP.add h0 h1
    · by_cases h01 : i = 0 ∧ j = 1
      · -- branch `(0,1)`
        simp only [Work.Asymptotics.Gcusp24, if_neg h00, if_pos h01]
        refine InP_div_const 2 ?_
        have hX : Work.Kernels.InP (fun τ : ℍ =>
            Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)) :=
          (Work.Kernels.KernelGrowth.PhiVec_InP 0).mul
            (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2 |>.mul
              Work.Kernels.ClassicalFacts.E6Fun_mem_InP)
        have hY : Work.Kernels.InP (fun τ : ℍ =>
            720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)) :=
          Work.Kernels.InP.const_mul 720 ((Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
            Work.Kernels.ClassicalFacts.DeltaFun_mem_InP)
        have hZ : Work.Kernels.InP (fun τ : ℍ =>
            Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3) :=
          (Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
            (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3)
        have hA : Work.Kernels.InP (fun τ : ℍ =>
            (Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 *
                (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
              + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
              - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) :=
          Work.Kernels.InP.const_mul ((Real.pi : ℂ) / 3) ((hX.add hY).sub hZ)
        have hB : Work.Kernels.InP (fun τ : ℍ =>
            Complex.I * (720 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)) :=
          Work.Kernels.InP.const_mul Complex.I
            ((Work.Kernels.InP.const_mul 720 Work.Kernels.ClassicalFacts.DeltaFun_mem_InP).sub
              (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3))
        exact hA.sub hB
      · by_cases h10 : i = 1 ∧ j = 0
        · -- branch `(1,0)`
          simp only [Work.Asymptotics.Gcusp24, if_neg h00, if_neg h01, if_pos h10]
          refine InP_div_const 2 ?_
          have hX : Work.Kernels.InP (fun τ : ℍ =>
              Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)) :=
            (Work.Kernels.KernelGrowth.PhiVec_InP 0).mul
              (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2 |>.mul
                Work.Kernels.ClassicalFacts.E6Fun_mem_InP)
          have hW : Work.Kernels.InP (fun τ : ℍ =>
              Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)) :=
            (Work.Kernels.KernelGrowth.PhiVec_InP 2).mul
              (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.mul
                Work.Kernels.ClassicalFacts.E6Fun_mem_InP)
          have h0 : Work.Kernels.InP (fun τ : ℍ =>
              -(Complex.I / 288) * (Work.Kernels.phiVec τ 0 *
                  (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
                + Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) :=
            Work.Kernels.InP.const_mul (-(Complex.I / 288)) (hX.add hW)
          have h1 : Work.Kernels.InP (fun τ : ℍ =>
              Complex.I / 144 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) :=
            Work.Kernels.InP.const_mul (Complex.I / 144)
              ((Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
                (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3))
          have h2 : Work.Kernels.InP (fun τ : ℍ =>
              7 * Complex.I * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)) :=
            Work.Kernels.InP.const_mul (7 * Complex.I)
              ((Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
                Work.Kernels.ClassicalFacts.DeltaFun_mem_InP)
          have h3 : Work.Kernels.InP (fun τ : ℍ =>
              Work.Kernels.DeltaFun τ * (Work.Asymptotics.cuspL ℓ - 1) / (Real.pi : ℂ)) :=
            InP_div_const (Real.pi : ℂ) (InP_mul_const (Work.Asymptotics.cuspL ℓ - 1)
              Work.Kernels.ClassicalFacts.DeltaFun_mem_InP)
          have h4 : Work.Kernels.InP (fun τ : ℍ =>
              (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
                - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2) /
                  (1152 * (Real.pi : ℂ))) :=
            InP_div_const (1152 * (Real.pi : ℂ))
              (((InP_psi2 ℓ).mul (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.mul
                  Work.Kernels.ClassicalFacts.E6Fun_mem_InP)).sub
                ((InP_psi4 ℓ).mul (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2)))
          refine Work.Kernels.InP.add ?_ h4
          refine Work.Kernels.InP.add ?_ h3
          refine Work.Kernels.InP.sub ?_ h2
          exact Work.Kernels.InP.add h0 h1
        · -- branch `(1,1)`
          simp only [Work.Asymptotics.Gcusp24, if_neg h00, if_neg h01, if_neg h10]
          refine InP_div_const 2 ?_
          have hX : Work.Kernels.InP (fun τ : ℍ =>
              Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)) :=
            (Work.Kernels.KernelGrowth.PhiVec_InP 0).mul
              (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2 |>.mul
                Work.Kernels.ClassicalFacts.E6Fun_mem_InP)
          have hW : Work.Kernels.InP (fun τ : ℍ =>
              Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)) :=
            (Work.Kernels.KernelGrowth.PhiVec_InP 2).mul
              (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.mul
                Work.Kernels.ClassicalFacts.E6Fun_mem_InP)
          have hY : Work.Kernels.InP (fun τ : ℍ =>
              1728 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)) :=
            Work.Kernels.InP.const_mul 1728 ((Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
              Work.Kernels.ClassicalFacts.DeltaFun_mem_InP)
          have hZ : Work.Kernels.InP (fun τ : ℍ =>
              2 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) :=
            Work.Kernels.InP.const_mul 2 ((Work.Kernels.KernelGrowth.PhiVec_InP 1).mul
              (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3))
          have hA : Work.Kernels.InP (fun τ : ℍ =>
              (Real.pi : ℂ) / 864 * (Work.Kernels.phiVec τ 0 *
                  (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
                + Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
                + 1728 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
                - 2 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3))) :=
            Work.Kernels.InP.const_mul ((Real.pi : ℂ) / 864) (((hX.add hW).add hY).sub hZ)
          have hB : Work.Kernels.InP (fun τ : ℍ => Complex.I * Work.Kernels.DeltaFun τ) :=
            Work.Kernels.InP.const_mul Complex.I Work.Kernels.ClassicalFacts.DeltaFun_mem_InP
          exact hA.add hB
  exact key

/-- **Moderate growth of the coefficient functions of the cusp expansion.**  Each of
`Gcusp ℓ d i j` (which is `Gcusp8` for `d = 8` and `Gcusp24` otherwise) is a sum of products of
the atoms `φ_k, E₄, E₆, Δ, ψ₂, ψ₄` and the constant `cuspL ℓ`, all of which lie in the class
`𝒫` of `Work.Kernels.InP`; hence it is of moderate growth, in particular on `𝒟`. -/
theorem GcuspInP (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (i j : Fin 2) :
    Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (Work.Asymptotics.Gcusp ℓ d i j) := by
  rcases eq_or_ne d 8 with hd | hd
  · rw [show Work.Asymptotics.Gcusp ℓ d = Work.Asymptotics.Gcusp8 ℓ from by
      rw [Work.Asymptotics.Gcusp]; exact if_pos hd]
    exact (InP_Gcusp8 ℓ i j).2.mono (Set.subset_univ _)
  · rw [show Work.Asymptotics.Gcusp ℓ d = Work.Asymptotics.Gcusp24 ℓ from by
      rw [Work.Asymptotics.Gcusp]; exact if_neg hd]
    exact (InP_Gcusp24 ℓ i j).2.mono (Set.subset_univ _)

end

end Work.Asymptotics
