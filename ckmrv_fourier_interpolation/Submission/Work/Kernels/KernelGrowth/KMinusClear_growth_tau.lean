/-
# Growth of the cleared kernel `K_-^{(d)}` in the first variable

Theorem 4.9(4) of CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022))
says that `Δ(τ)Δ(z)^e (j(τ) - j(z)) K_-^{(d)}(τ,z)` lies in the class `𝒫` for `d = 8, 24`.
This file proves the statement in the *first* variable `τ`, with `z` fixed: the function
`τ ↦ KMinusClear ℓ d τ z` is holomorphic on `ℍ` and of moderate growth.

The proof is an entry-by-entry computation.  Writing

  `Υ_-^{clear,(8)}(τ,z) = c₈ • (Π_Δ(τ) · B₈(τ) · Π(z))`,  `B₈(τ) = !![…]`,
  `Υ_-^{clear,(24)}(τ,z) = c₂₄ • (Π_Δ(τ) · B₂₄(τ,z) · (Δ(z) • Π(z)))`,

with `Π_Δ(τ) = diag(Δ(τ) f_k(τ))` diagonal, every entry of `Υ_-^{clear}` has the shape

  `c · (Δ τ · f_k(τ) · A(τ)) · (constant in τ)`,

where `A(τ)` is the corresponding entry of `B₈`/`B₂₄`, an affine function of `j(τ)` whose
coefficients depend only on `z`.  Since `Δ·j = E₄³`, the products `(Δ f_k)·j` are again
holomorphic of moderate growth for the weights `k ∈ {0, 8, 10, 12}` that occur, and the
statement follows from the closure of `𝒫` under sums, products and scalar multiples.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E4Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E6Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta00Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta01Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta10Fun_mem_InP

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelGrowth

/-! ## Preliminaries: `𝒫` is a pointwise notion -/

private lemma InP_congr {F G : ℍ → ℂ} (h : ∀ τ, F τ = G τ)
    (hG : Work.Kernels.InP G) : Work.Kernels.InP F := by
  refine ⟨fun τ => (hG.1 τ).congr_of_eventuallyEq (Filter.Eventually.of_forall h), ?_⟩
  obtain ⟨α, β, γ, hα, hβ, hγ, hb⟩ := hG.2
  exact ⟨α, β, γ, hα, hβ, hγ, fun τ hτ => by rw [h τ]; exact hb τ hτ⟩

/-! ## The classical modular forms lie in `𝒫` -/

private lemma E4InP : Work.Kernels.InP Work.Kernels.E4Fun :=
  Work.Kernels.ClassicalFacts.E4Fun_mem_InP

private lemma E6InP : Work.Kernels.InP Work.Kernels.E6Fun :=
  Work.Kernels.ClassicalFacts.E6Fun_mem_InP

private lemma DeltaInP : Work.Kernels.InP Work.Kernels.DeltaFun :=
  Work.Kernels.ClassicalFacts.DeltaFun_mem_InP

private lemma E8InP : Work.Kernels.InP Work.Kernels.E8Fun :=
  Work.Kernels.InP.pow E4InP 2

private lemma E10InP : Work.Kernels.InP Work.Kernels.E10Fun :=
  Work.Kernels.InP.mul E4InP E6InP

private lemma E14InP : Work.Kernels.InP Work.Kernels.E14Fun :=
  (Work.Kernels.InP.pow E4InP 2).mul E6InP

/-! ## The products `Δ · f_k` and `Δ · f_k · j` -/

private lemma Dfk0_InP : Work.Kernels.InP (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 0 τ) := by
  have h : (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 0 τ) = Work.Kernels.DeltaFun := by
    funext τ
    rw [show Work.Kernels.fk 0 τ = (1 : ℂ) by simp only [Work.Kernels.fk]; norm_num]
    exact mul_one _
  rw [h]; exact DeltaInP

private lemma Dfk2_InP : Work.Kernels.InP (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 2 τ) := by
  have h : (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 2 τ) = Work.Kernels.E14Fun := by
    funext τ
    rw [show Work.Kernels.fk 2 τ = Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ by
      simp only [Work.Kernels.fk]; norm_num]
    rw [mul_div_cancel₀ _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)]
  rw [h]; exact E14InP

private lemma Dfk4_InP :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 4 τ) := by
  have h : (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 4 τ)
      = fun τ => Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ := by
    funext τ
    rw [show Work.Kernels.fk 4 τ = Work.Kernels.E4Fun τ by simp only [Work.Kernels.fk]; norm_num]
  rw [h]; exact DeltaInP.mul E4InP

private lemma Dfk8_InP :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 8 τ) := by
  have h : (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 8 τ)
      = fun τ => Work.Kernels.DeltaFun τ * Work.Kernels.E8Fun τ := by
    funext τ
    rw [show Work.Kernels.fk 8 τ = Work.Kernels.E8Fun τ by simp only [Work.Kernels.fk]; norm_num]
  rw [h]; exact DeltaInP.mul E8InP

private lemma Dfk10_InP :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 10 τ) := by
  have h : (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 10 τ)
      = fun τ => Work.Kernels.DeltaFun τ * Work.Kernels.E10Fun τ := by
    funext τ
    rw [show Work.Kernels.fk 10 τ = Work.Kernels.E10Fun τ by simp only [Work.Kernels.fk]; norm_num]
  rw [h]; exact DeltaInP.mul E10InP

private lemma Dfk12_InP :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 12 τ) := by
  have h : (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk 12 τ)
      = fun τ => Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ := by
    funext τ
    rw [show Work.Kernels.fk 12 τ = Work.Kernels.DeltaFun τ by
      simp only [Work.Kernels.fk]; norm_num]
  rw [h]; exact DeltaInP.mul DeltaInP

private lemma Dfj0_InP :
    Work.Kernels.InP (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 0 τ) *
      Work.Kernels.jInvariantFun τ) := by
  have h : (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 0 τ) *
        Work.Kernels.jInvariantFun τ) = fun τ => Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    rw [show Work.Kernels.fk 0 τ = (1 : ℂ) by simp only [Work.Kernels.fk]; norm_num, mul_one,
      Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  rw [h]; exact Work.Kernels.InP.pow E4InP 3

private lemma Dfj8_InP :
    Work.Kernels.InP (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 8 τ) *
      Work.Kernels.jInvariantFun τ) := by
  have h : (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 8 τ) *
        Work.Kernels.jInvariantFun τ) = fun τ => Work.Kernels.E8Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    rw [show Work.Kernels.fk 8 τ = Work.Kernels.E8Fun τ by simp only [Work.Kernels.fk]; norm_num]
    rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]; exact E8InP.mul (Work.Kernels.InP.pow E4InP 3)

private lemma Dfj10_InP :
    Work.Kernels.InP (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 10 τ) *
      Work.Kernels.jInvariantFun τ) := by
  have h : (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 10 τ) *
        Work.Kernels.jInvariantFun τ) = fun τ => Work.Kernels.E10Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    rw [show Work.Kernels.fk 10 τ = Work.Kernels.E10Fun τ by simp only [Work.Kernels.fk]; norm_num]
    rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]; exact E10InP.mul (Work.Kernels.InP.pow E4InP 3)

private lemma Dfj12_InP :
    Work.Kernels.InP (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 12 τ) *
      Work.Kernels.jInvariantFun τ) := by
  have h : (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 12 τ) *
        Work.Kernels.jInvariantFun τ) =
      fun τ => Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    rw [show Work.Kernels.fk 12 τ = Work.Kernels.DeltaFun τ by
      simp only [Work.Kernels.fk]; norm_num]
    rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]; exact DeltaInP.mul (Work.Kernels.InP.pow E4InP 3)

/-- `(Δ f_k) · (α j + β)` lies in `𝒫` whenever `(Δ f_k)` and `(Δ f_k) · j` do. -/
private lemma Dfk_affine_InP {k : ℤ}
    (h1 : Work.Kernels.InP (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.fk k τ))
    (h2 : Work.Kernels.InP (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk k τ) *
      Work.Kernels.jInvariantFun τ))
    (α β : ℂ) :
    Work.Kernels.InP (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk k τ) *
      (α * Work.Kernels.jInvariantFun τ + β)) := by
  have heq : (fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk k τ) *
        (α * Work.Kernels.jInvariantFun τ + β))
      = fun τ => α * ((Work.Kernels.DeltaFun τ * Work.Kernels.fk k τ) *
            Work.Kernels.jInvariantFun τ) + β * (Work.Kernels.DeltaFun τ * Work.Kernels.fk k τ) := by
    funext τ; ring
  rw [heq]
  exact (Work.Kernels.InP.const_mul α h2).add (Work.Kernels.InP.const_mul β h1)

/-! ## The `B` matrices and the entry formulas for `Υ_-^{clear}` -/

/-- The `d = 8` matrix `B₈` of the cleared kernel, so that
`Υ_-^{clear,(8)}(τ,z) = c₈ • (Π_Δ(τ) · B₈(τ) · Π(z))`. -/
private def B8 (τ : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-2 : ℂ) * Work.Kernels.c1728, 0, 0; 0, 1, -1;
     0, Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ, Work.Kernels.jInvariantFun τ]

/-- The `d = 24` matrix `B₂₄` of the cleared kernel, so that
`Υ_-^{clear,(24)}(τ,z) = c₂₄ • (Π_Δ(τ) · B₂₄(τ,z) · (Δ(z) • Π(z)))`. -/
private def B24 (τ z : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-2 : ℂ) * Work.Kernels.c1728,
      (-2 : ℂ) * Work.Kernels.c1728 *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), 0;
      0, Work.Kernels.jInvariantFun τ +
        2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), -1;
      0, Work.Kernels.c1728 -
        2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) -
        Work.Kernels.jInvariantFun τ, 1]

private lemma smul_diagonal_aux {c : ℂ} {g : Fin 3 → ℂ} :
    c • Matrix.diagonal g = Matrix.diagonal (fun j => c * g j) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private lemma umc8_eq (τ z : ℍ) :
    Work.Kernels.UpsilonMinusClear 8 τ z =
      (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) •
        (Work.Kernels.PiMatDelta ![4,2,0] τ * B8 τ * Work.Kernels.PiMat ![10,8,6] z) := by
  simp only [Work.Kernels.UpsilonMinusClear]
  rw [if_pos trivial]
  rfl

private lemma umc24_eq (τ z : ℍ) :
    Work.Kernels.UpsilonMinusClear 24 τ z =
      (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) •
        (Work.Kernels.PiMatDelta ![12,10,8] τ * B24 τ z *
          (Work.Kernels.DeltaFun z • Work.Kernels.PiMat ![2,0,-2] z)) := by
  simp only [Work.Kernels.UpsilonMinusClear]
  rw [if_neg (by norm_num : ¬ ((24 : ℕ) = 8)), if_pos trivial]
  rfl

private lemma umc8_apply (τ z : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear 8 τ z i j =
      (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) *
        ((Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4,2,0] i) τ) * B8 τ i j *
          Work.Kernels.fk (![10,8,6] j) z) := by
  rw [umc8_eq]
  simp only [Matrix.smul_apply, Work.Kernels.PiMatDelta, Work.Kernels.PiMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private lemma umc24_apply (τ z : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear 24 τ z i j =
      (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) *
        ((Work.Kernels.DeltaFun τ * Work.Kernels.fk (![12,10,8] i) τ) * B24 τ z i j *
          (Work.Kernels.DeltaFun z * Work.Kernels.fk (![2,0,-2] j) z)) := by
  rw [umc24_eq]
  simp only [Matrix.smul_apply, Work.Kernels.PiMatDelta, Work.Kernels.PiMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, smul_diagonal_aux]
  ring

/-! ## The entries of `B₈` and `B₂₄`, multiplied by `Δ f_k` -/

private lemma B8_entry_InP (_z : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun τ : ℍ =>
      (Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4,2,0] i) τ) * B8 τ i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [B8, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact Dfk4_InP.mul (Work.Kernels.InP.const (-2 * Work.Kernels.c1728))
  · exact Dfk4_InP.mul (Work.Kernels.InP.const 0)
  · exact Dfk4_InP.mul (Work.Kernels.InP.const 0)
  · exact Dfk2_InP.mul (Work.Kernels.InP.const 0)
  · exact Dfk2_InP.mul (Work.Kernels.InP.const 1)
  · exact Dfk2_InP.mul (Work.Kernels.InP.const (-1))
  · exact Dfk0_InP.mul (Work.Kernels.InP.const 0)
  · refine InP_congr (G := fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 0 τ) *
      ((-1 : ℂ) * Work.Kernels.jInvariantFun τ + Work.Kernels.c1728)) (fun τ => by ring) ?_
    exact Dfk_affine_InP Dfk0_InP Dfj0_InP (-1) Work.Kernels.c1728
  · exact Dfj0_InP

private lemma B24_entry_InP (z : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun τ : ℍ =>
      (Work.Kernels.DeltaFun τ * Work.Kernels.fk (![12,10,8] i) τ) * B24 τ z i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [B24, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact Dfk12_InP.mul (Work.Kernels.InP.const (-2 * Work.Kernels.c1728))
  · refine InP_congr (G := fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 12 τ) *
      ((-2 * Work.Kernels.c1728) * Work.Kernels.jInvariantFun τ +
        (2 * Work.Kernels.c1728) * Work.Kernels.jInvariantFun z)) (fun τ => by ring) ?_
    exact Dfk_affine_InP Dfk12_InP Dfj12_InP (-2 * Work.Kernels.c1728)
      (2 * Work.Kernels.c1728 * Work.Kernels.jInvariantFun z)
  · exact Dfk12_InP.mul (Work.Kernels.InP.const 0)
  · exact Dfk10_InP.mul (Work.Kernels.InP.const 0)
  · refine InP_congr (G := fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 10 τ) *
      (3 * Work.Kernels.jInvariantFun τ + (-2 * Work.Kernels.jInvariantFun z)))
      (fun τ => by ring) ?_
    exact Dfk_affine_InP Dfk10_InP Dfj10_InP 3 (-2 * Work.Kernels.jInvariantFun z)
  · exact Dfk10_InP.mul (Work.Kernels.InP.const (-1))
  · exact Dfk8_InP.mul (Work.Kernels.InP.const 0)
  · refine InP_congr (G := fun τ : ℍ => (Work.Kernels.DeltaFun τ * Work.Kernels.fk 8 τ) *
      ((-3 : ℂ) * Work.Kernels.jInvariantFun τ +
        (Work.Kernels.c1728 + 2 * Work.Kernels.jInvariantFun z))) (fun τ => by ring) ?_
    exact Dfk_affine_InP Dfk8_InP Dfj8_InP (-3)
      (Work.Kernels.c1728 + 2 * Work.Kernels.jInvariantFun z)
  · exact Dfk8_InP.mul (Work.Kernels.InP.const 1)

/-! ## Membership of the entries of `Υ_-^{clear}` in `𝒫`, in the variable `τ` -/

private lemma UpsilonMinusClear8_entry_InP (z : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z i j) := by
  have hmain := B8_entry_InP z i j
  have heq : (fun τ : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z i j)
      = fun τ => ((((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) *
          Work.Kernels.fk (![10,8,6] j) z) *
          ((Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4,2,0] i) τ) * B8 τ i j) := by
    funext τ
    rw [umc8_apply]
    ring
  rw [heq]
  exact Work.Kernels.InP.const_mul _ hmain

private lemma UpsilonMinusClear24_entry_InP (z : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z i j) := by
  have hmain := B24_entry_InP z i j
  have heq : (fun τ : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z i j)
      = fun τ => ((((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) *
          (Work.Kernels.DeltaFun z * Work.Kernels.fk (![2,0,-2] j) z)) *
          ((Work.Kernels.DeltaFun τ * Work.Kernels.fk (![12,10,8] i) τ) * B24 τ z i j) := by
    funext τ
    rw [umc24_apply]
    ring
  rw [heq]
  exact Work.Kernels.InP.const_mul _ hmain

/-! ## The vector `ψ⃗` -/

private lemma xi2_InP : Work.Kernels.InP Work.Kernels.xi2Fun := by
  have h : Work.Kernels.xi2Fun
      = fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
  rw [h]
  exact (Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta00Fun_mem_InP 4).add
    (Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta01Fun_mem_InP 4)

private lemma xi4_InP : Work.Kernels.InP Work.Kernels.xi4Fun := by
  have h : Work.Kernels.xi4Fun
      = fun τ : ℍ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 -
          2 * Work.Kernels.VFun τ ^ 2 := rfl
  rw [h]
  exact ((Work.Kernels.InP.pow (Work.Kernels.InP.pow
        Work.Kernels.ClassicalFacts.theta00Fun_mem_InP 4) 2).add
      (Work.Kernels.InP.pow (Work.Kernels.InP.pow
        Work.Kernels.ClassicalFacts.theta01Fun_mem_InP 4) 2)).sub
    (Work.Kernels.InP.const_mul 2 (Work.Kernels.InP.pow (Work.Kernels.InP.pow
      Work.Kernels.ClassicalFacts.theta10Fun_mem_InP 4) 2))

private lemma psi2_InP (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.InP (Work.Kernels.psi2 ℓ) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  have h : Work.Kernels.psi2 ℓ = fun τ : ℍ => Work.Kernels.xi2Fun τ * ℓ.L τ +
      (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
  rw [h]
  exact (xi2_InP.mul hL).add ((xi2_InP.slash (2 : ℤ) ModularGroup.S).mul hLS)

private lemma psi4_InP (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.InP (Work.Kernels.psi4 ℓ) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  have h : Work.Kernels.psi4 ℓ = fun τ : ℍ => Work.Kernels.xi4Fun τ * ℓ.L τ +
      (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
  rw [h]
  exact (xi4_InP.mul hL).add ((xi4_InP.slash (4 : ℤ) ModularGroup.S).mul hLS)

private lemma psiVec_InP (ℓ : Work.Kernels.LogLambdaData) (i : Fin 3) :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.psiVec ℓ τ i) := by
  fin_cases i
  · simpa [Work.Kernels.psiVec] using (Work.Kernels.InP.one : Work.Kernels.InP (fun _ : ℍ => (1 : ℂ)))
  · simpa [Work.Kernels.psiVec] using psi2_InP ℓ
  · simpa [Work.Kernels.psiVec] using psi4_InP ℓ

/-! ## Assembly -/

/-- Closure of `𝒫` under finite sums, in the `fun τ => ∑ …` form. -/
private lemma InP_sum_fun {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, Work.Kernels.InP (F i)) :
    Work.Kernels.InP (fun τ => ∑ i ∈ s, F i τ) := by
  have hsum := Work.Kernels.InP.sum s h
  have heq : (∑ i ∈ s, F i) = fun τ => ∑ i ∈ s, F i τ := by
    funext τ; rw [Finset.sum_apply]
  rwa [heq] at hsum

theorem KMinusClear_growth_tau (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) :
    Work.Kernels.InP (fun τ : UpperHalfPlane => Work.Kernels.KMinusClear ℓ d τ z) := by
  have hPsi : ∀ i : Fin 3, Work.Kernels.InP (fun τ : ℍ => Work.Kernels.psiVec ℓ τ i) :=
    psiVec_InP ℓ
  have hU : ∀ i j : Fin 3,
      Work.Kernels.InP (fun τ : ℍ => Work.Kernels.UpsilonMinusClear d τ z i j) := by
    rcases hd with rfl | rfl
    · exact fun i j => UpsilonMinusClear8_entry_InP z i j
    · exact fun i j => UpsilonMinusClear24_entry_InP z i j
  have hsum : Work.Kernels.InP (fun τ : ℍ => ∑ i : Fin 3, ∑ j : Fin 3,
      Work.Kernels.psiVec ℓ τ i * Work.Kernels.UpsilonMinusClear d τ z i j *
        Work.Kernels.psitVec ℓ z j) := by
    apply InP_sum_fun
    intro i _
    apply InP_sum_fun
    intro j _
    exact ((hPsi i).mul (hU i j)).mul (Work.Kernels.InP.const (Work.Kernels.psitVec ℓ z j))
  have heq : (fun τ : ℍ => Work.Kernels.KMinusClear ℓ d τ z) = fun τ => ∑ i : Fin 3, ∑ j : Fin 3,
      Work.Kernels.psiVec ℓ τ i * Work.Kernels.UpsilonMinusClear d τ z i j *
        Work.Kernels.psitVec ℓ z j := by
    funext τ; rfl
  rwa [heq]

end Work.Kernels.KernelGrowth
