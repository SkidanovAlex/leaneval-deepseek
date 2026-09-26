/-
# Two-variable moderate growth of the cleared CKMRV kernels

Theorem 4.9(4) of Cohn--Kumar--Miller--Radchenko--Viazovska asserts that the cleared kernels
`Δ(τ)Δ(z)^e(j(τ)-j(z))K^{(d)}_±(τ,z)` are of moderate growth in each variable.  For the
contour integral of `Work.Asymptotics` the required statement is the *uniform* two-variable
version:  `‖F τ z‖ ≤ α (scale τ)^N (scale z)^M` with constants independent of `τ` and `z`
(`Work.Asymptotics.ModerateGrowth2`).

Every entry of the cleared coefficient matrices is a finite sum of products `f(τ) g(z)` where
both factors lie in the class `𝒫` of holomorphic functions of moderate growth.  The τ-factors
are `Δ(τ) f_k(τ) j(τ)^a`, with the polar part of `j` cleared by `Δ·j = E₄³`; the z-factors are
`f_k(z) j(z)^b` or `Δ(z) f_k(z) j(z)^b`, cleared in the same way.  The kernels are bilinear in
the basis vectors `φ⃗, φ̃⃗` and `ψ⃗, ψ̃⃗`, whose coordinates all lie in `𝒫`.

This file carries out that computation entry by entry and assembles the result.
-/
import Mathlib
import Submission.Work.Asymptotics.ModerateGrowth2
import Submission.Work.Kernels.All

noncomputable section

set_option linter.unusedSimpArgs false

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

/-! ## Two-variable calculus of `ModerateGrowth2` -/

/-- A product of a `𝒫`-function of `τ` with a `𝒫`-function of `z` has two-variable moderate
growth with constants independent of both variables. -/
private lemma MG2_prod {f g : ℍ → ℂ} (hf : Work.Kernels.InP f) (hg : Work.Kernels.InP g) :
    ModerateGrowth2 (fun τ z : ℍ => f τ * g z) :=
  (ModerateGrowth2.of_fst_InP hf).mul (ModerateGrowth2.of_snd_InP hg)

/-- `ModerateGrowth2` is closed under finite sums. -/
private lemma MG2_sum_fun {ι : Type*} (s : Finset ι) {g : ι → ℍ → ℍ → ℂ}
    (h : ∀ i ∈ s, ModerateGrowth2 (g i)) :
    ModerateGrowth2 (fun τ z => ∑ i ∈ s, g i τ z) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (ModerateGrowth2.zero : ModerateGrowth2 (fun _ _ : ℍ => (0 : ℂ)))
  | insert i s hi ih =>
      have hsplit : (fun τ z => ∑ x ∈ insert i s, g x τ z)
          = fun τ z => g i τ z + ∑ x ∈ s, g x τ z := by
        funext τ z; rw [Finset.sum_insert hi]
      rw [hsplit]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-! ## The one-variable factors and their membership in `𝒫`

The τ-factor `TF k a = Δ · f_k · j^a`, the z-factor `ZF k b = f_k · j^b` and the z-factor
`DF k b = Δ · f_k · j^b`.  The pairs `(k,a)` and `(k,b)` which occur below are exactly those for
which these functions lie in `𝒫`: the power of `j` never exceeds the number of available `Δ`'s.
-/

/-- `Δ(τ) f_k(τ) j(τ)^a`, a τ-factor of the cleared coefficient matrix. -/
private def TF (k : ℤ) (a : ℕ) : ℍ → ℂ :=
  fun τ => Work.Kernels.DeltaFun τ * Work.Kernels.fk k τ * Work.Kernels.jInvariantFun τ ^ a

/-- `f_k(z) j(z)^b`, a z-factor of the cleared matrix `Υ_+^{(8)}`. -/
private def ZF (k : ℤ) (b : ℕ) : ℍ → ℂ :=
  fun z => Work.Kernels.fk k z * Work.Kernels.jInvariantFun z ^ b

/-- `Δ(z) f_k(z) j(z)^b`, a z-factor of the cleared matrices `Υ_±^{(24)}`. -/
private def DF (k : ℤ) (b : ℕ) : ℍ → ℂ :=
  fun z => Work.Kernels.DeltaFun z * Work.Kernels.fk k z * Work.Kernels.jInvariantFun z ^ b

/-- `(36 π^{-2} i)^{-1}`. -/
private def cc8 : ℂ := ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- `(36 · 1728 · π^{-2} i)^{-1}`. -/
private def c24 : ℂ := ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- `(2 · 1728 · π)^{-1}`. -/
private def cm : ℂ := ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹

/-! ### The classical forms -/

private lemma E4InP : Work.Kernels.InP Work.Kernels.E4Fun :=
  Work.Kernels.ClassicalFacts.E4Fun_mem_InP

private lemma E6InP : Work.Kernels.InP Work.Kernels.E6Fun :=
  Work.Kernels.ClassicalFacts.E6Fun_mem_InP

private lemma DeltaInP : Work.Kernels.InP Work.Kernels.DeltaFun :=
  Work.Kernels.ClassicalFacts.DeltaFun_mem_InP

private lemma E10InP : Work.Kernels.InP Work.Kernels.E10Fun := by
  have h : Work.Kernels.E10Fun = fun τ : ℍ => Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ := rfl
  rw [h]; exact E4InP.mul E6InP

private lemma E14InP : Work.Kernels.InP Work.Kernels.E14Fun := by
  have h : Work.Kernels.E14Fun = fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ := rfl
  rw [h]; exact (E4InP.pow 2).mul E6InP

private lemma E8InP : Work.Kernels.InP Work.Kernels.E8Fun := by
  have h : Work.Kernels.E8Fun = fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2 := rfl
  rw [h]; exact E4InP.pow 2

/-! ### Membership of the occurring factors in `𝒫` -/

private lemma TF_6_0 : Work.Kernels.InP (TF 6 0) := by
  have h : TF 6 0 = fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ := by
    funext τ
    simp only [TF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (6) τ = Work.Kernels.E6Fun τ by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP.mul E6InP

private lemma TF_6_1 : Work.Kernels.InP (TF 6 1) := by
  have h : TF 6 1 = fun τ : ℍ => Work.Kernels.E6Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    simp only [TF, pow_one]
    rw [show Work.Kernels.fk (6) τ = Work.Kernels.E6Fun τ by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun τ * (Work.Kernels.E6Fun τ)) * Work.Kernels.jInvariantFun τ
        = (Work.Kernels.E6Fun τ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ) := by ring
      _ = Work.Kernels.E6Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact E6InP.mul (E4InP.pow 3)

private lemma TF_4_0 : Work.Kernels.InP (TF 4 0) := by
  have h : TF 4 0 = fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ := by
    funext τ
    simp only [TF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (4) τ = Work.Kernels.E4Fun τ by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP.mul E4InP

private lemma TF_4_1 : Work.Kernels.InP (TF 4 1) := by
  have h : TF 4 1 = fun τ : ℍ => Work.Kernels.E4Fun τ ^ 4 := by
    funext τ
    simp only [TF, pow_one]
    rw [show Work.Kernels.fk (4) τ = Work.Kernels.E4Fun τ by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun τ)) * Work.Kernels.jInvariantFun τ
        = (Work.Kernels.E4Fun τ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ) := by ring
      _ = Work.Kernels.E4Fun τ ^ 4 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact E4InP.pow 4

private lemma TF_2_0 : Work.Kernels.InP (TF 2 0) := by
  have h : TF 2 0 = fun τ : ℍ => Work.Kernels.E14Fun τ := by
    funext τ
    simp only [TF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (2) τ = Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ by simp only [Work.Kernels.fk]; norm_num]
    have hΔ := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
    field_simp
    try ring
  rw [h]; exact E14InP

private lemma TF_0_0 : Work.Kernels.InP (TF 0 0) := by
  have h : TF 0 0 = fun τ : ℍ => Work.Kernels.DeltaFun τ := by
    funext τ
    simp only [TF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (0) τ = 1 by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP

private lemma TF_0_1 : Work.Kernels.InP (TF 0 1) := by
  have h : TF 0 1 = fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    simp only [TF, pow_one]
    rw [show Work.Kernels.fk (0) τ = 1 by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun τ * (1)) * Work.Kernels.jInvariantFun τ
        = (1) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ) := by ring
      _ = Work.Kernels.E4Fun τ ^ 3 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun, one_mul]
  rw [h]; exact E4InP.pow 3

private lemma TF_14_0 : Work.Kernels.InP (TF 14 0) := by
  have h : TF 14 0 = fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.E14Fun τ := by
    funext τ
    simp only [TF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (14) τ = Work.Kernels.E14Fun τ by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP.mul E14InP

private lemma TF_14_1 : Work.Kernels.InP (TF 14 1) := by
  have h : TF 14 1 = fun τ : ℍ => Work.Kernels.E14Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    simp only [TF, pow_one]
    rw [show Work.Kernels.fk (14) τ = Work.Kernels.E14Fun τ by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun τ * (Work.Kernels.E14Fun τ)) * Work.Kernels.jInvariantFun τ
        = (Work.Kernels.E14Fun τ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ) := by ring
      _ = Work.Kernels.E14Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact E14InP.mul (E4InP.pow 3)

private lemma TF_12_0 : Work.Kernels.InP (TF 12 0) := by
  have h : TF 12 0 = fun τ : ℍ => Work.Kernels.DeltaFun τ ^ 2 := by
    funext τ
    simp only [TF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (12) τ = Work.Kernels.DeltaFun τ by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP.pow 2

private lemma TF_12_1 : Work.Kernels.InP (TF 12 1) := by
  have h : TF 12 1 = fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    simp only [TF, pow_one]
    rw [show Work.Kernels.fk (12) τ = Work.Kernels.DeltaFun τ by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ)) * Work.Kernels.jInvariantFun τ
        = (Work.Kernels.DeltaFun τ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ) := by ring
      _ = Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ ^ 3 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact DeltaInP.mul (E4InP.pow 3)

private lemma TF_12_2 : Work.Kernels.InP (TF 12 2) := by
  have h : TF 12 2 = fun τ : ℍ => Work.Kernels.E4Fun τ ^ 6 := by
    funext τ
    simp only [TF]
    rw [show Work.Kernels.fk (12) τ = Work.Kernels.DeltaFun τ by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ) * Work.Kernels.jInvariantFun τ ^ 2
        = (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ) ^ 2 := by ring
      _ = Work.Kernels.E4Fun τ ^ 6 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact E4InP.pow 6

private lemma TF_10_0 : Work.Kernels.InP (TF 10 0) := by
  have h : TF 10 0 = fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.E10Fun τ := by
    funext τ
    simp only [TF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (10) τ = Work.Kernels.E10Fun τ by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP.mul E10InP

private lemma TF_10_1 : Work.Kernels.InP (TF 10 1) := by
  have h : TF 10 1 = fun τ : ℍ => Work.Kernels.E10Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    simp only [TF, pow_one]
    rw [show Work.Kernels.fk (10) τ = Work.Kernels.E10Fun τ by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun τ * (Work.Kernels.E10Fun τ)) * Work.Kernels.jInvariantFun τ
        = (Work.Kernels.E10Fun τ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ) := by ring
      _ = Work.Kernels.E10Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact E10InP.mul (E4InP.pow 3)

private lemma TF_8_0 : Work.Kernels.InP (TF 8 0) := by
  have h : TF 8 0 = fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.E8Fun τ := by
    funext τ
    simp only [TF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (8) τ = Work.Kernels.E8Fun τ by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP.mul E8InP

private lemma TF_8_1 : Work.Kernels.InP (TF 8 1) := by
  have h : TF 8 1 = fun τ : ℍ => Work.Kernels.E8Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
    funext τ
    simp only [TF, pow_one]
    rw [show Work.Kernels.fk (8) τ = Work.Kernels.E8Fun τ by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun τ * (Work.Kernels.E8Fun τ)) * Work.Kernels.jInvariantFun τ
        = (Work.Kernels.E8Fun τ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ) := by ring
      _ = Work.Kernels.E8Fun τ * Work.Kernels.E4Fun τ ^ 3 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact E8InP.mul (E4InP.pow 3)

private lemma ZF_12_0 : Work.Kernels.InP (ZF 12 0) := by
  have h : ZF 12 0 = fun z : ℍ => Work.Kernels.DeltaFun z := by
    funext z
    simp only [ZF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (12) z = Work.Kernels.DeltaFun z by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP

private lemma ZF_12_1 : Work.Kernels.InP (ZF 12 1) := by
  have h : ZF 12 1 = fun z : ℍ => Work.Kernels.E4Fun z ^ 3 := by
    funext z
    simp only [ZF, pow_one]
    rw [show Work.Kernels.fk (12) z = Work.Kernels.DeltaFun z by simp only [Work.Kernels.fk]; norm_num]
    simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
    try ring
  rw [h]; exact E4InP.pow 3

private lemma ZF_10_0 : Work.Kernels.InP (ZF 10 0) := by
  have h : ZF 10 0 = fun z : ℍ => Work.Kernels.E10Fun z := by
    funext z
    simp only [ZF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (10) z = Work.Kernels.E10Fun z by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact E10InP

private lemma ZF_8_0 : Work.Kernels.InP (ZF 8 0) := by
  have h : ZF 8 0 = fun z : ℍ => Work.Kernels.E8Fun z := by
    funext z
    simp only [ZF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (8) z = Work.Kernels.E8Fun z by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact E8InP

private lemma ZF_6_0 : Work.Kernels.InP (ZF 6 0) := by
  have h : ZF 6 0 = fun z : ℍ => Work.Kernels.E6Fun z := by
    funext z
    simp only [ZF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (6) z = Work.Kernels.E6Fun z by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact E6InP

private lemma DF_4_0 : Work.Kernels.InP (DF (4) 0) := by
  have h : DF (4) 0 = fun z : ℍ => Work.Kernels.DeltaFun z * Work.Kernels.E4Fun z := by
    funext z
    simp only [DF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (4) z = Work.Kernels.E4Fun z by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP.mul E4InP

private lemma DF_4_1 : Work.Kernels.InP (DF (4) 1) := by
  have h : DF (4) 1 = fun z : ℍ => Work.Kernels.E4Fun z ^ 4 := by
    funext z
    simp only [DF, pow_one]
    rw [show Work.Kernels.fk (4) z = Work.Kernels.E4Fun z by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun z * (Work.Kernels.E4Fun z)) * Work.Kernels.jInvariantFun z
        = (Work.Kernels.E4Fun z) * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun z) := by ring
      _ = Work.Kernels.E4Fun z ^ 4 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact E4InP.pow 4

private lemma DF_2_0 : Work.Kernels.InP (DF (2) 0) := by
  have h : DF (2) 0 = fun z : ℍ => Work.Kernels.E14Fun z := by
    funext z
    simp only [DF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (2) z = Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z by simp only [Work.Kernels.fk]; norm_num]
    have hΔ := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    field_simp
    try ring
  rw [h]; exact E14InP

private lemma DF_0_0 : Work.Kernels.InP (DF (0) 0) := by
  have h : DF (0) 0 = fun z : ℍ => Work.Kernels.DeltaFun z := by
    funext z
    simp only [DF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (0) z = 1 by simp only [Work.Kernels.fk]; norm_num]
    try ring
  rw [h]; exact DeltaInP

private lemma DF_0_1 : Work.Kernels.InP (DF (0) 1) := by
  have h : DF (0) 1 = fun z : ℍ => Work.Kernels.E4Fun z ^ 3 := by
    funext z
    simp only [DF, pow_one]
    rw [show Work.Kernels.fk (0) z = 1 by simp only [Work.Kernels.fk]; norm_num]
    calc (Work.Kernels.DeltaFun z * (1)) * Work.Kernels.jInvariantFun z
        = (1) * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun z) := by ring
      _ = Work.Kernels.E4Fun z ^ 3 := by
          simp only [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
          try ring
  rw [h]; exact E4InP.pow 3

private lemma DFm_2_0 : Work.Kernels.InP (DF (-2) 0) := by
  have h : DF (-2) 0 = fun z : ℍ => Work.Kernels.E10Fun z := by
    funext z
    simp only [DF, pow_zero, mul_one]
    rw [show Work.Kernels.fk (-2) z = Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z by simp only [Work.Kernels.fk]; norm_num]
    have hΔ := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    field_simp
    try ring
  rw [h]; exact E10InP

/-! ## The entries of the cleared coefficient matrices -/

private lemma e_UP8_00 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 0 0) =
    fun τ z => ((cc8) * TF (6) 1 τ) * ZF (12) 0 z + ((-cc8) * TF (6) 0 τ) * ZF (12) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP8_01 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 0 1) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP8_02 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 0 2) =
    fun τ z => ((cc8) * TF (6) 0 τ) * ZF (8) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP8_10 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 1 0) =
    fun τ z => ((-2 * cc8) * TF (4) 1 τ) * ZF (12) 0 z + ((2 * cc8) * TF (4) 0 τ) * ZF (12) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP8_11 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 1 1) =
    fun τ z => ((-2 * cc8) * TF (4) 0 τ) * ZF (10) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP8_12 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 1 2) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP8_20 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 2 0) =
    fun τ z => ((cc8) * TF (2) 0 τ) * ZF (12) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP8_21 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 2 1) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP8_22 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 2 2) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_00 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 0 0) =
    fun τ z => ((-2 * Work.Kernels.c1728 * cm) * TF (4) 0 τ) * ZF (10) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_01 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 0 1) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_02 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 0 2) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_10 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 1 0) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_11 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 1 1) =
    fun τ z => ((cm) * TF (2) 0 τ) * ZF (8) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_12 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 1 2) =
    fun τ z => ((-cm) * TF (2) 0 τ) * ZF (6) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_20 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 2 0) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_21 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 2 1) =
    fun τ z => ((Work.Kernels.c1728 * cm) * TF (0) 0 τ) * ZF (8) 0 z + ((-cm) * TF (0) 1 τ) * ZF (8) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM8_22 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 2 2) =
    fun τ z => ((cm) * TF (0) 1 τ) * ZF (6) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_00 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 0 0) =
    fun τ z => ((6 * c24) * TF (14) 1 τ) * DF (4) 0 z + ((-6 * c24) * TF (14) 0 τ) * DF (4) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_01 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 0 1) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_02 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 0 2) =
    fun τ z => ((Work.Kernels.c1728 * c24) * TF (14) 0 τ) * DF (0) 0 z + ((-6 * c24) * TF (14) 1 τ) * DF (0) 0 z + ((6 * c24) * TF (14) 0 τ) * DF (0) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_10 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 1 0) =
    fun τ z => ((-12 * c24) * TF (12) 2 τ) * DF (4) 0 z + ((12 * c24) * TF (12) 1 τ) * DF (4) 1 z + ((5 * Work.Kernels.c1728 * c24) * TF (12) 1 τ) * DF (4) 0 z + ((-5 * Work.Kernels.c1728 * c24) * TF (12) 0 τ) * DF (4) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_11 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 1 1) =
    fun τ z => ((-2 * Work.Kernels.c1728 * c24) * TF (12) 0 τ) * DF (2) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_12 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 1 2) =
    fun τ z => ((12 * c24) * TF (12) 2 τ) * DF (0) 0 z + ((-12 * c24) * TF (12) 1 τ) * DF (0) 1 z + ((-7 * Work.Kernels.c1728 * c24) * TF (12) 1 τ) * DF (0) 0 z + ((7 * Work.Kernels.c1728 * c24) * TF (12) 0 τ) * DF (0) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_20 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 2 0) =
    fun τ z => ((Work.Kernels.c1728 * c24) * TF (10) 0 τ) * DF (4) 0 z + ((6 * c24) * TF (10) 1 τ) * DF (4) 0 z + ((-6 * c24) * TF (10) 0 τ) * DF (4) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_21 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 2 1) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UP24_22 : (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 2 2) =
    fun τ z => ((-6 * c24) * TF (10) 1 τ) * DF (0) 0 z + ((6 * c24) * TF (10) 0 τ) * DF (0) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_00 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 0 0) =
    fun τ z => ((-2 * Work.Kernels.c1728 * cm) * TF (12) 0 τ) * DF (2) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_01 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 0 1) =
    fun τ z => ((-2 * Work.Kernels.c1728 * cm) * TF (12) 1 τ) * DF (0) 0 z + ((2 * Work.Kernels.c1728 * cm) * TF (12) 0 τ) * DF (0) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_02 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 0 2) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_10 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 1 0) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_11 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 1 1) =
    fun τ z => ((3 * cm) * TF (10) 1 τ) * DF (0) 0 z + ((-2 * cm) * TF (10) 0 τ) * DF (0) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_12 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 1 2) =
    fun τ z => ((-cm) * TF (10) 0 τ) * DF (-2) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_20 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 2 0) =
    fun τ z => (0 : ℂ) := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_21 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 2 1) =
    fun τ z => ((Work.Kernels.c1728 * cm) * TF (8) 0 τ) * DF (0) 0 z + ((-3 * cm) * TF (8) 1 τ) * DF (0) 0 z + ((2 * cm) * TF (8) 0 τ) * DF (0) 1 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

private lemma e_UM24_22 : (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 2 2) =
    fun τ z => ((cm) * TF (8) 0 τ) * DF (-2) 0 z := by
  funext τ z
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, if_true, ite_false, smul_eq_mul, TF, ZF, DF, cc8, c24, cm]
  simp
  try ring

/-! ## Two-variable moderate growth of the entries -/

private lemma mg2_UP8_00 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 0 0) := by
  rw [e_UP8_00]
  exact ((MG2_prod (Work.Kernels.InP.const_mul (cc8) TF_6_1) ZF_12_0).add (MG2_prod (Work.Kernels.InP.const_mul (-cc8) TF_6_0) ZF_12_1))

private lemma mg2_UP8_01 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 0 1) := by
  rw [e_UP8_01]
  exact ModerateGrowth2.zero

private lemma mg2_UP8_02 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 0 2) := by
  rw [e_UP8_02]
  exact (MG2_prod (Work.Kernels.InP.const_mul (cc8) TF_6_0) ZF_8_0)

private lemma mg2_UP8_10 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 1 0) := by
  rw [e_UP8_10]
  exact ((MG2_prod (Work.Kernels.InP.const_mul (-2 * cc8) TF_4_1) ZF_12_0).add (MG2_prod (Work.Kernels.InP.const_mul (2 * cc8) TF_4_0) ZF_12_1))

private lemma mg2_UP8_11 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 1 1) := by
  rw [e_UP8_11]
  exact (MG2_prod (Work.Kernels.InP.const_mul (-2 * cc8) TF_4_0) ZF_10_0)

private lemma mg2_UP8_12 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 1 2) := by
  rw [e_UP8_12]
  exact ModerateGrowth2.zero

private lemma mg2_UP8_20 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 2 0) := by
  rw [e_UP8_20]
  exact (MG2_prod (Work.Kernels.InP.const_mul (cc8) TF_2_0) ZF_12_0)

private lemma mg2_UP8_21 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 2 1) := by
  rw [e_UP8_21]
  exact ModerateGrowth2.zero

private lemma mg2_UP8_22 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z 2 2) := by
  rw [e_UP8_22]
  exact ModerateGrowth2.zero

private lemma UP8_mg2 (i j : Fin 3) :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 8 τ z i j) := by
  fin_cases i <;> fin_cases j
  · exact mg2_UP8_00
  · exact mg2_UP8_01
  · exact mg2_UP8_02
  · exact mg2_UP8_10
  · exact mg2_UP8_11
  · exact mg2_UP8_12
  · exact mg2_UP8_20
  · exact mg2_UP8_21
  · exact mg2_UP8_22

private lemma mg2_UM8_00 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 0 0) := by
  rw [e_UM8_00]
  exact (MG2_prod (Work.Kernels.InP.const_mul (-2 * Work.Kernels.c1728 * cm) TF_4_0) ZF_10_0)

private lemma mg2_UM8_01 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 0 1) := by
  rw [e_UM8_01]
  exact ModerateGrowth2.zero

private lemma mg2_UM8_02 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 0 2) := by
  rw [e_UM8_02]
  exact ModerateGrowth2.zero

private lemma mg2_UM8_10 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 1 0) := by
  rw [e_UM8_10]
  exact ModerateGrowth2.zero

private lemma mg2_UM8_11 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 1 1) := by
  rw [e_UM8_11]
  exact (MG2_prod (Work.Kernels.InP.const_mul (cm) TF_2_0) ZF_8_0)

private lemma mg2_UM8_12 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 1 2) := by
  rw [e_UM8_12]
  exact (MG2_prod (Work.Kernels.InP.const_mul (-cm) TF_2_0) ZF_6_0)

private lemma mg2_UM8_20 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 2 0) := by
  rw [e_UM8_20]
  exact ModerateGrowth2.zero

private lemma mg2_UM8_21 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 2 1) := by
  rw [e_UM8_21]
  exact ((MG2_prod (Work.Kernels.InP.const_mul (Work.Kernels.c1728 * cm) TF_0_0) ZF_8_0).add (MG2_prod (Work.Kernels.InP.const_mul (-cm) TF_0_1) ZF_8_0))

private lemma mg2_UM8_22 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z 2 2) := by
  rw [e_UM8_22]
  exact (MG2_prod (Work.Kernels.InP.const_mul (cm) TF_0_1) ZF_6_0)

private lemma UM8_mg2 (i j : Fin 3) :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 8 τ z i j) := by
  fin_cases i <;> fin_cases j
  · exact mg2_UM8_00
  · exact mg2_UM8_01
  · exact mg2_UM8_02
  · exact mg2_UM8_10
  · exact mg2_UM8_11
  · exact mg2_UM8_12
  · exact mg2_UM8_20
  · exact mg2_UM8_21
  · exact mg2_UM8_22

private lemma mg2_UP24_00 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 0 0) := by
  rw [e_UP24_00]
  exact ((MG2_prod (Work.Kernels.InP.const_mul (6 * c24) TF_14_1) DF_4_0).add (MG2_prod (Work.Kernels.InP.const_mul (-6 * c24) TF_14_0) DF_4_1))

private lemma mg2_UP24_01 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 0 1) := by
  rw [e_UP24_01]
  exact ModerateGrowth2.zero

private lemma mg2_UP24_02 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 0 2) := by
  rw [e_UP24_02]
  exact (((MG2_prod (Work.Kernels.InP.const_mul (Work.Kernels.c1728 * c24) TF_14_0) DF_0_0).add (MG2_prod (Work.Kernels.InP.const_mul (-6 * c24) TF_14_1) DF_0_0)).add (MG2_prod (Work.Kernels.InP.const_mul (6 * c24) TF_14_0) DF_0_1))

private lemma mg2_UP24_10 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 1 0) := by
  rw [e_UP24_10]
  exact ((((MG2_prod (Work.Kernels.InP.const_mul (-12 * c24) TF_12_2) DF_4_0).add (MG2_prod (Work.Kernels.InP.const_mul (12 * c24) TF_12_1) DF_4_1)).add (MG2_prod (Work.Kernels.InP.const_mul (5 * Work.Kernels.c1728 * c24) TF_12_1) DF_4_0)).add (MG2_prod (Work.Kernels.InP.const_mul (-5 * Work.Kernels.c1728 * c24) TF_12_0) DF_4_1))

private lemma mg2_UP24_11 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 1 1) := by
  rw [e_UP24_11]
  exact (MG2_prod (Work.Kernels.InP.const_mul (-2 * Work.Kernels.c1728 * c24) TF_12_0) DF_2_0)

private lemma mg2_UP24_12 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 1 2) := by
  rw [e_UP24_12]
  exact ((((MG2_prod (Work.Kernels.InP.const_mul (12 * c24) TF_12_2) DF_0_0).add (MG2_prod (Work.Kernels.InP.const_mul (-12 * c24) TF_12_1) DF_0_1)).add (MG2_prod (Work.Kernels.InP.const_mul (-7 * Work.Kernels.c1728 * c24) TF_12_1) DF_0_0)).add (MG2_prod (Work.Kernels.InP.const_mul (7 * Work.Kernels.c1728 * c24) TF_12_0) DF_0_1))

private lemma mg2_UP24_20 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 2 0) := by
  rw [e_UP24_20]
  exact (((MG2_prod (Work.Kernels.InP.const_mul (Work.Kernels.c1728 * c24) TF_10_0) DF_4_0).add (MG2_prod (Work.Kernels.InP.const_mul (6 * c24) TF_10_1) DF_4_0)).add (MG2_prod (Work.Kernels.InP.const_mul (-6 * c24) TF_10_0) DF_4_1))

private lemma mg2_UP24_21 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 2 1) := by
  rw [e_UP24_21]
  exact ModerateGrowth2.zero

private lemma mg2_UP24_22 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z 2 2) := by
  rw [e_UP24_22]
  exact ((MG2_prod (Work.Kernels.InP.const_mul (-6 * c24) TF_10_1) DF_0_0).add (MG2_prod (Work.Kernels.InP.const_mul (6 * c24) TF_10_0) DF_0_1))

private lemma UP24_mg2 (i j : Fin 3) :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear 24 τ z i j) := by
  fin_cases i <;> fin_cases j
  · exact mg2_UP24_00
  · exact mg2_UP24_01
  · exact mg2_UP24_02
  · exact mg2_UP24_10
  · exact mg2_UP24_11
  · exact mg2_UP24_12
  · exact mg2_UP24_20
  · exact mg2_UP24_21
  · exact mg2_UP24_22

private lemma mg2_UM24_00 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 0 0) := by
  rw [e_UM24_00]
  exact (MG2_prod (Work.Kernels.InP.const_mul (-2 * Work.Kernels.c1728 * cm) TF_12_0) DF_2_0)

private lemma mg2_UM24_01 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 0 1) := by
  rw [e_UM24_01]
  exact ((MG2_prod (Work.Kernels.InP.const_mul (-2 * Work.Kernels.c1728 * cm) TF_12_1) DF_0_0).add (MG2_prod (Work.Kernels.InP.const_mul (2 * Work.Kernels.c1728 * cm) TF_12_0) DF_0_1))

private lemma mg2_UM24_02 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 0 2) := by
  rw [e_UM24_02]
  exact ModerateGrowth2.zero

private lemma mg2_UM24_10 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 1 0) := by
  rw [e_UM24_10]
  exact ModerateGrowth2.zero

private lemma mg2_UM24_11 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 1 1) := by
  rw [e_UM24_11]
  exact ((MG2_prod (Work.Kernels.InP.const_mul (3 * cm) TF_10_1) DF_0_0).add (MG2_prod (Work.Kernels.InP.const_mul (-2 * cm) TF_10_0) DF_0_1))

private lemma mg2_UM24_12 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 1 2) := by
  rw [e_UM24_12]
  exact (MG2_prod (Work.Kernels.InP.const_mul (-cm) TF_10_0) DFm_2_0)

private lemma mg2_UM24_20 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 2 0) := by
  rw [e_UM24_20]
  exact ModerateGrowth2.zero

private lemma mg2_UM24_21 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 2 1) := by
  rw [e_UM24_21]
  exact (((MG2_prod (Work.Kernels.InP.const_mul (Work.Kernels.c1728 * cm) TF_8_0) DF_0_0).add (MG2_prod (Work.Kernels.InP.const_mul (-3 * cm) TF_8_1) DF_0_0)).add (MG2_prod (Work.Kernels.InP.const_mul (2 * cm) TF_8_0) DF_0_1))

private lemma mg2_UM24_22 :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z 2 2) := by
  rw [e_UM24_22]
  exact (MG2_prod (Work.Kernels.InP.const_mul (cm) TF_8_0) DFm_2_0)

private lemma UM24_mg2 (i j : Fin 3) :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear 24 τ z i j) := by
  fin_cases i <;> fin_cases j
  · exact mg2_UM24_00
  · exact mg2_UM24_01
  · exact mg2_UM24_02
  · exact mg2_UM24_10
  · exact mg2_UM24_11
  · exact mg2_UM24_12
  · exact mg2_UM24_20
  · exact mg2_UM24_21
  · exact mg2_UM24_22

/-! ## The basis vectors `φ⃗, φ̃⃗, ψ⃗, ψ̃⃗` lie in `𝒫` -/

/-- The coordinate function `z ↦ (z : ℂ)` lies in the class `P`. -/
private lemma hcoe_InP : Work.Kernels.InP (fun z : ℍ => (z : ℂ)) :=
  Work.Kernels.KernelGrowth.InP_coe

/-- `E₂∣₂S` lies in the class `P`. -/
private lemma hE2S_InP : Work.Kernels.InP Work.Kernels.E2S := by
  have h := Work.Kernels.InP.slash Work.Kernels.ClassicalFacts.E2Fun_mem_InP (2 : ℤ) ModularGroup.S
  have hE : Work.Kernels.E2S = (Work.Kernels.E2Fun ∣[(2 : ℤ)] ModularGroup.S) := by
    funext z; rfl
  rwa [hE]

private lemma phitVec_InP_0 : Work.Kernels.InP (fun z : ℍ => Work.Kernels.phitVec z 0) := by
  have h : (fun z : ℍ => Work.Kernels.phitVec z 0) = fun z : ℍ => (z : ℂ) ^ 2 := by
    funext z; simp [Work.Kernels.phitVec]
  rw [h]; exact hcoe_InP.pow 2

private lemma phitVec_InP_1 : Work.Kernels.InP (fun z : ℍ => Work.Kernels.phitVec z 1) := by
  have h : (fun z : ℍ => Work.Kernels.phitVec z 1)
      = fun z : ℍ => (z : ℂ) ^ 2 * Work.Kernels.E2S z := by
    funext z; simp [Work.Kernels.phitVec]
  rw [h]; exact (hcoe_InP.pow 2).mul hE2S_InP

private lemma phitVec_InP_2 : Work.Kernels.InP (fun z : ℍ => Work.Kernels.phitVec z 2) := by
  have h : (fun z : ℍ => Work.Kernels.phitVec z 2)
      = fun z : ℍ => (z : ℂ) ^ 2 * Work.Kernels.E2S z ^ 2 := by
    funext z; simp [Work.Kernels.phitVec]
  rw [h]; exact (hcoe_InP.pow 2).mul (hE2S_InP.pow 2)

private lemma phitVec_InP (j : Fin 3) :
    Work.Kernels.InP (fun z : ℍ => Work.Kernels.phitVec z j) := by
  fin_cases j
  · exact phitVec_InP_0
  · exact phitVec_InP_1
  · exact phitVec_InP_2

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

/-- The coordinates of `ψ⃗(τ) = (1, ψ₂, ψ₄)` lie in `𝒫`. -/
private lemma psiVec_InP (ℓ : Work.Kernels.LogLambdaData) (i : Fin 3) :
    Work.Kernels.InP (fun τ : ℍ => Work.Kernels.psiVec ℓ τ i) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  have hpsi2 : Work.Kernels.InP (Work.Kernels.psi2 ℓ) := by
    have h : Work.Kernels.psi2 ℓ = fun τ : ℍ => Work.Kernels.xi2Fun τ * ℓ.L τ +
        (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
    rw [h]
    exact (xi2_InP.mul hL).add ((xi2_InP.slash (2 : ℤ) ModularGroup.S).mul hLS)
  have hpsi4 : Work.Kernels.InP (Work.Kernels.psi4 ℓ) := by
    have h : Work.Kernels.psi4 ℓ = fun τ : ℍ => Work.Kernels.xi4Fun τ * ℓ.L τ +
        (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
    rw [h]
    exact (xi4_InP.mul hL).add ((xi4_InP.slash (4 : ℤ) ModularGroup.S).mul hLS)
  fin_cases i
  · simpa [Work.Kernels.psiVec] using
      (Work.Kernels.InP.one : Work.Kernels.InP (fun _ : ℍ => (1 : ℂ)))
  · simpa [Work.Kernels.psiVec] using hpsi2
  · simpa [Work.Kernels.psiVec] using hpsi4

/-- The coordinates of `ψ̃⃗(z) = (𝓛, W, U² - V²)` lie in `𝒫`. -/
private lemma psitVec_InP (ℓ : Work.Kernels.LogLambdaData) (j : Fin 3) :
    Work.Kernels.InP (fun z : ℍ => Work.Kernels.psitVec ℓ z j) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hW : Work.Kernels.InP Work.Kernels.WFun :=
    Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta01Fun_mem_InP 4
  have hUWV : Work.Kernels.InP (fun z : ℍ => Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) :=
    (Work.Kernels.InP.pow (Work.Kernels.InP.pow
        Work.Kernels.ClassicalFacts.theta00Fun_mem_InP 4) 2).sub
      (Work.Kernels.InP.pow (Work.Kernels.InP.pow
        Work.Kernels.ClassicalFacts.theta10Fun_mem_InP 4) 2)
  fin_cases j
  · simpa [Work.Kernels.psitVec] using hL
  · simpa [Work.Kernels.psitVec] using hW
  · simpa [Work.Kernels.psitVec] using hUWV

/-! ## Assembly: the cleared kernels -/

/-- Two-variable moderate growth of `K_+^{(d)}`. -/
private lemma KPlusClear_mg2 (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.KPlusClear d τ z) := by
  have hphi : ∀ i : Fin 3, ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.phiVec τ i) :=
    fun i => ModerateGrowth2.of_fst_InP (Work.Kernels.KernelGrowth.PhiVec_InP i)
  have hphit : ∀ j : Fin 3, ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.phitVec z j) :=
    fun j => ModerateGrowth2.of_snd_InP (phitVec_InP j)
  have hU : ∀ i j : Fin 3,
      ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonPlusClear d τ z i j) := by
    rcases hd with rfl | rfl
    · exact UP8_mg2
    · exact UP24_mg2
  have hsum : ModerateGrowth2 (fun τ z => ∑ i : Fin 3, ∑ j : Fin 3,
      Work.Kernels.phiVec τ i * Work.Kernels.UpsilonPlusClear d τ z i j *
        Work.Kernels.phitVec z j) := by
    apply MG2_sum_fun
    intro i _
    apply MG2_sum_fun
    intro j _
    exact ((hphi i).mul (hU i j)).mul (hphit j)
  have heq : (fun τ z : ℍ => Work.Kernels.KPlusClear d τ z) = fun τ z =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        Work.Kernels.phiVec τ i * Work.Kernels.UpsilonPlusClear d τ z i j *
          Work.Kernels.phitVec z j := by
    funext τ z; rfl
  rwa [heq]

/-- Two-variable moderate growth of `K_-^{(d)}`. -/
private lemma KMinusClear_mg2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.KMinusClear ℓ d τ z) := by
  have hpsi : ∀ i : Fin 3, ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.psiVec ℓ τ i) :=
    fun i => ModerateGrowth2.of_fst_InP (psiVec_InP ℓ i)
  have hpsit : ∀ j : Fin 3, ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.psitVec ℓ z j) :=
    fun j => ModerateGrowth2.of_snd_InP (psitVec_InP ℓ j)
  have hU : ∀ i j : Fin 3,
      ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.UpsilonMinusClear d τ z i j) := by
    rcases hd with rfl | rfl
    · exact UM8_mg2
    · exact UM24_mg2
  have hsum : ModerateGrowth2 (fun τ z => ∑ i : Fin 3, ∑ j : Fin 3,
      Work.Kernels.psiVec ℓ τ i * Work.Kernels.UpsilonMinusClear d τ z i j *
        Work.Kernels.psitVec ℓ z j) := by
    apply MG2_sum_fun
    intro i _
    apply MG2_sum_fun
    intro j _
    exact ((hpsi i).mul (hU i j)).mul (hpsit j)
  have heq : (fun τ z : ℍ => Work.Kernels.KMinusClear ℓ d τ z) = fun τ z =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        Work.Kernels.psiVec ℓ τ i * Work.Kernels.UpsilonMinusClear d τ z i j *
          Work.Kernels.psitVec ℓ z j := by
    funext τ z; rfl
  rwa [heq]

/-- Two-variable moderate growth of the cleared kernel `K^{(d)}`. -/
private lemma KfunClear_mg2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.KfunClear ℓ d τ z) := by
  have h1 := KPlusClear_mg2 d hd
  have h2 := KMinusClear_mg2 ℓ d hd
  have heq : (fun τ z : ℍ => Work.Kernels.KfunClear ℓ d τ z) = fun τ z =>
      (2 : ℂ)⁻¹ * Work.Kernels.KPlusClear d τ z +
        (2 : ℂ)⁻¹ * Work.Kernels.KMinusClear ℓ d τ z := by
    funext τ z; simp only [Work.Kernels.KfunClear]; ring
  rw [heq]
  exact (h1.const_mul _).add (h2.const_mul _)

/-- Two-variable moderate growth of the cleared kernel `K̂^{(d)}`. -/
private lemma KhatClear_mg2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ModerateGrowth2 (fun τ z : ℍ => Work.Kernels.KhatClear ℓ d τ z) := by
  have h1 := KPlusClear_mg2 d hd
  have h2 := KMinusClear_mg2 ℓ d hd
  have heq : (fun τ z : ℍ => Work.Kernels.KhatClear ℓ d τ z) = fun τ z =>
      (2 : ℂ)⁻¹ * Work.Kernels.KPlusClear d τ z +
        (-(2 : ℂ)⁻¹) * Work.Kernels.KMinusClear ℓ d τ z := by
    funext τ z; simp only [Work.Kernels.KhatClear]; ring
  rw [heq]
  exact (h1.const_mul _).add (h2.const_mul _)

/-! ## The requested statement -/

/-- **Two-variable moderate growth of the cleared CKMRV kernels.**  For `d ∈ {8, 24}` the
cleared kernels `Δ(τ)Δ(z)^e(j(τ)-j(z))K^{(d)}(τ,z)` and the same for `K̂^{(d)}` satisfy the
two-variable bound `‖F τ z‖ ≤ α (scale τ)^N (scale z)^M` with constants independent of both
variables.  This is Theorem 4.9(4) with the `z`-dependence of the constants tracked; it is what
turns the kernels into an integrable dominator on the contour `z = it` (cf.
`Work.Asymptotics.norm_Kfun_le_of_divisor`). -/
theorem KClear_mg2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Work.Asymptotics.ModerateGrowth2 (fun τ z : UpperHalfPlane => Work.Kernels.KfunClear ℓ d τ z) ∧
    Work.Asymptotics.ModerateGrowth2 (fun τ z : UpperHalfPlane => Work.Kernels.KhatClear ℓ d τ z) := by
  exact ⟨KfunClear_mg2 ℓ d hd, KhatClear_mg2 ℓ d hd⟩

end Work.Asymptotics
