/-
# The functional equations of the basis functions `φ_{-2}`, `φ_0`, `φ_2`

CKMRV Proposition 4.2 states that the space `Ann_k(𝓘₊, 𝒫)` of functions in `𝒫` annihilated by
the right ideal `𝓘₊ = (S+I)R + (T-I)²R` is

  `φ_2 M_{k-2} + φ_0 M_k + φ_{-2} M_{k+2}`

with `φ_{-2}(τ) = τ`, `φ_0(τ) = τE₂(τ) - 3i/π`, `φ_2(τ) = τE₂(τ)² - (6i/π)E₂(τ)`.

This file proves the "⊇" half of that proposition: each `φ_j` is annihilated by `(T-I)²` and
by `S + I` in its weight `j`, stated in the *explicit* pointwise form

  `F(τ+2) - 2F(τ+1) + F(τ) = 0`,   `(F ∣[j] S)(τ) + F(τ) = 0`.

## Main definitions

* `Work.Kernels.T2op` : the operator `F ↦ F(·+2) - 2F(·+1) + F`, i.e. the action of `(T-I)²`
  at any weight.
* `Work.Kernels.Sop` : the operator `F ↦ (F ∣[k] S) + F`, i.e. the action of `S + I` at
  weight `k`.
-/
import Mathlib
import Submission.Work.Kernels.E2Laws

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- The operator `F ↦ F(·+2) - 2F(·+1) + F`, the action of `(T-I)²` (its value is independent
of the weight). -/
def T2op (F : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => F ((2 : ℝ) +ᵥ τ) - 2 * F ((1 : ℝ) +ᵥ τ) + F τ

/-- The operator `F ↦ (F ∣[k] S) + F`, the action of `S + I` at weight `k`. -/
def Sop (k : ℤ) (F : ℍ → ℂ) : ℍ → ℂ := fun τ => (F ∣[k] ModularGroup.S) τ + F τ

/-- The operator `F ↦ (F ∣[k] S) - F`, the action of `S - I` at weight `k`. -/
def Sopm (k : ℤ) (F : ℍ → ℂ) : ℍ → ℂ := fun τ => (F ∣[k] ModularGroup.S) τ - F τ

/-! ## Auxiliary computations -/

lemma coe_vadd_one (τ : ℍ) : (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) = 1 + (τ : ℂ) := by
  rw [UpperHalfPlane.coe_vadd]; norm_num

lemma coe_vadd_two (τ : ℍ) : (((2 : ℝ) +ᵥ τ : ℍ) : ℂ) = 2 + (τ : ℂ) := by
  rw [UpperHalfPlane.coe_vadd]; norm_num

lemma vadd_one_add_one (τ : ℍ) : (2 : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) := by
  ext <;> simp [UpperHalfPlane.coe_vadd] <;> ring

lemma E2Fun_vadd_two (τ : ℍ) : E2Fun ((2 : ℝ) +ᵥ τ) = E2Fun τ := by
  rw [vadd_one_add_one, E2Fun_vadd_one, E2Fun_vadd_one]

lemma S_smul_coe (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]
  simp

lemma denom_S (z : ℂ) : UpperHalfPlane.denom (glOf ModularGroup.S) z = z := by
  show (glOf ModularGroup.S) 1 0 * z + (glOf ModularGroup.S) 1 1 = z
  rw [glOf_apply, glOf_apply]
  have h1 : (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by decide
  have h0 : (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by decide
  rw [h1, h0]; norm_num

lemma slash_S_apply (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] ModularGroup.S) τ = F (ModularGroup.S • τ) * (τ : ℂ) ^ (-k) := by
  rw [SL_slash_apply, denom_S]

/-! ## The functional equations of `φ_{-2}`, `φ_0`, `φ_2` -/

theorem phiNeg2_T2 : T2op phiNeg2 = 0 := by
  ext τ
  simp only [T2op, phiNeg2, Pi.zero_apply, coe_vadd_one, coe_vadd_two]
  ring

lemma phiNeg2_S_smul (τ : ℍ) : phiNeg2 (ModularGroup.S • τ) = -((τ : ℂ))⁻¹ :=
  S_smul_coe τ

lemma phi0_S_smul (τ : ℍ) : phi0 (ModularGroup.S • τ) = - phi0 τ := by
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  simp only [phi0, S_smul_coe, E2Fun_S_smul]
  field_simp
  ring

lemma phi2_S_smul (τ : ℍ) : phi2 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * (- phi2 τ) := by
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  simp only [phi2, S_smul_coe, E2Fun_S_smul]
  field_simp
  ring

theorem phiNeg2_S_add : Sop (-2) phiNeg2 = 0 := by
  ext τ
  simp only [Sop, Pi.zero_apply]
  rw [slash_S_apply, phiNeg2_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  have h2 : (-(-2 : ℤ)) = (2 : ℤ) := by norm_num
  rw [h2]
  simp only [phiNeg2]
  field_simp
  ring

theorem phi0_T2 : T2op phi0 = 0 := by
  ext τ
  simp only [T2op, phi0, Pi.zero_apply, coe_vadd_one, coe_vadd_two, E2Fun_vadd_one,
    E2Fun_vadd_two]
  ring

theorem phi0_S_add : Sop 0 phi0 = 0 := by
  ext τ
  simp only [Sop, Pi.zero_apply]
  rw [slash_S_apply, phi0_S_smul]
  simp only [neg_zero, zpow_zero, mul_one]
  ring

theorem phi2_T2 : T2op phi2 = 0 := by
  ext τ
  simp only [T2op, phi2, Pi.zero_apply, coe_vadd_one, coe_vadd_two, E2Fun_vadd_one,
    E2Fun_vadd_two]
  ring

theorem phi2_S_add : Sop 2 phi2 = 0 := by
  ext τ
  simp only [Sop, Pi.zero_apply]
  rw [slash_S_apply, phi2_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  field_simp
  ring

/-! ## The product rule for the two annihilation conditions -/

lemma T2op_zero : T2op (fun _ : ℍ => (0 : ℂ)) = 0 := by
  ext τ; simp [T2op]

lemma Sop_zero (k : ℤ) : Sop k (fun _ : ℍ => (0 : ℂ)) = 0 := by
  ext τ
  change ((0 : ℍ → ℂ) ∣[k] ModularGroup.S) τ + (0 : ℍ → ℂ) τ = 0
  rw [SlashAction.zero_slash]
  simp

lemma T2op_add {F G : ℍ → ℂ} (hF : T2op F = 0) (hG : T2op G = 0) : T2op (F + G) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  have h2 := congr_fun hG τ
  simp only [T2op, Pi.zero_apply] at h1 h2
  simp only [T2op, Pi.add_apply, Pi.zero_apply]
  linear_combination h1 + h2

lemma T2op_sum {ι : Type*} {F : ι → ℍ → ℂ} (s : Finset ι)
    (h : ∀ i ∈ s, T2op (F i) = 0) : T2op (∑ i ∈ s, F i) = 0 := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact T2op_zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact T2op_add (h i (Finset.mem_insert_self i s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma Sop_add {k : ℤ} {F G : ℍ → ℂ} (hF : Sop k F = 0) (hG : Sop k G = 0) :
    Sop k (F + G) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  have h2 := congr_fun hG τ
  simp only [Sop, Pi.zero_apply, SlashAction.add_slash] at h1 h2
  simp only [Sop, Pi.add_apply, Pi.zero_apply, SlashAction.add_slash]
  linear_combination h1 + h2

lemma Sop_sum {k : ℤ} {ι : Type*} {F : ι → ℍ → ℂ} (s : Finset ι)
    (h : ∀ i ∈ s, Sop k (F i) = 0) : Sop k (∑ i ∈ s, F i) = 0 := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact Sop_zero k
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact Sop_add (h i (Finset.mem_insert_self i s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- If `G` is invariant under `T` (`G(τ+1) = G(τ)`) and `(T-I)²F = 0`, then `(T-I)²(FG) = 0`. -/
lemma T2op_mul_of {F G : ℍ → ℂ} (hF : T2op F = 0) (hG : ∀ τ : ℍ, G ((1 : ℝ) +ᵥ τ) = G τ) :
    T2op (fun τ => F τ * G τ) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  have hG1 : G ((1 : ℝ) +ᵥ τ) = G τ := hG τ
  have hG2 : G ((2 : ℝ) +ᵥ τ) = G τ := by
    rw [vadd_one_add_one, hG, hG1]
  simp only [T2op, Pi.zero_apply] at h1
  simp only [T2op, Pi.zero_apply]
  rw [hG2, hG1]
  linear_combination h1 * G τ

lemma Sopm_zero (k : ℤ) : Sopm k (fun _ : ℍ => (0 : ℂ)) = 0 := by
  ext τ
  change ((0 : ℍ → ℂ) ∣[k] ModularGroup.S) τ - (0 : ℍ → ℂ) τ = 0
  rw [SlashAction.zero_slash]
  simp

/-- The constant function `1` is fixed by `S` at weight `0`, hence killed by `S - I` there. -/
theorem Sopm_one : Sopm 0 (fun _ : ℍ => (1 : ℂ)) = 0 := by
  ext τ
  change ((1 : ℍ → ℂ) ∣[(0 : ℤ)] ModularGroup.S) τ - (1 : ℍ → ℂ) τ = 0
  rw [ModularForm.is_invariant_one]
  simp

/-- If `G ∣[k₂] S = G` and `(S-I)` kills `F` at weight `k₁`, then `(S-I)` kills `FG`
at weight `k₁ + k₂`. -/
lemma Sopm_mul_of {k₁ k₂ : ℤ} {F G : ℍ → ℂ} (hF : Sopm k₁ F = 0) (hG : G ∣[k₂] S = G) :
    Sopm (k₁ + k₂) (fun τ => F τ * G τ) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  simp only [Sopm, Pi.zero_apply] at h1
  have h1' : (F ∣[k₁] S) τ = F τ := by linear_combination h1
  have hG' : (G ∣[k₂] S) τ = G τ := by rw [hG]
  show ((F * G) ∣[k₁ + k₂] ModularGroup.S) τ - (F * G) τ = 0
  rw [mul_slash_SL2, Pi.mul_apply, Pi.mul_apply, h1', hG']
  ring

/-- If `G ∣[k₂] S = G` and `(S+I)` kills `F` at weight `k₁`, then `(S+I)` kills `FG`
at weight `k₁ + k₂`. -/
lemma Sop_mul_of {k₁ k₂ : ℤ} {F G : ℍ → ℂ} (hF : Sop k₁ F = 0) (hG : G ∣[k₂] S = G) :
    Sop (k₁ + k₂) (fun τ => F τ * G τ) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  simp only [Sop, Pi.zero_apply] at h1
  have h1' : (F ∣[k₁] S) τ = - F τ := by linear_combination h1
  have hG' : (G ∣[k₂] S) τ = G τ := by rw [hG]
  show ((F * G) ∣[k₁ + k₂] ModularGroup.S) τ + (F * G) τ = 0
  rw [mul_slash_SL2, Pi.mul_apply, Pi.mul_apply, h1', hG']
  ring

end Work.Kernels
