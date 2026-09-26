/-
# `S`-invariance of the coefficient functions of `K_+^{(d)}`

CKMRV (Ann. of Math. 196 (2022)) build the kernel `K_+^{(d)}` for `d = 8, 24` as

  `K_+^{(d)}(τ,z) = ∑_i φ_i(τ) · c_i^{(d)}(τ,z)`,
  `c_i^{(d)}(τ,z) = ∑_j Υ_+^{(d)}(τ,z)_{ij} φ̃_j(z)`

(`Work.Kernels.KPlus`, `Work.Kernels.KPlusCoeff`), with `φ_{-2}, φ_0, φ_2` of weights
`-2, 0, 2`.  For `K_+^{(d)}(·,z)` to have weight `d/2` under `SL(2,ℤ)`, the coefficient
`c_i` must have weight `d/2 + 2 - 2i`.  This file proves the corresponding statement for the
generator `S` of `SL(2,ℤ)`:

  `(c_i^{(d)}(·,z)) ∣[d/2 + 2 - 2i] S = c_i^{(d)}(·,z)`,

i.e. `KPlusCoeff d z i` is `S`-invariant in the weight `d/2 + 2 - 2*((i : ℕ) : ℤ)`.

The content is entirely explicit.  Writing `Υ_+^{(d)}(τ,z) = s(τ,z) • (Π_a(τ)·M(j τ, j τ - j z)·Π_b(z))`
with `Π_k(τ)` the diagonal matrix `diag(f_{k_1},f_{k_2},f_{k_3})`, one checks

* the scalar `s(τ,z)` and the matrix `M` depend on `τ` only through `j(τ)` and the
  `S`-invariant number `j(τ) - j(z)` (for `d = 24` the scalar is even independent of `τ`);
* `f_k(S·τ) = τ^k f_k(τ)` for each modular form appearing in `fk` (weights `-2,0,2,4,6,8,10,12,14`).

Hence `Υ_+^{(d)}(S·τ,z) = diag(τ^{a_1},τ^{a_2},τ^{a_3}) · Υ_+^{(d)}(τ,z)` with `(a_1,a_2,a_3) = (6,4,2)`
for `d = 8` and `(14,12,10)` for `d = 24`, and `a_i = d/2 + 2 - 2i`.

## Main result

* `Work.Kernels.KernelFacts.KPlusCoeff_slash_S`.
-/
import Mathlib
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelFacts

open Work.Kernels

/-! ## Pointwise transformation laws under `τ ↦ S • τ` -/

/-- The slash action of the generator `S` on a function `ℍ → ℂ`: it inverts `τ` on the
function and multiplies by the factor of automorphy `τ ^ (-k)`. -/
lemma kpc_slash_S_apply (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] ModularGroup.S) τ = F (ModularGroup.S • τ) * (τ : ℂ) ^ (-k) := by
  rw [slash_apply', jFun_apply]
  norm_num

/-- A point of `ℍ` is a non-zero complex number. -/
lemma kpc_tau_ne_zero (τ : ℍ) : (τ : ℂ) ≠ 0 := fun h =>
  τ.im_ne_zero (by rw [← coe_im τ, h]; simp)

/-- `E₄` is `S`-invariant in weight `4`. -/
lemma kpc_E4_slash_S : E4Fun ∣[(4 : ℤ)] ModularGroup.S = E4Fun := by
  have h := ModularForm.E₄.slash_action_eq' (ModularGroup.S : GL (Fin 2) ℝ)
      (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩)
  rw [← ModularForm.SL_slash] at h
  simpa [E4Fun] using h

/-- `E₆` is `S`-invariant in weight `6`. -/
lemma kpc_E6_slash_S : E6Fun ∣[(6 : ℤ)] ModularGroup.S = E6Fun := by
  have h := ModularForm.E₆.slash_action_eq' (ModularGroup.S : GL (Fin 2) ℝ)
      (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩)
  rw [← ModularForm.SL_slash] at h
  simpa [E6Fun] using h

/-- `Δ` is `S`-invariant in weight `12`. -/
lemma kpc_Delta_slash_S : DeltaFun ∣[(12 : ℤ)] ModularGroup.S = DeltaFun := by
  simpa [DeltaFun] using ModularForm.discriminant_S_invariant

/-- A function which is `S`-invariant of weight `k` satisfies the pointwise transformation
law `F(S • τ) = τ^k F(τ)`. -/
lemma kpc_smul_S_of_slash {k : ℤ} {F : ℍ → ℂ} (h : F ∣[k] ModularGroup.S = F) (τ : ℍ) :
    F (ModularGroup.S • τ) = (τ : ℂ) ^ k * F τ := by
  have h1 : F (ModularGroup.S • τ) * (τ : ℂ) ^ (-k) = F τ := by
    rw [← kpc_slash_S_apply k F τ, h]
  have hτ := kpc_tau_ne_zero τ
  calc F (ModularGroup.S • τ) = F (ModularGroup.S • τ) * 1 := by rw [mul_one]
    _ = F (ModularGroup.S • τ) * ((τ : ℂ) ^ (-k) * (τ : ℂ) ^ k) := by
          rw [← zpow_add₀ hτ, neg_add_cancel, zpow_zero]
    _ = (F (ModularGroup.S • τ) * (τ : ℂ) ^ (-k)) * (τ : ℂ) ^ k := by rw [mul_assoc]
    _ = F τ * (τ : ℂ) ^ k := by rw [h1]
    _ = (τ : ℂ) ^ k * F τ := by rw [mul_comm]

/-- The functions `f_k` of CKMRV Section 4.4 transform under `S` in their own weight. -/
lemma kpc_fk_S (k : ℤ) (τ : ℍ) : fk k (ModularGroup.S • τ) = (τ : ℂ) ^ k * fk k τ := by
  have hE4 := kpc_smul_S_of_slash kpc_E4_slash_S τ
  have hE6 := kpc_smul_S_of_slash kpc_E6_slash_S τ
  have hDel := kpc_smul_S_of_slash kpc_Delta_slash_S τ
  have hτ := kpc_tau_ne_zero τ
  simp only [fk]
  split_ifs with e1 e2 e3 e4 e5 e6 e7 e8 e9
  · rw [e1]
    have h10 : E10Fun (ModularGroup.S • τ) = (τ : ℂ) ^ (10 : ℤ) * E10Fun τ := by
      simp only [E10Fun, hE4, hE6, zpow_ofNat]; ring
    rw [h10, hDel]
    have he : (τ : ℂ) ^ (10 : ℤ) / (τ : ℂ) ^ (12 : ℤ) = (τ : ℂ) ^ (-2 : ℤ) := by
      rw [← zpow_sub₀ hτ]; norm_num
    rw [← he, div_mul_div_comm]
  · rw [e2]; simp
  · rw [e3]
    have h14 : E14Fun (ModularGroup.S • τ) = (τ : ℂ) ^ (14 : ℤ) * E14Fun τ := by
      simp only [E14Fun, hE4, hE6, zpow_ofNat]; ring
    rw [h14, hDel]
    have he : (τ : ℂ) ^ (14 : ℤ) / (τ : ℂ) ^ (12 : ℤ) = (τ : ℂ) ^ (2 : ℤ) := by
      rw [← zpow_sub₀ hτ]; norm_num
    rw [← he, div_mul_div_comm]
  · rw [e4]; exact hE4
  · rw [e5]; exact hE6
  · rw [e6]; simp only [E8Fun, hE4, zpow_ofNat]; ring
  · rw [e7]; simp only [E10Fun, hE4, hE6, zpow_ofNat]; ring
  · rw [e8]; exact hDel
  · rw [e9]; simp only [E14Fun, hE4, hE6, zpow_ofNat]; ring
  · simp

/-- The modular `j`-invariant is `S`-invariant. -/
lemma kpc_jInvariant_S (τ : ℍ) : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ := by
  have h4 := kpc_smul_S_of_slash kpc_E4_slash_S τ
  have h12 := kpc_smul_S_of_slash kpc_Delta_slash_S τ
  have hΔ : DeltaFun τ ≠ 0 := by
    simpa [DeltaFun] using ModularForm.discriminant_ne_zero τ
  have hτ := kpc_tau_ne_zero τ
  simp only [jInvariantFun, h4, h12, zpow_ofNat]
  rw [div_eq_div_iff]
  · ring
  · exact mul_ne_zero (pow_ne_zero _ hτ) hΔ
  · exact hΔ

/-- The diagonal matrices `Π_v` transform under `S` by the diagonal matrix of the weights. -/
lemma kpc_PiMat_S (v : Fin 3 → ℤ) (τ : ℍ) :
    PiMat v (ModularGroup.S • τ) = Matrix.diagonal (fun i => (τ : ℂ) ^ (v i)) * PiMat v τ := by
  have h1 : PiMat v (ModularGroup.S • τ)
      = Matrix.diagonal (fun i => (τ : ℂ) ^ (v i) * fk (v i) τ) := by
    rw [PiMat]
    exact congr_arg Matrix.diagonal (funext fun i => kpc_fk_S (v i) τ)
  rw [h1]
  show Matrix.diagonal (fun i => (τ : ℂ) ^ (v i) * fk (v i) τ)
      = Matrix.diagonal (fun i => (τ : ℂ) ^ (v i)) * Matrix.diagonal (fun i => fk (v i) τ)
  rw [Matrix.diagonal_mul_diagonal]

/-- The entrywise transformation law of `Υ_+^{(d)}` under `τ ↦ S • τ`. -/
lemma kpc_UpsilonPlus_S (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    UpsilonPlus d (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ ((d : ℤ) / 2 + 2 - 2 * ((i : ℕ) : ℤ)) * UpsilonPlus d τ z i j := by
  have hJ : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ := kpc_jInvariant_S τ
  rcases hd with rfl | rfl
  · have hPi := kpc_PiMat_S (![6, 4, 2] : Fin 3 → ℤ) τ
    simp only [UpsilonPlus, reduceIte]
    rw [hJ, hPi]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
    rw [Matrix.diagonal_mul]
    have hai : (((![6, 4, 2] : Fin 3 → ℤ) i : ℤ)) = ((8 : ℕ) : ℤ) / 2 + 2 - 2 * ((i : ℕ) : ℤ) := by
      fin_cases i <;> norm_num
    rw [← hai]
    ring
  · have hPi := kpc_PiMat_S (![14, 12, 10] : Fin 3 → ℤ) τ
    simp only [UpsilonPlus, reduceIte]
    simp only [if_neg (show ¬((24 : ℕ) = 8) by decide)]
    rw [hJ, hPi]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
    rw [Matrix.diagonal_mul]
    have hai : (((![14, 12, 10] : Fin 3 → ℤ) i : ℤ)) = ((24 : ℕ) : ℤ) / 2 + 2 - 2 * ((i : ℕ) : ℤ) := by
      fin_cases i <;> norm_num
    rw [← hai]
    ring

/-! ## The main statement -/

/-- **`S`-invariance of the coefficient functions of `K_+^{(d)}`**: for `d = 8` and `d = 24`
and each `i : Fin 3`, the coefficient function `c_i^{(d)}(·,z) = KPlusCoeff d z i` is
invariant under the slash action of `S` in the weight `d/2 + 2 - 2i`. -/
theorem KPlusCoeff_slash_S (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) (i : Fin 3) :
    SlashAction.map ((d : ℤ) / 2 + 2 - 2 * ((i : ℕ) : ℤ)) ModularGroup.S
      (Work.Kernels.KPlusCoeff d z i) = Work.Kernels.KPlusCoeff d z i := by
  ext τ
  set k : ℤ := (d : ℤ) / 2 + 2 - 2 * ((i : ℕ) : ℤ) with hk
  show (Work.Kernels.KPlusCoeff d z i ∣[k] ModularGroup.S) τ = Work.Kernels.KPlusCoeff d z i τ
  rw [kpc_slash_S_apply]
  have hτ := kpc_tau_ne_zero τ
  have hsum : Work.Kernels.KPlusCoeff d z i (ModularGroup.S • τ)
      = (τ : ℂ) ^ k * Work.Kernels.KPlusCoeff d z i τ := by
    simp only [KPlusCoeff]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [kpc_UpsilonPlus_S d hd z i j τ, ← hk]
    ring
  rw [hsum]
  have hkk : (τ : ℂ) ^ k * (τ : ℂ) ^ (-k) = 1 := by
    rw [← zpow_add₀ hτ, add_neg_cancel, zpow_zero]
  calc ((τ : ℂ) ^ k * Work.Kernels.KPlusCoeff d z i τ) * (τ : ℂ) ^ (-k)
      = (τ : ℂ) ^ k * (τ : ℂ) ^ (-k) * Work.Kernels.KPlusCoeff d z i τ := by ring
    _ = 1 * Work.Kernels.KPlusCoeff d z i τ := by rw [hkk]
    _ = Work.Kernels.KPlusCoeff d z i τ := by ring

end Work.Kernels.KernelFacts
