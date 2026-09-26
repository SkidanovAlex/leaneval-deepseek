/-
# The residue theorem of CKMRV Theorem 4.9(3) for `K` and `K̂`

The kernels `K = (K_+ + K_-)/2` and `K̂ = (K_+ - K_-)/2` are the ones used to build the
generating functions `F` and `F̃` of Section 5.  Since `K` and `K̂` are linear combinations of
`K_±`, their residues follow from `Work.Residues.hasResidue_slash_KPlus`,
`Work.Residues.hasResidue_slash_KMinus` and the relation
`φ = (φ_+ + φ_-)/2` between the functionals of CKMRV (3.12).

## Main results

* `Work.Residues.hasResidue_slash_Kfun` : for `r ∈ R` the function
  `τ ↦ (K^{(d)}|^τ_{d/2}r)(τ,z)` has residue `-(1/2π)φ(r)` at `τ = z`.
* `Work.Residues.hasResidue_slash_Khat` : the same for `K̂`, with residue `-(1/2π)·(φ_+ - φ_-)(r)/2`.
-/
import Mathlib
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Kernels.Theorem31

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-! ## `K` and `K̂` as linear combinations of `K_±` -/

/-- `Kfun = (K_+ + K_-)/2` pointwise. -/
lemma Kfun_eq_smul (ℓ : LogLambdaData) (d : ℕ) (z : ℍ) :
    (fun τ : ℍ => Kfun ℓ d τ z)
      = fun τ : ℍ => (1 / 2 : ℂ) * KPlus d τ z + (1 / 2 : ℂ) * KMinus ℓ d τ z := by
  funext τ
  simp only [Kfun]
  ring

/-- `Khat = (K_+ - K_-)/2` pointwise. -/
lemma Khat_eq_smul (ℓ : LogLambdaData) (d : ℕ) (z : ℍ) :
    (fun τ : ℍ => Khat ℓ d τ z)
      = fun τ : ℍ => (1 / 2 : ℂ) * KPlus d τ z - (1 / 2 : ℂ) * KMinus ℓ d τ z := by
  funext τ
  simp only [Khat]
  ring

/-- The group-algebra action on `K` is the average of the actions on `K_±`. -/
lemma slash_Kfun (ℓ : LogLambdaData) (d : ℕ) (k : ℤ) (r : R) (z : ℍ) :
    slash k r (fun σ : ℍ => Kfun ℓ d σ z)
      = fun τ : ℍ => (1 / 2 : ℂ) * slash k r (fun σ : ℍ => KPlus d σ z) τ
          + (1 / 2 : ℂ) * slash k r (fun σ : ℍ => KMinus ℓ d σ z) τ := by
  rw [Kfun_eq_smul ℓ d z]
  rw [show (fun τ : ℍ => (1 / 2 : ℂ) * KPlus d τ z + (1 / 2 : ℂ) * KMinus ℓ d τ z)
      = (1 / 2 : ℂ) • ((fun σ : ℍ => KPlus d σ z) + (fun σ : ℍ => KMinus ℓ d σ z)) by
    funext τ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  rw [slash_smul_F, slash_add_F]
  funext τ
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- The group-algebra action on `K̂` is the half-difference of the actions on `K_±`. -/
lemma slash_Khat (ℓ : LogLambdaData) (d : ℕ) (k : ℤ) (r : R) (z : ℍ) :
    slash k r (fun σ : ℍ => Khat ℓ d σ z)
      = fun τ : ℍ => (1 / 2 : ℂ) * slash k r (fun σ : ℍ => KPlus d σ z) τ
          - (1 / 2 : ℂ) * slash k r (fun σ : ℍ => KMinus ℓ d σ z) τ := by
  rw [Khat_eq_smul ℓ d z]
  rw [show (fun τ : ℍ => (1 / 2 : ℂ) * KPlus d τ z - (1 / 2 : ℂ) * KMinus ℓ d τ z)
      = ((1 / 2 : ℂ) • (fun σ : ℍ => KPlus d σ z)) + ((-(1 / 2) : ℂ) • (fun σ : ℍ => KMinus ℓ d σ z)) by
    funext τ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  rw [slash_add_F, slash_smul_F, slash_smul_F]
  funext τ
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-! ## The residue theorems -/

/-- **Theorem 4.9(3) for `K = (K_+ + K_-)/2`.**  For every `r ∈ R` and every `z` with
`j'(z) ≠ 0`, the function `τ ↦ (K^{(d)}|^τ_{d/2}r)(τ,z)` has at `τ = z` at most a simple pole
with residue `-(1/2π)φ(r)`. -/
theorem hasResidue_slash_Kfun (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) (r : R) :
    HasResidue (slash ((d : ℤ) / 2) r (fun σ : ℍ => Kfun ℓ d σ z)) z
      (-(1 / (2 * Real.pi)) * phi r) := by
  have hplus := hasResidue_slash_KPlus d hd z hne r
  have hminus := hasResidue_slash_KMinus ℓ d hd z hne r
  have hsum : HasResidue (fun τ : ℍ =>
      (1 / 2 : ℂ) * slash ((d : ℤ) / 2) r (fun σ : ℍ => KPlus d σ z) τ
        + (1 / 2 : ℂ) * slash ((d : ℤ) / 2) r (fun σ : ℍ => KMinus ℓ d σ z) τ) z
      ((1 / 2 : ℂ) * (-(1 / (2 * Real.pi)) * phiPlus r)
        + (1 / 2 : ℂ) * (-(1 / (2 * Real.pi)) * phiMinus r)) :=
    (hplus.const_mul (1 / 2)).add (hminus.const_mul (1 / 2))
  rw [← slash_Kfun ℓ d ((d : ℤ) / 2) r z] at hsum
  convert hsum using 1
  rw [phi_eq_half_phiPlus_add_phiMinus r]
  ring

/-- **Theorem 4.9(3) for `K̂ = (K_+ - K_-)/2`**: the residue at `τ = z` is
`-(1/2π)·(φ_+ - φ_-)(r)/2`. -/
theorem hasResidue_slash_Khat (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) (r : R) :
    HasResidue (slash ((d : ℤ) / 2) r (fun σ : ℍ => Khat ℓ d σ z)) z
      (-(1 / (2 * Real.pi)) * ((phiPlus r - phiMinus r) / 2)) := by
  have hplus := hasResidue_slash_KPlus d hd z hne r
  have hminus := hasResidue_slash_KMinus ℓ d hd z hne r
  have hsum : HasResidue (fun τ : ℍ =>
      (1 / 2 : ℂ) * slash ((d : ℤ) / 2) r (fun σ : ℍ => KPlus d σ z) τ
        - (1 / 2 : ℂ) * slash ((d : ℤ) / 2) r (fun σ : ℍ => KMinus ℓ d σ z) τ) z
      ((1 / 2 : ℂ) * (-(1 / (2 * Real.pi)) * phiPlus r)
        - (1 / 2 : ℂ) * (-(1 / (2 * Real.pi)) * phiMinus r)) :=
    (hplus.const_mul (1 / 2)).sub (hminus.const_mul (1 / 2))
  rw [← slash_Khat ℓ d ((d : ℤ) / 2) r z] at hsum
  convert hsum using 1
  ring

/-! ## `K` is annihilated by `𝓘` -/

lemma Kfun_slash_eq_zero_of_mem_idealI (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) {x : R} (hx : x ∈ idealI) :
    slash ((d : ℤ) / 2) x (fun σ : ℍ => Kfun ℓ d σ z) = 0 := by
  rw [slash_Kfun ℓ d ((d : ℤ) / 2) x z,
    KPlus_slash_eq_zero_of_mem_idealIp d hd z (idealI_le_idealIp hx),
    KMinus_slash_eq_zero_of_mem_idealIm ℓ d hd z (idealI_le_idealIm hx)]
  funext τ
  simp

lemma Khat_slash_eq_zero_of_mem_idealI (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) {x : R} (hx : x ∈ idealI) :
    slash ((d : ℤ) / 2) x (fun σ : ℍ => Khat ℓ d σ z) = 0 := by
  rw [slash_Khat ℓ d ((d : ℤ) / 2) x z,
    KPlus_slash_eq_zero_of_mem_idealIp d hd z (idealI_le_idealIp hx),
    KMinus_slash_eq_zero_of_mem_idealIm ℓ d hd z (idealI_le_idealIm hx)]
  funext τ
  simp

/-- The generator `S(T-I)²` of `𝓘` annihilates `K`; this is the kernel identity behind the
second recurrence of CKMRV Proposition 5.1 (`h5b`). -/
lemma Kfun_slash_S_T2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2) (fun σ : ℍ => Kfun ℓ d σ z) = 0 := by
  refine Kfun_slash_eq_zero_of_mem_idealI ℓ d hd z ?_
  rw [idealI]
  exact Submodule.mem_sup_left (mem_span2.mpr ⟨0, 1, by rw [mul_zero, zero_add, mul_one]⟩)

/-- The pointwise kernel identity behind `h5b`, in the `t`-variable of the contour integral. -/
lemma Kaxis_Kfun_slash_S_T2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (t : ℝ) :
    slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2) (fun σ : ℍ => Kaxis (Kfun ℓ d) σ t) = 0 := by
  by_cases ht : 0 < t
  · ext σ
    simp only [Kaxis, dif_pos ht]
    exact congr_fun (Kfun_slash_S_T2 ℓ d hd (imagAxis t ht)) σ
  · ext σ
    simp only [Kaxis, dif_neg ht]
    exact congr_fun (AlgebraFacts.slash_mul_aux_zero ((d : ℤ) / 2)
      (R_S * (R_T - 1) ^ 2)) σ

/-- The kernel `K = (K_+ + K_-)/2` is annihilated by `(T-I)²` in the `τ` variable (Theorem
4.9(2)), in the explicit form used throughout Section 5. -/
theorem Kfun_T2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun σ : ℍ => Kfun ℓ d σ z) = 0 := by
  have h : (fun σ : ℍ => Kfun ℓ d σ z)
      = fun σ : ℍ => (1 / 2 : ℂ) * KPlus d σ z + (1 / 2 : ℂ) * KMinus ℓ d σ z :=
    Kfun_eq_smul ℓ d z
  rw [h]
  have hp := KernelFacts.KPlus_T2 d hd z
  have hm := KernelFacts.KMinus_T2 ℓ d hd z
  ext τ
  have h1 := congr_fun hp τ
  have h2 := congr_fun hm τ
  simp only [T2op, Pi.zero_apply] at h1 h2 ⊢
  linear_combination (1 / 2) * h1 + (1 / 2) * h2

end Work.Residues
