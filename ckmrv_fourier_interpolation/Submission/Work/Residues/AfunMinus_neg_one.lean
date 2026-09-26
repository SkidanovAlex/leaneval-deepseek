/-
# The cleared `K_-` kernel at the pole `τ = z - 1 = T⁻¹z`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) Section 8 needs
the residues of the kernel `K = (K_+ + K_-)/2` at the two translates `z ± 1` of the diagonal
point: the paper records that `K(·,z)` "has poles at `z+1` and `z-1` with residues `-1/(2π)`
and `1/(2π)`".  In the normalisation of this workspace the value of the *cleared* kernel
`AfunMinus ℓ d z τ = KMinusClear ℓ d τ z / (Δ(τ)Δ(z)^e)` at a pole `σ = γz` of the orbit of
`z` is `(1/(2π))·j'(z)·(-φ_-(γ))`; here we prove the case `σ = z - 1 = T⁻¹z`, i.e.

  `AfunMinus ℓ d z (T⁻¹z) = (1/(2π))·j'(z)`.

## Method

Rather than computing the explicit value of `KMinusClear` at `τ = z - 1` (which would require
the `T⁻¹`-transformation of the whole `ψ⃗`-vector, in particular of `ξ₂𝓛 + (ξ₂|₂S)𝓛_S`), we
use the *functional equation* `(T - I)² K_- = 0` of Theorem 4.9(2).  In its cleared form it
says that the holomorphic function `τ ↦ KMinusClear ℓ d τ z` satisfies the second difference
equation

  `F(τ+2) - 2F(τ+1) + F(τ) = 0`

(`Work.Residues.AfunMinusNegOne.KMinusClear_T2`).  Together with the two values already
computed in the library, `KMinusClear ℓ d z z = 0` (`Work.Residues.KMinusClear_diag`) and
`KMinusClear ℓ d (Tz) z = (iE₄²E₆/Δ)(z)·Δ(Tz)Δ(z)^e` (`Work.Residues.KMinusClear_T`), this
gives `KMinusClear ℓ d (z-1) z = - KMinusClear ℓ d (z+1) z`, hence

  `AfunMinus ℓ d z (z-1) = - AfunMinus ℓ d z (z+1) = (1/(2π))j'(z)`

by `Work.Residues.AfunMinus_vadd_one_eq`.  The argument is uniform in `z`; in particular the
elliptic points `j'(z) = 0` need no separate treatment.

## Main results

* `Work.Residues.AfunMinusNegOne.KMinusClear_T2` :
  `τ ↦ KMinusClear ℓ d τ z` is killed by `(T-I)²`.
* `Work.Residues.AfunMinus_neg_one` :
  `AfunMinus ℓ d z ((-1) +ᵥ z) = (1/(2π))·j'(z)`.
-/
import Mathlib
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Kernels.KernelFacts.KMinus_T2
import Submission.Work.Kernels.KernelFacts.KPlus_T2

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Residues

open Work.Kernels

namespace AfunMinusNegOne

/-! ## The coefficient function of the cleared kernel -/

/-- The `i`-th coefficient of `KMinusClear ℓ d · z` in the basis `ψ⃗`: the function
`τ ↦ ∑_j Υ_-^{(d),cl}(τ,z)_{ij} ψ̃_j(z)`.  It is `T`-periodic in `τ`. -/
def KMinusClearCoeff (ℓ : LogLambdaData) (d : ℕ) (z : ℍ) (i : Fin 3) (τ : ℍ) : ℂ :=
  ∑ j : Fin 3, UpsilonMinusClear d τ z i j * psitVec ℓ z j

lemma KMinusClear_eq_sum (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) :
    KMinusClear ℓ d τ z = ∑ i : Fin 3, psiVec ℓ τ i * KMinusClearCoeff ℓ d z i τ := by
  simp only [KMinusClear, KMinusClearCoeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ## `T`-periodicity of the cleared coefficient matrix -/

lemma PiMatDelta_vadd_one (v : Fin 3 → ℤ) (τ : ℍ) :
    PiMatDelta v ((1 : ℝ) +ᵥ τ) = PiMatDelta v τ := by
  unfold PiMatDelta
  simp only [KernelFacts.fk_vadd_one, KernelFacts.DeltaFun_vadd_one]

lemma UpsilonMinusClear_vadd_one (d : ℕ) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    UpsilonMinusClear d ((1 : ℝ) +ᵥ τ) z i j = UpsilonMinusClear d τ z i j := by
  simp only [UpsilonMinusClear]
  split_ifs with h8 h24 <;>
    simp only [PiMatDelta_vadd_one, KernelFacts.jInvariantFun_vadd_one]

lemma KMinusClearCoeff_vadd_one (ℓ : LogLambdaData) (d : ℕ) (z : ℍ) (i : Fin 3) (τ : ℍ) :
    KMinusClearCoeff ℓ d z i ((1 : ℝ) +ᵥ τ) = KMinusClearCoeff ℓ d z i τ := by
  unfold KMinusClearCoeff
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [UpsilonMinusClear_vadd_one]

/-! ## The cleared kernel satisfies the same difference equation as `K_-` -/

/-- **`(T-I)²` kills the cleared kernel `τ ↦ KMinusClear ℓ d τ z`.**  This is the cleared form
of `Work.Kernels.KernelFacts.KMinus_T2`: the coefficient matrix `Υ_-^{cl}(τ,z)` is
`T`-periodic in `τ`, and the basis vector `ψ⃗` is killed by `(T-I)²`
(`Work.Kernels.KernelFacts.psiVec_T2_km`). -/
theorem KMinusClear_T2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun τ : ℍ => KMinusClear ℓ d τ z) = 0 := by
  have _ := hd
  have h1 : (fun τ : ℍ => KMinusClear ℓ d τ z)
      = ∑ i : Fin 3, (fun τ : ℍ => psiVec ℓ τ i * KMinusClearCoeff ℓ d z i τ) := by
    funext τ
    simp only [Finset.sum_apply]
    exact KMinusClear_eq_sum ℓ d τ z
  rw [h1]
  rw [show (∑ i : Fin 3, (fun τ : ℍ => psiVec ℓ τ i * KMinusClearCoeff ℓ d z i τ))
      = ∑ i ∈ Finset.univ,
          (fun τ : ℍ => psiVec ℓ τ i * KMinusClearCoeff ℓ d z i τ) from rfl]
  refine T2op_sum Finset.univ (fun i _ => ?_)
  exact T2op_mul_of (KernelFacts.psiVec_T2_km ℓ i)
    (fun τ => KMinusClearCoeff_vadd_one ℓ d z i τ)

/-! ## The value at `τ = z - 1` -/

/-- The point `T⁻¹z = z - 1 = (-1) +ᵥ z`. -/
lemma vadd_neg_one_add_one (z : ℍ) : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z := by
  rw [← vadd_assoc]; norm_num

lemma vadd_neg_one_add_two (z : ℍ) :
    (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = (1 : ℝ) +ᵥ z := by
  rw [← vadd_assoc]; norm_num

/-- `Δ(z - 1) = Δ(z)`. -/
lemma DeltaFun_vadd_neg_one (z : ℍ) : DeltaFun ((-1 : ℝ) +ᵥ z) = DeltaFun z := by
  rw [← KernelFacts.DeltaFun_vadd_one ((-1 : ℝ) +ᵥ z), vadd_neg_one_add_one]

/-- The cleared kernel at `τ = z - 1` is the negative of its value at `τ = z + 1`: the
difference equation `KMinusClear(τ+2) - 2KMinusClear(τ+1) + KMinusClear(τ) = 0` at `τ = z-1`,
together with `KMinusClear ℓ d z z = 0`. -/
lemma KMinusClear_vadd_neg_one (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KMinusClear ℓ d ((-1 : ℝ) +ᵥ z) z = - KMinusClear ℓ d ((1 : ℝ) +ᵥ z) z := by
  have hT2 := congr_fun (KMinusClear_T2 ℓ d hd z) ((-1 : ℝ) +ᵥ z)
  simp only [T2op, Pi.zero_apply] at hT2
  rw [vadd_neg_one_add_two, vadd_neg_one_add_one, KMinusClear_diag ℓ d hd z] at hT2
  simp only [mul_zero, sub_zero] at hT2
  linear_combination hT2

/-- `AfunMinus ℓ d z (z-1) = - AfunMinus ℓ d z (z+1)`. -/
lemma AfunMinus_vadd_neg_one_eq_neg (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    AfunMinus ℓ d z ((-1 : ℝ) +ᵥ z) = - AfunMinus ℓ d z ((1 : ℝ) +ᵥ z) := by
  have hK := KMinusClear_vadd_neg_one ℓ d hd z
  simp only [AfunMinus]
  rw [hK, DeltaFun_vadd_neg_one z, KernelFacts.DeltaFun_vadd_one z]
  ring

end AfunMinusNegOne

/-- **The cleared kernel `K_-` at the pole `τ = z - 1`.**  The residue of `K_-^{(d)}(·,z)` at
`z - 1 = T⁻¹z` is `-(1/2π)φ_-(T⁻¹) = 1/(2π)`, so the value of the cleared kernel divided by
`Δ(τ)Δ(z)^e` is `(1/(2π))j'(z)`; this is the companion of
`Work.Residues.AfunMinus_vadd_one_eq`, which handles `τ = z + 1`. -/
theorem AfunMinus_neg_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Residues.AfunMinus ℓ d z ((-1 : ℝ) +ᵥ z) = (1 / (2 * Real.pi)) * Work.Residues.jprime z := by
  rw [AfunMinusNegOne.AfunMinus_vadd_neg_one_eq_neg ℓ d hd z, AfunMinus_vadd_one_eq ℓ d hd z,
    jprime_vadd_one]
  ring

end Work.Residues
