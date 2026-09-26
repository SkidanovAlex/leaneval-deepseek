import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs

namespace Work.Asymptotics

open Work.Kernels Matrix
open scoped UpperHalfPlane

noncomputable section

/-!
## The identity `Ξ₂₄(τ,z) = 36·1728·π⁻²·i · Δ(z)(j(τ)−j(z)) · z¹⁰ · K₊^{(24)}(τ, S·z)`

`Ξ₂₄` is defined as a double sum of products of `φ⃗(τ)`, the `f_k`'s and the entries of an
explicit matrix.  The same product is obtained by expanding `K₊^{(24)}(τ, S·z)`: the matrices
`Υ₊^{(24)}` and `Ξ₂₄` differ exactly by the prefactor `(36·1728·π⁻²·i·Δ(z)(j(τ)−j(z)))⁻¹` and
by the transformation laws `f_k(S·z) = z^k f_k(z)`, `Δ(S·z) = z¹²Δ(z)`, `j(S·z) = j(z)` of the
`S`-translations, together with `φ̃_j(S·z) z² = z^{2j}E₂(z)^j` (`phitVec_S_smul`).
-/

/-- The matrix with entries `N_{ij}` appearing in the definition of `Ξ₂₄` (i.e. `J • M` where
`M` is the middle matrix of `Υ₊^{(24)}` and `J = j(τ) - j(z)`). -/
def Xi24Mat (jτ J : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![6 * J, 0, c1728 - 6 * J;
     -12 * jτ * J + 5 * c1728 * J, -2 * c1728, 12 * jτ * J - 7 * c1728 * J;
     c1728 + 6 * J, 0, -6 * J]

/-- The middle matrix of `Υ₊^{(24)}` (with `(j(τ)−j(z))⁻¹` left uncovered). -/
def XUpsilonMat24 (jτ J : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![6, 0, c1728 * J⁻¹ - 6;
     -12 * jτ + 5 * c1728, -2 * c1728 * J⁻¹, 12 * jτ - 7 * c1728;
     c1728 * J⁻¹ + 6, 0, -6]

/-- Unfolding of `Ξ₂₄` into its defining double sum. -/
lemma Xi24_eq_sum (τ z : UpperHalfPlane) :
    Xi24 τ z = ∑ i : Fin 3, ∑ m : Fin 3,
      phiVec τ i * fk ((![14, 12, 10] : Fin 3 → ℤ) i) τ *
        Xi24Mat (jInvariantFun τ) (jInvariantFun τ - jInvariantFun z) i m *
        fk ((![4, 2, 0] : Fin 3 → ℤ) m) z * E2Fun z ^ (m : ℕ) := rfl

/-- Unfolding of `Υ₊^{(24)}` into the product of the three matrices. -/
lemma UpsilonPlus24_eq (τ z : UpperHalfPlane) :
    UpsilonPlus 24 τ z =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ •
        (PiMat (![14, 12, 10] : Fin 3 → ℤ) τ *
          XUpsilonMat24 (jInvariantFun τ) (jInvariantFun τ - jInvariantFun z) *
          PiMat (![4, 2, 0] : Fin 3 → ℤ) z) := rfl

/-- `XUpsilonMat24` is `(j(τ)−j(z))⁻¹` times `Xi24Mat`: the entries of `Υ₊^{(24)}` are the
entries of the matrix of `Ξ₂₄`, each divided by `j(τ)−j(z)`. -/
lemma XUpsilonMat24_eq (jτ J : ℂ) (hJ : J ≠ 0) :
    XUpsilonMat24 jτ J = J⁻¹ • Xi24Mat jτ J := by
  ext i m
  fin_cases i <;> fin_cases m <;>
    simp [XUpsilonMat24, Xi24Mat, Matrix.smul_apply] <;> field_simp

/-- The `(i,m)` entry of `Π_a(x) · M · Π_b(y)`. -/
lemma PiMat_mul_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (x y : UpperHalfPlane) (i m : Fin 3) :
    (PiMat a x * M * PiMat b y) i m = fk (a i) x * M i m * fk (b m) y := by
  simp only [PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- The key scalar identity: `z⁻² f_k(S·z) φ̃_j(S·z) = f_k(z) E₂(z)^j` for the weights
`k = 4 - 2j` of the second `Π`-matrix of `Υ₊^{(24)}`.  It combines the transformation laws
`f_k(S·z) = z^k f_k(z)` with `φ̃_j(S·z) z² = z^{2j}E₂(z)^j`. -/
lemma fk_phitVec_S_smul (z : UpperHalfPlane) (j : Fin 3) :
    (z : ℂ) ^ (-2 : ℤ) * fk ((![4, 2, 0] : Fin 3 → ℤ) j) (ModularGroup.S • z) *
        phitVec (ModularGroup.S • z) j
      = fk ((![4, 2, 0] : Fin 3 → ℤ) j) z * E2Fun z ^ (j : ℕ) := by
  have hz : (z : ℂ) ≠ 0 := fun hh => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, hh]; simp)
  have h := phitVec_S_smul z j
  have h2 : phitVec (ModularGroup.S • z) j =
      (z : ℂ) ^ (2 * (j : ℕ)) * E2Fun z ^ (j : ℕ) * ((z : ℂ) ^ 2)⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hz), mul_one]
  rw [Work.Kernels.KernelFacts.fk_S_smul ((![4, 2, 0] : Fin 3 → ℤ) j)
    (by fin_cases j <;> simp) z, h2]
  fin_cases j <;> norm_num <;> field_simp

/-- `Ξ₂₄(τ,z)` equals the expression obtained by expanding the kernel `K₊^{(24)}` at `S·z`:
the residue/first-order asymptotics identity of CKMRV Theorem 1.9(2) for `d = 24`. -/
theorem Xi24_eq (τ z : UpperHalfPlane)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) *
        (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
        ((z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)) =
      Work.Asymptotics.Xi24 τ z := by
  have hz : (z : ℂ) ≠ 0 := fun hh => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, hh]; simp)
  have hJ0 : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr h
  have hJul : jInvariantFun (ModularGroup.S • z) = jInvariantFun z :=
    Work.Kernels.KernelFacts.jInvariantFun_S_smul z
  have hDel : DeltaFun (ModularGroup.S • z) = (z : ℂ) ^ 12 * DeltaFun z :=
    Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.DeltaFun_S_slash z
  have hDz : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hC : (36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by simp [c1728])) ?_)
      Complex.I_ne_zero
    exact zpow_ne_zero _ ((Complex.ofReal_ne_zero).mpr Real.pi_ne_zero)
  rw [Xi24_eq_sum,
    show KPlus 24 τ (ModularGroup.S • z) =
      ∑ i, ∑ j, phiVec τ i * UpsilonPlus 24 τ (ModularGroup.S • z) i j *
        phitVec (ModularGroup.S • z) j from rfl,
    UpsilonPlus24_eq τ (ModularGroup.S • z), hJul, hDel,
    XUpsilonMat24_eq (jInvariantFun τ) (jInvariantFun τ - jInvariantFun z) hJ0]
  set J := jInvariantFun τ - jInvariantFun z with hJdef
  have hJ : J ≠ 0 := by rw [hJdef]; exact hJ0
  set D := (36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hDdef
  have hD : D ≠ 0 := by rw [hDdef]; exact hC
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, Finset.mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [PiMat_mul_entry]
  simp only [mul_assoc] at *
  rw [← fk_phitVec_S_smul z j]
  field_simp

end

end Work.Asymptotics
