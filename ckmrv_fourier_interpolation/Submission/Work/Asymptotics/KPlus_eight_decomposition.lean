import Mathlib
import Submission.Work.Kernels.All

namespace Work.Asymptotics

open Work.Kernels

/-! ## The explicit `d = 8` decomposition of `K_+`

Everything here is pure algebra: `K_+^{(8)}(τ,z)` is the matrix product
`φ⃗(τ)ᵗ · Υ_+^{(8)}(τ,z) · φ̃⃗(z)` and `Υ_+^{(8)}` is an explicit scalar multiple of a product
of two diagonal matrices and a fixed `3 × 3` matrix.  Expanding the double sum and clearing
the factor `(j(τ) − j(z))` yields the announced decomposition. -/

/-- Entry formula for a product `Π_a(τ) · M · Π_b(z)` of diagonal matrices with a matrix:
`(Π_a(τ) M Π_b(z))_{im} = f_{a i}(τ) · M_{im} · f_{b m}(z)`. -/
private lemma PiMat_mul_PiMat_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (τ z : UpperHalfPlane) (i m : Fin 3) :
    (PiMat a τ * M * PiMat b z) i m = fk (a i) τ * M i m * fk (b m) z := by
  simp only [PiMat, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- The pure field identity underlying the decomposition: after multiplying the scalar
`(C·Δ(z)·J)⁻¹` into the numerator and clearing the division by `Δ(τ)Δ(z)J`, both sides agree. -/
private lemma kplus8_alg (C Dτ Dz J A F P0 P1 P2 B W : ℂ) (hC : C ≠ 0) (hDτ : Dτ ≠ 0)
    (hDz : Dz ≠ 0) (hJ : J ≠ 0) :
    (C * Dz * J)⁻¹ * (J * A * Dz * P0 + (F / Dτ) * Dz * P0 - (B * P1) + W * P2)
      = C⁻¹ * (P0 * A + (F * Dz * P0 + Dτ * (W * P2 - (B * P1))) / (Dτ * Dz * J)) := by
  field_simp
  ring

/-- Explicit expansion of `K_+^{(8)}(τ,z)` from its definition as a double sum over the
vector `φ⃗(τ)`, the coefficient matrix `Υ_+^{(8)}` and the vector `φ̃⃗(z)`.  The three
non-trivial entries of the middle matrix `!![J,0,1; -2J,-2,0; 1,0,0]` produce the three
braces `(J·A + F/Δ(τ))`, `B`, `W` below. -/
private lemma KPlus_eight_expand (τ z : UpperHalfPlane) :
    KPlus 8 τ z =
      ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z
          * (jInvariantFun τ - jInvariantFun z))⁻¹ *
        ((jInvariantFun τ - jInvariantFun z) *
            ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ) * DeltaFun z * phitVec z 0
          + (phi2 τ * E14Fun τ / DeltaFun τ) * DeltaFun z * phitVec z 0
          - ((2 * phi0 τ * E4Fun τ) * E10Fun z * phitVec z 1)
          + ((τ : ℂ) * E6Fun τ) * E8Fun z * phitVec z 2) := by
  rw [KPlus,
    show UpsilonPlus 8 τ z =
      ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z
          * (jInvariantFun τ - jInvariantFun z))⁻¹ •
        (PiMat ![6, 4, 2] τ *
          !![jInvariantFun τ - jInvariantFun z, 0, 1;
             -2 * (jInvariantFun τ - jInvariantFun z), -2, 0; 1, 0, 0] *
          PiMat ![12, 10, 8] z) from rfl]
  simp only [Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three, PiMat_mul_PiMat_entry]
  simp only [phiVec, phitVec, phiNeg2, fk]
  simp
  ring_nf

theorem KPlus_eight_decomposition (τ z : UpperHalfPlane)
    (hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KPlus 8 τ z =
      ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
        (Work.Kernels.phitVec z 0 * ((τ : ℂ) * Work.Kernels.E6Fun τ
            - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ)
          + (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * Work.Kernels.DeltaFun z
              * Work.Kernels.phitVec z 0
              + Work.Kernels.DeltaFun τ * ((τ : ℂ) * Work.Kernels.E6Fun τ
                  * Work.Kernels.E8Fun z * Work.Kernels.phitVec z 2
                - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                  * Work.Kernels.E10Fun z * Work.Kernels.phitVec z 1))
            / (Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) := by
  have hDτ : DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hJ' : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr hJ
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hC : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by simp [hpi]
  rw [KPlus_eight_expand τ z]
  exact kplus8_alg ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) (DeltaFun τ)
    (DeltaFun z) (jInvariantFun τ - jInvariantFun z)
    ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ) (phi2 τ * E14Fun τ)
    (phitVec z 0) (phitVec z 1) (phitVec z 2)
    ((2 * phi0 τ * E4Fun τ) * E10Fun z) (((τ : ℂ) * E6Fun τ) * E8Fun z)
    hC hDτ hDz hJ'

end Work.Asymptotics
