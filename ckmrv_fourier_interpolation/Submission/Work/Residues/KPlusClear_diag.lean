import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Kernels.PhiAnnihilation

namespace Work.Residues

open Work.Kernels UpperHalfPlane Matrix

/-! ## The value of the coefficient matrix `Υ_+` on the diagonal

On the diagonal `τ = z` the factor `j(τ) - j(z)` vanishes and the three nonzero entries of
the middle matrix of `Υ_+^{(d)}` are `1`, `-2`, `1`, so that the whole product collapses to a
scalar multiple of the fixed matrix `!![0,0,1; 0,-2,0; 1,0,0]`.

The key point for the vanishing of `K_+^{clear}` on the diagonal is then that the vector
`(φ_{-2}, φ_0, φ_2)` evaluated in this matrix against `(φ̃_{-2}, φ̃_0, φ̃_2)` gives

  `z² · (z (E₂-E₂|₂S)² - (6i/π)(E₂-E₂|₂S))`,

which vanishes by the transformation law `z(E₂(z) - (E₂|₂S)(z)) = 6i/π` of `E₂`
(CKMRV (2.8), `Work.Kernels.TildeFacts.E2S_eq`). -/

/-- The entries of `Δ(τ)·Π_{k₁,k₂,k₃}(τ)` multiplied into a matrix. -/
private lemma PiMatDelta_mul_PiMat_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (τ z : UpperHalfPlane) (i m : Fin 3) :
    (PiMatDelta a τ * M * PiMat b z) i m
      = (DeltaFun τ * fk (a i) τ) * M i m * fk (b m) z := by
  simp only [PiMatDelta, PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- The entries of `Δ(τ)·Π_{k₁,k₂,k₃}(τ)` multiplied into a matrix and into a scalar multiple
of `Π_{l₁,l₂,l₃}(z)` (the shape occurring for `d = 24`). -/
private lemma PiMatDelta_mul_smul_PiMat_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (c : ℂ) (τ z : UpperHalfPlane) (i m : Fin 3) :
    (PiMatDelta a τ * M * (c • PiMat b z)) i m
      = (DeltaFun τ * fk (a i) τ) * M i m * (c * fk (b m) z) := by
  rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_PiMat_entry]
  ring

/-- `Δ` does not vanish. -/
private lemma DeltaFun_ne_zero' (z : UpperHalfPlane) : DeltaFun z ≠ 0 := by
  simpa [DeltaFun] using ModularForm.discriminant_ne_zero z

/-- **`Υ_+^{(8)}` on the diagonal.** Since `j(τ) - j(z) = 0` there, the middle matrix becomes
`!![0,0,1; 0,-2,0; 1,0,0]` and the entries of the product are all the same modular form
`Δ(z)E₁₄(z)`. -/
private lemma UpsilonPlusClear_self_8 (z : UpperHalfPlane) :
    UpsilonPlusClear 8 z z
      = (((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ * (DeltaFun z * E14Fun z))
        • (!![0, 0, 1; 0, -2, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [show UpsilonPlusClear 8 z z = ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ •
      (PiMatDelta ![6, 4, 2] z *
        !![jInvariantFun z - jInvariantFun z, 0, 1;
           -2 * (jInvariantFun z - jInvariantFun z), -2, 0; 1, 0, 0] *
        PiMat ![12, 10, 8] z) from rfl]
  have hΔ : DeltaFun z ≠ 0 := DeltaFun_ne_zero' z
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_PiMat_entry, sub_self]
      simp [fk, E8Fun, E10Fun, E14Fun]
      try field_simp
      try ring

/-- **`Υ_+^{(24)}` on the diagonal.** The same collapse as for `d = 8`, with the entries
`Δ(z)²E₁₄(z)` in place of `Δ(z)E₁₄(z)`. -/
private lemma UpsilonPlusClear_self_24 (z : UpperHalfPlane) :
    UpsilonPlusClear 24 z z
      = (((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
          (c1728 * (DeltaFun z) ^ 2 * E14Fun z))
        • (!![0, 0, 1; 0, -2, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [show UpsilonPlusClear 24 z z =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ •
      (PiMatDelta ![14, 12, 10] z *
        !![6 * (jInvariantFun z - jInvariantFun z), 0,
            c1728 - 6 * (jInvariantFun z - jInvariantFun z);
           -12 * jInvariantFun z * (jInvariantFun z - jInvariantFun z) +
              5 * c1728 * (jInvariantFun z - jInvariantFun z), -2 * c1728,
            12 * jInvariantFun z * (jInvariantFun z - jInvariantFun z) -
              7 * c1728 * (jInvariantFun z - jInvariantFun z);
           c1728 + 6 * (jInvariantFun z - jInvariantFun z), 0,
             -6 * (jInvariantFun z - jInvariantFun z)] *
        (DeltaFun z • PiMat ![4, 2, 0] z)) from rfl]
  have hΔ : DeltaFun z ≠ 0 := DeltaFun_ne_zero' z
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_smul_PiMat_entry, sub_self]
      simp [fk, E10Fun, E14Fun, c1728]
      try field_simp
      try ring

/-- The diagonal pairing of `φ⃗(z)`, the residue matrix `!![0,0,1; 0,-2,0; 1,0,0]` and
`φ̃⃗(z)`, written in terms of `φ_0`, `φ_2`. -/
private lemma sum_KRes (κ : ℂ) (z : UpperHalfPlane) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        phiVec z i * (κ • (!![0, 0, 1; 0, -2, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ)) i j
          * phitVec z j)
      = κ * ((z : ℂ) ^ 2 * ((z : ℂ) * E2S z ^ 2 - 2 * phi0 z * E2S z + phi2 z)) := by
  simp only [Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three, phiVec, phitVec]
  simp only [phiNeg2]
  simp
  ring

/-- **The vanishing of the residue bracket.** Using `z(E₂(z) - (E₂|₂S)(z)) = 6i/π`, the
diagonal pairing of the log-derivative basis against the residue matrix is zero. -/
private lemma diag_bracket (z : UpperHalfPlane) :
    (z : ℂ) ^ 2 * ((z : ℂ) * E2S z ^ 2 - 2 * phi0 z * E2S z + phi2 z) = 0 := by
  have hz : (z : ℂ) ≠ 0 := fun h => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h]; simp)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Work.Kernels.TildeFacts.E2S_eq z]
  simp only [phi0, phi2]
  field_simp
  ring

/-- **The cleared kernel `K_+` vanishes on the diagonal `τ = z`** (the residue of `K_+` at
`τ = z` is zero, since `φ_+(1) = 0`). -/
theorem KPlusClear_diag (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Kernels.KPlusClear d z z = 0 := by
  rcases hd with rfl | rfl
  · rw [KPlusClear, UpsilonPlusClear_self_8 z, sum_KRes, diag_bracket z, mul_zero]
  · rw [KPlusClear, UpsilonPlusClear_self_24 z, sum_KRes, diag_bracket z, mul_zero]

end Work.Residues
