import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.KPlusCoeff_slash_S
import Submission.Work.Kernels.KernelFacts.fk_slash
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Residues

open Work.Kernels

/-! ## Entrywise form of the cleared coefficient matrices

The cleared matrix `Υ_+^{clear}` is `Π^Δ_a(τ)·M·Π_b(z)` (for `d = 8`) resp.
`Π^Δ_a(τ)·M·(Δ(z) • Π_b(z))` (for `d = 24`), where `Π` is diagonal.  Multiplying by a
diagonal matrix on the left (right) multiplies the `i`-th row (`j`-th column) by `a_i(τ)`
(`b_j(z)`), so the entries are the three-fold products stated below. -/

/-- The `(i,j)` entry of `Π^Δ_a(τ) · M · Π_b(z)`. -/
lemma PiMatDelta_mul_PiMat_apply (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (τ z : UpperHalfPlane) (i j : Fin 3) :
    (PiMatDelta a τ * M * PiMat b z) i j =
      (DeltaFun τ * fk (a i) τ) * M i j * fk (b j) z := by
  rw [PiMatDelta, PiMat, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- The `(i,j)` entry of `Π^Δ_a(τ) · M · (Δ(z) • Π_b(z))`. -/
lemma PiMatDelta_mul_smul_PiMat_apply (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (τ z : UpperHalfPlane) (i j : Fin 3) :
    (PiMatDelta a τ * M * (DeltaFun z • PiMat b z)) i j =
      (DeltaFun τ * fk (a i) τ) * M i j * (DeltaFun z * fk (b j) z) := by
  rw [PiMatDelta, PiMat, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-! ## Expansion of the cleared kernel when `j(τ) = j(z)`

At a point with `j(τ) = j(z)` the matrix `M` occurring in `Υ_+^{clear}` has the three
non-zero entries `M_{0,2}, M_{1,1}, M_{2,0}`, so the double sum collapses to three terms. -/

/-- The expansion of `K_+^{clear}` for `d = 8` at a point with `j(τ) = j(z)`. -/
lemma KPlusClear_expand_eight (τ z : UpperHalfPlane)
    (hJ : jInvariantFun τ = jInvariantFun z) :
    KPlusClear 8 τ z =
      ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
        ( phiNeg2 τ * (DeltaFun τ * fk (6 : ℤ) τ) * fk (8 : ℤ) z * ((z : ℂ) ^ 2 * E2S z ^ 2)
        - 2 * phi0 τ * (DeltaFun τ * fk (4 : ℤ) τ) * fk (10 : ℤ) z * ((z : ℂ) ^ 2 * E2S z)
        + phi2 τ * (DeltaFun τ * fk (2 : ℤ) τ) * fk (12 : ℤ) z * ((z : ℂ) ^ 2) ) := by
  have hU : ∀ i j : Fin 3, UpsilonPlusClear 8 τ z i j =
      ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
        ((DeltaFun τ * fk (![6, 4, 2] i) τ) *
          (!![jInvariantFun τ - jInvariantFun z, 0, 1;
             -2 * (jInvariantFun τ - jInvariantFun z), -2, 0; 1, 0, 0] :
            Matrix (Fin 3) (Fin 3) ℂ) i j * fk (![12, 10, 8] j) z) := by
    intro i j
    rw [show UpsilonPlusClear 8 τ z =
        ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ •
          (PiMatDelta ![6, 4, 2] τ * !![jInvariantFun τ - jInvariantFun z, 0, 1;
            -2 * (jInvariantFun τ - jInvariantFun z), -2, 0; 1, 0, 0] *
            PiMat ![12, 10, 8] z) from rfl]
    rw [Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_PiMat_apply]
  simp only [KPlusClear, Fin.sum_univ_three, phiVec, phitVec, hU, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
  rw [hJ]
  ring

/-- The expansion of `K_+^{clear}` for `d = 24` at a point with `j(τ) = j(z)`. -/
lemma KPlusClear_expand_twentyfour (τ z : UpperHalfPlane)
    (hJ : jInvariantFun τ = jInvariantFun z) :
    KPlusClear 24 τ z =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
        ( phiNeg2 τ * (DeltaFun τ * fk (14 : ℤ) τ) * c1728 * (DeltaFun z * fk (0 : ℤ) z)
            * ((z : ℂ) ^ 2 * E2S z ^ 2)
        - 2 * c1728 * phi0 τ * (DeltaFun τ * fk (12 : ℤ) τ)
            * (DeltaFun z * fk (2 : ℤ) z) * ((z : ℂ) ^ 2 * E2S z)
        + c1728 * phi2 τ * (DeltaFun τ * fk (10 : ℤ) τ) * (DeltaFun z * fk (4 : ℤ) z)
            * ((z : ℂ) ^ 2) ) := by
  have hU : ∀ i j : Fin 3, UpsilonPlusClear 24 τ z i j =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
        ((DeltaFun τ * fk (![14, 12, 10] i) τ) *
          (!![6 * (jInvariantFun τ - jInvariantFun z), 0,
              c1728 - 6 * (jInvariantFun τ - jInvariantFun z);
             -12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z) +
               5 * c1728 * (jInvariantFun τ - jInvariantFun z), -2 * c1728,
               12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z) -
               7 * c1728 * (jInvariantFun τ - jInvariantFun z);
             c1728 + 6 * (jInvariantFun τ - jInvariantFun z), 0,
               -6 * (jInvariantFun τ - jInvariantFun z)] :
            Matrix (Fin 3) (Fin 3) ℂ) i j * (DeltaFun z * fk (![4, 2, 0] j) z)) := by
    intro i j
    rw [show UpsilonPlusClear 24 τ z =
        ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ •
          (PiMatDelta ![14, 12, 10] τ *
            !![6 * (jInvariantFun τ - jInvariantFun z), 0,
                c1728 - 6 * (jInvariantFun τ - jInvariantFun z);
               -12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z) +
                 5 * c1728 * (jInvariantFun τ - jInvariantFun z), -2 * c1728,
                 12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z) -
                 7 * c1728 * (jInvariantFun τ - jInvariantFun z);
               c1728 + 6 * (jInvariantFun τ - jInvariantFun z), 0,
                 -6 * (jInvariantFun τ - jInvariantFun z)] *
            (DeltaFun z • PiMat ![4, 2, 0] z)) from rfl]
    rw [Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_smul_PiMat_apply]
  simp only [KPlusClear, Fin.sum_univ_three, phiVec, phitVec, hU, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
  rw [hJ]
  ring

/-! ## The main theorem -/

/-- **The cleared kernel `K_+` vanishes at `τ = TS·z = (z−1)/z`**, the point where the
residue of `K_+` is `−(1/2π)φ_+(TS) = 0`. -/
theorem KPlusClear_TS (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Kernels.KPlusClear d ((1 : ℝ) +ᵥ (ModularGroup.S • z)) z = 0 := by
  set τ : ℍ := (1 : ℝ) +ᵥ (ModularGroup.S • z) with hτ
  -- `j(τ) = j(z)`: `j` is invariant under `SL(2,ℤ) ∋ TS`.
  have hj : jInvariantFun τ = jInvariantFun z := by
    rw [hτ, KernelFacts.jInvariantFun_vadd_one, KernelFacts.kpc_jInvariant_S]
  -- the transformation laws of the modular forms at `τ = TS·z`, all with the factor of
  -- automorphy `z^k` of `TS`.
  have h4 : E4Fun τ = (z : ℂ) ^ 4 * E4Fun z := by
    rw [hτ, KernelFacts.E4Fun_vadd_one,
      KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_E4_slash_S]
    simp
  have h6 : E6Fun τ = (z : ℂ) ^ 6 * E6Fun z := by
    rw [hτ, KernelFacts.E6Fun_vadd_one,
      KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_E6_slash_S]
    simp
  have hΔ : DeltaFun τ = (z : ℂ) ^ 12 * DeltaFun z := by
    rw [hτ, KernelFacts.DeltaFun_vadd_one,
      KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_Delta_slash_S]
    simp
  -- the quasimodular law `E₂(TS·z) = z²(E₂|₂S)(z)`.
  have hE2 : E2Fun τ = (z : ℂ) ^ 2 * E2S z := by
    have hz : (z : ℂ) ≠ 0 := KernelFacts.kpc_tau_ne_zero z
    rw [hτ, E2Fun_vadd_one, E2Fun_S_smul, TildeFacts.E2S_eq]
    field_simp
  -- the two cancellations `Δ · f_2 = E₁₄` (at `τ` and at `z`).
  have hfk2 : DeltaFun τ * fk (2 : ℤ) τ = E14Fun τ := by
    rw [KernelFacts.fk_two]
    exact mul_div_cancel₀ _ (ClassicalFacts.DeltaFun_ne_zero τ)
  have hfk2z : DeltaFun z * fk (2 : ℤ) z = E14Fun z := by
    rw [KernelFacts.fk_two]
    exact mul_div_cancel₀ _ (ClassicalFacts.DeltaFun_ne_zero z)
  have hfk0z : DeltaFun z * fk (0 : ℤ) z = DeltaFun z := by
    rw [KernelFacts.fk_zero, Pi.one_apply, mul_one]
  rcases hd with rfl | rfl
  · rw [KPlusClear_expand_eight τ z hj, hfk2]
    simp only [KernelFacts.fk_six, KernelFacts.fk_four, KernelFacts.fk_eight,
      KernelFacts.fk_ten, KernelFacts.fk_twelve, E8Fun, E10Fun, E14Fun, phiNeg2, phi0, phi2]
    rw [h4, h6, hΔ, hE2]
    ring
  · rw [KPlusClear_expand_twentyfour τ z hj, hfk2z, hfk0z]
    simp only [KernelFacts.fk_fourteen, KernelFacts.fk_twelve, KernelFacts.fk_ten,
      KernelFacts.fk_four, E10Fun, E14Fun, phiNeg2, phi0, phi2]
    rw [h4, h6, hΔ, hE2]
    ring

end Work.Residues
