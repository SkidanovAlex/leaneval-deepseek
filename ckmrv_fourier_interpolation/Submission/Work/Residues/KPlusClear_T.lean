import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA

namespace Work.Residues

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

/-! ## Evaluation of the cleared kernel `K_+` at `(Tz, z)`

This file computes the value of the cleared kernel `Δ(τ)Δ(z)^e(j(τ)−j(z))K_+^{(d)}(τ,z)` at
`τ = Tz = z+1` for `d = 8` and `d = 24`.  Since `j(Tz) = j(z)`, the factor `j(τ)−j(z)` vanishes
and the whole expression collapses to a polynomial in the classical modular forms evaluated at
`z`; the point is that all the `E₂`-dependence cancels, leaving `iE₄²E₆·Δ(z)^e`.

The computation is purely algebraic: we expand the definitions of `KPlusClear`,
`UpsilonPlusClear`, `PiMatDelta`, `PiMat`, `fk`, `phiVec`, `phitVec`, use `T`-invariance of
`E₂, E₄, E₆, Δ, j`, and the transformation law `E₂|₂S = E₂ − 6i/(πz)`, and finally clear
denominators. -/

/-- **`KPlusClear` at `(Tz,z)` for `d = 8`**: `Δ(Tz)Δ(z)(j(Tz)−j(z))K_+^{(8)}(Tz,z)
= iE₄(z)²E₆(z)Δ(z)`. -/
private lemma KPlusClear_vadd_one_eight (z : UpperHalfPlane) :
    Work.Kernels.KPlusClear 8 ((1 : ℝ) +ᵥ z) z =
      Complex.I * Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z * Work.Kernels.DeltaFun z := by
  have hz : (z : ℂ) ≠ 0 := by exact_mod_cast z.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  simp only [Work.Kernels.KPlusClear, Work.Kernels.UpsilonPlusClear, ite_true,
    Work.Kernels.KernelFacts.jInvariantFun_vadd_one, sub_self,
    Work.Kernels.PiMatDelta, Work.Kernels.PiMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul,
    Work.Kernels.KernelFacts.fk_four, Work.Kernels.KernelFacts.fk_six,
    Work.Kernels.KernelFacts.fk_two, Work.Kernels.KernelFacts.fk_eight,
    Work.Kernels.KernelFacts.fk_ten, Work.Kernels.KernelFacts.fk_twelve,
    Work.Kernels.E8Fun, Work.Kernels.E10Fun, Work.Kernels.E14Fun,
    Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one,
    Work.Kernels.KernelFacts.DeltaFun_vadd_one, Work.Kernels.E2Fun_vadd_one,
    Work.Kernels.phiVec, Work.Kernels.phiNeg2, Work.Kernels.phi0, Work.Kernels.phi2,
    Work.Kernels.phitVec, Work.Kernels.coe_vadd_one, Work.Kernels.TildeFacts.E2S_eq,
    Pi.div_apply,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    _root_.zpow_neg, _root_.zpow_ofNat]
  field_simp
  ring

/-- **`KPlusClear` at `(Tz,z)` for `d = 24`**: `Δ(Tz)Δ(z)²(j(Tz)−j(z))K_+^{(24)}(Tz,z)
= iE₄(z)²E₆(z)Δ(z)²`. -/
private lemma KPlusClear_vadd_one_twentyfour (z : UpperHalfPlane) :
    Work.Kernels.KPlusClear 24 ((1 : ℝ) +ᵥ z) z =
      Complex.I * Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z * Work.Kernels.DeltaFun z ^ 2 := by
  have hz : (z : ℂ) ≠ 0 := by exact_mod_cast z.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  simp only [Work.Kernels.KPlusClear, Work.Kernels.UpsilonPlusClear,
    show ((24 : ℕ) = 8) = False from by decide, ite_true, ite_false, Work.Kernels.c1728,
    Work.Kernels.KernelFacts.jInvariantFun_vadd_one, sub_self,
    Work.Kernels.PiMatDelta, Work.Kernels.PiMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_smul,
    Matrix.smul_apply, smul_eq_mul,
    Work.Kernels.KernelFacts.fk_four, Work.Kernels.KernelFacts.fk_two,
    Work.Kernels.KernelFacts.fk_ten, Work.Kernels.KernelFacts.fk_twelve,
    Work.Kernels.KernelFacts.fk_fourteen, Work.Kernels.KernelFacts.fk_zero,
    Pi.one_apply,
    Work.Kernels.E10Fun, Work.Kernels.E14Fun,
    Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one,
    Work.Kernels.KernelFacts.DeltaFun_vadd_one, Work.Kernels.E2Fun_vadd_one,
    Work.Kernels.phiVec, Work.Kernels.phiNeg2, Work.Kernels.phi0, Work.Kernels.phi2,
    Work.Kernels.phitVec, Work.Kernels.coe_vadd_one, Work.Kernels.TildeFacts.E2S_eq,
    Pi.div_apply,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    _root_.zpow_neg, _root_.zpow_ofNat]
  field_simp
  ring

/-- **The cleared kernel `K_+` at the pole `τ = z + 1` (i.e. `τ = Tz`).**  Dividing the value
of `Δ(τ)Δ(z)^e(j(τ)−j(z))K_+` at `(Tz,z)` by `Δ(Tz)Δ(z)^e` gives `iE₄²E₆/Δ(z)`; since
`j' = −2πiE₄²E₆/Δ`, the residue of `K_+` at the pole `Tz` is `−(1/2π)φ_+(T) = −1/(2π)`. -/
theorem KPlusClear_T (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Kernels.KPlusClear d ((1 : ℝ) +ᵥ z) z =
      (Complex.I * Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z / Work.Kernels.DeltaFun z)
        * (Work.Kernels.DeltaFun ((1 : ℝ) +ᵥ z)
            * Work.Kernels.DeltaFun z ^ (if d = 8 then 1 else 2)) := by
  rcases hd with rfl | rfl
  · rw [KPlusClear_vadd_one_eight, Work.Kernels.KernelFacts.DeltaFun_vadd_one,
      show (if (8 : ℕ) = 8 then (1 : ℕ) else 2) = 1 from by decide]
    have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    field_simp
    try ring
  · rw [KPlusClear_vadd_one_twentyfour, Work.Kernels.KernelFacts.DeltaFun_vadd_one,
      show (if (24 : ℕ) = 8 then (1 : ℕ) else 2) = 2 from by decide]
    have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    field_simp
    try ring

end Work.Residues
