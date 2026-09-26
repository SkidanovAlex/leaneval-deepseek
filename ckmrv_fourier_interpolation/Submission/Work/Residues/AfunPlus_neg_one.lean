/-
# The value of the cleared kernel at the pole `τ = T⁻¹z = z - 1`

The kernel `K_+^{(d)}(τ,z)` has, as a function of `τ`, simple poles at the `SL(2,ℤ)`-orbit
of `z`, i.e. exactly where `j(τ) = j(z)`.  The residue at a pole `τ₀` of the orbit is
`j'(τ₀)⁻¹ · K_+^{clear}(d, τ₀, z) / (Δ(τ₀)Δ(z)^e) = j'(τ₀)⁻¹ · AfunPlus d z τ₀`
(`Work.Residues.hasResidue_of_cleared`).

`Work.Residues.ResidueKernel` computes this at the poles `z` (`AfunPlus d z z = 0`), `Tz = z+1`
(`AfunPlus d z (Tz) = -(1/2π) j'(z)`) and `TS·z` (`= 0`).  This file computes it at the
remaining generator of the stabilizer `⟨T⟩` of the cusp, namely at `T⁻¹z = z - 1`:

  `AfunPlus d z (z - 1) = (1/(2π)) · j'(z)`

so that the residue of `K_+^{(d)}(·,z)` at `τ = T⁻¹z` is `-(1/2π)φ_+(T⁻¹) = +1/(2π)`,
consistent with `T⁻¹ ≡ 2 - T` and `φ_+(T) = -1` in the quotient `R/𝓘_+` (CKMRV Theorem 4.9(3),
used in `Work.Asymptotics.Kfun_principal_part_z_lip` for the case `n = -1`).

The computation is the direct one: at `τ = z - 1` the factor `j(τ) - j(z)` vanishes, so the
cleared kernel collapses to its three diagonal terms (`KPlusClear_expand_eight`,
`KPlusClear_expand_twentyfour`), and every `τ`-dependent modular form occurring there
(`Δ, E₄, E₆, E₁₄`, i.e. `Δ(τ)f_k(τ)`) is invariant under `τ ↦ τ + 1`; only the three
`E₂`-corrections `φ_{-2}(τ) - φ_{-2}(z) = -1`, `φ_0(τ) - φ_0(z) = -E₂(z)`,
`φ_2(τ) - φ_2(z) = -E₂(z)²` survive, and the result follows from
`z(E₂(z) - (E₂|₂S)(z)) = 6i/π` (`Work.Kernels.TildeFacts.E2S_eq`).
-/
import Mathlib
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.ResidueTheoremMinus

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Residues

open Work.Kernels

/-! ## The translate `τ = (-1) +ᵥ z = z - 1` and its `T`-invariance -/

/-- `(1:ℝ) +ᵥ ((-1:ℝ) +ᵥ z) = z`, the translation `z - 1` followed by `z ↦ z + 1`. -/
private lemma vadd_one_vadd_neg_one (z : UpperHalfPlane) :
    (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- The underlying complex number of `(-1:ℝ) +ᵥ z` is `z - 1`. -/
private lemma coe_vadd_neg_one (z : UpperHalfPlane) :
    ((((-1 : ℝ) +ᵥ z : UpperHalfPlane)) : ℂ) = (z : ℂ) - 1 := by
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- `Δ` is invariant under `τ ↦ τ - 1`. -/
private lemma DeltaFun_vadd_neg_one (z : UpperHalfPlane) :
    DeltaFun ((-1 : ℝ) +ᵥ z) = DeltaFun z := by
  have h := KernelFacts.DeltaFun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [vadd_one_vadd_neg_one] at h
  exact h.symm

/-- `E₄` is invariant under `τ ↦ τ - 1`. -/
private lemma E4Fun_vadd_neg_one (z : UpperHalfPlane) :
    E4Fun ((-1 : ℝ) +ᵥ z) = E4Fun z := by
  have h := KernelFacts.E4Fun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [vadd_one_vadd_neg_one] at h
  exact h.symm

/-- `E₆` is invariant under `τ ↦ τ - 1`. -/
private lemma E6Fun_vadd_neg_one (z : UpperHalfPlane) :
    E6Fun ((-1 : ℝ) +ᵥ z) = E6Fun z := by
  have h := KernelFacts.E6Fun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [vadd_one_vadd_neg_one] at h
  exact h.symm

/-- `j` is invariant under `τ ↦ τ - 1`. -/
private lemma jInvariantFun_vadd_neg_one (z : UpperHalfPlane) :
    jInvariantFun ((-1 : ℝ) +ᵥ z) = jInvariantFun z := by
  have h := KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [vadd_one_vadd_neg_one] at h
  exact h.symm

/-! ## The cleared kernel at `τ = z - 1` -/

/-- **The cleared kernel `K_+` at the pole `τ = T⁻¹z = z - 1`.**  Since `j(z-1) = j(z)` the
factor `j(τ) - j(z)` vanishes and the cleared kernel collapses to `-i E₄²E₆ Δ^e`, where
`e = dpow d` is `1` for `d = 8` and `2` for `d = 24`. -/
private theorem KPlusClear_vadd_neg_one (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    KPlusClear d ((-1 : ℝ) +ᵥ z) z =
      -(Complex.I) * (E4Fun z ^ 2 * E6Fun z) * DeltaFun z ^ dpow d := by
  have hj : jInvariantFun ((-1 : ℝ) +ᵥ z) = jInvariantFun z := jInvariantFun_vadd_neg_one z
  have hD : DeltaFun ((-1 : ℝ) +ᵥ z) = DeltaFun z := DeltaFun_vadd_neg_one z
  have h4 : E4Fun ((-1 : ℝ) +ᵥ z) = E4Fun z := E4Fun_vadd_neg_one z
  have h6 : E6Fun ((-1 : ℝ) +ᵥ z) = E6Fun z := E6Fun_vadd_neg_one z
  have hE2 : E2Fun ((-1 : ℝ) +ᵥ z) = E2Fun z := TildeFacts.E2Fun_vadd_neg_one z
  have hcoe : ((((-1 : ℝ) +ᵥ z : UpperHalfPlane)) : ℂ) = (z : ℂ) - 1 := coe_vadd_neg_one z
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hz : (z : ℂ) ≠ 0 := by exact_mod_cast z.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rcases hd with rfl | rfl
  · rw [show dpow 8 = 1 from by norm_num [dpow]]
    rw [KPlusClear_expand_eight ((-1 : ℝ) +ᵥ z) z hj]
    simp only [KernelFacts.fk_six, KernelFacts.fk_four, KernelFacts.fk_two, KernelFacts.fk_eight,
      KernelFacts.fk_ten, KernelFacts.fk_twelve, Pi.div_apply, E8Fun, E10Fun, E14Fun,
      phiNeg2, phi0, phi2]
    rw [hD, h4, h6, hE2, hcoe, TildeFacts.E2S_eq z]
    rw [_root_.zpow_neg, _root_.zpow_ofNat]
    field_simp
    ring
  · rw [show dpow 24 = 2 from by norm_num [dpow]]
    rw [KPlusClear_expand_twentyfour ((-1 : ℝ) +ᵥ z) z hj]
    simp only [KernelFacts.fk_fourteen, KernelFacts.fk_twelve, KernelFacts.fk_ten,
      KernelFacts.fk_four, KernelFacts.fk_two, KernelFacts.fk_zero, Pi.one_apply, c1728,
      Pi.div_apply, E10Fun, E14Fun, phiNeg2, phi0, phi2]
    rw [hD, h4, h6, hE2, hcoe, TildeFacts.E2S_eq z]
    rw [_root_.zpow_neg, _root_.zpow_ofNat]
    field_simp
    ring

/-! ## The main result -/

/-- **`AfunPlus d z (T⁻¹z) = (1/2π)·j'(z)`.**  This is the `T⁻¹` companion of
`Work.Residues.AfunPlus_vadd_one_eq`: the residue of `K_+^{(d)}(·,z)` at `τ = z - 1` is
`-(1/2π)φ_+(T⁻¹) = 1/(2π)`. -/
theorem AfunPlus_neg_one (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Residues.AfunPlus d z ((-1 : ℝ) +ᵥ z) = (1 / (2 * Real.pi)) * Work.Residues.jprime z := by
  have hK := KPlusClear_vadd_neg_one d hd z
  have hD := DeltaFun_vadd_neg_one z
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [AfunPlus, hK, hD, jprime]
  rcases hd with rfl | rfl
  · rw [show dpow 8 = 1 from by norm_num [dpow]]
    field_simp
  · rw [show dpow 24 = 2 from by norm_num [dpow]]
    field_simp

end Work.Residues
