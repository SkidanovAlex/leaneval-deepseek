/-
# The regrouped form of `K_+^{(8)}`: the identity and the vanishing at the coincidence

* `KPlus_eight_regrouped`: `36π⁻²i·K_+^{(8)}(τ,z) = z² N₁/D₁` for `j τ ≠ j z`;
* `DOne_self`, `NOne_self`: both `D₁` and `N₁` vanish at the coincidence `τ = σ = S•z`;
* `NOne_decomp`: `N₁ = Δ(σ)E₄(τ)²·P(τ) + Δ(τ)·Q(τ,z)`.
-/
import Mathlib
import Submission.Work.Asymptotics.CuspDecay.Defs
import Submission.Work.Asymptotics.KPlus_eight_decomposition

set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

/-! ## The `S`-transform of the atoms -/

lemma E4Fun_sg (z : UpperHalfPlane) :
    E4Fun (sg z) = (z : ℂ) ^ (4 : ℤ) * E4Fun z :=
  KernelFacts.smul_of_slash_inv KernelFacts.E4Fun_S_slash z

lemma E6Fun_sg (z : UpperHalfPlane) :
    E6Fun (sg z) = (z : ℂ) ^ (6 : ℤ) * E6Fun z :=
  KernelFacts.smul_of_slash_inv KernelFacts.E6Fun_S_slash z

lemma DeltaFun_sg (z : UpperHalfPlane) :
    DeltaFun (sg z) = (z : ℂ) ^ (12 : ℤ) * DeltaFun z :=
  KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash z

lemma E2S_eq (z : UpperHalfPlane) : E2S z = (z : ℂ) ^ (-2 : ℤ) * E2Fun (sg z) := by
  rw [E2S, KernelFacts.kpc_slash_S_apply, sg]
  ring

/-- `E₄(z) = z⁻⁴E₄(σ)`. -/
lemma E4Fun_eq (z : UpperHalfPlane) :
    E4Fun z = (z : ℂ) ^ (-4 : ℤ) * E4Fun (sg z) := by
  have h := KernelFacts.smul_of_slash_inv KernelFacts.E4Fun_S_slash z
  rw [← sg] at h
  rw [h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero z), show (-4:ℤ) + 4 = 0 by norm_num,
    zpow_zero, one_mul]

/-- `E₆(z) = z⁻⁶E₆(σ)`. -/
lemma E6Fun_eq (z : UpperHalfPlane) :
    E6Fun z = (z : ℂ) ^ (-6 : ℤ) * E6Fun (sg z) := by
  have h := KernelFacts.smul_of_slash_inv KernelFacts.E6Fun_S_slash z
  rw [← sg] at h
  rw [h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero z), show (-6:ℤ) + 6 = 0 by norm_num,
    zpow_zero, one_mul]

/-- `Δ(z) = z⁻¹²Δ(σ)`. -/
lemma DeltaFun_eq (z : UpperHalfPlane) :
    DeltaFun z = (z : ℂ) ^ (-12 : ℤ) * DeltaFun (sg z) := by
  have h := KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash z
  rw [← sg] at h
  rw [h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero z), show (-12:ℤ) + 12 = 0 by norm_num,
    zpow_zero, one_mul]

/-! ## `D₁` as the `j`-difference -/

/-- `Δ(τ)Δ(σ)(j τ - j σ) = D₁`. -/
lemma mul_jsub_eq_DOne (τ z : UpperHalfPlane) :
    DeltaFun τ * DeltaFun (sg z) * (jInvariantFun τ - jInvariantFun (sg z)) = DOne τ z := by
  have h1 : DeltaFun τ * jInvariantFun τ = E4Fun τ ^ 3 :=
    ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  have h2 : DeltaFun (sg z) * jInvariantFun (sg z) = E4Fun (sg z) ^ 3 :=
    ClassicalFacts.DeltaFun_mul_jInvariantFun (sg z)
  have h3 : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have h4 : DeltaFun (sg z) ≠ 0 := ClassicalFacts.DeltaFun_ne_zero (sg z)
  rw [DOne, ← h1, ← h2]
  field_simp

/-- `D₁ = Δ(τ)Δ(σ)(j τ - j z)`. -/
lemma DOne_eq' (τ z : UpperHalfPlane) :
    DOne τ z = DeltaFun τ * DeltaFun (sg z) * (jInvariantFun τ - jInvariantFun z) := by
  rw [← mul_jsub_eq_DOne, jInvariantFun_sg]

lemma DOne_eq (τ z : UpperHalfPlane) :
    DOne τ z = DeltaFun τ * DeltaFun (sg z) * (jInvariantFun τ - jInvariantFun (sg z)) := by
  rw [← mul_jsub_eq_DOne]

/-! ## The identity -/

/-- The algebraic content of the regrouping: the right-hand side of the CKMRV decomposition of
`K_+^{(8)}`, with the atoms `E₄(z), E₆(z), Δ(z), E₂|₂S(z)` expressed through `σ = S•z`, equals
`z²N₁/D₁`. -/
private lemma regroup_aux (τ z : UpperHalfPlane)
    (hjz : jInvariantFun τ - jInvariantFun z = DOne τ z / (DeltaFun τ * DeltaFun (sg z)))
    (hD1 : DOne τ z ≠ 0) (hDτ : DeltaFun τ ≠ 0) (hDs : DeltaFun (sg z) ≠ 0)
    (hz : (z : ℂ) ≠ 0) :
    (z : ℂ) ^ 2 * NOne τ z / DOne τ z
      = phitVec z 0 * ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ)
        + (phi2 τ * E14Fun τ * DeltaFun z * phitVec z 0
            + DeltaFun τ * ((τ : ℂ) * E6Fun τ * E8Fun z * phitVec z 2
              - 2 * phi0 τ * E4Fun τ * E10Fun z * phitVec z 1))
          / (DeltaFun τ * DeltaFun z * (jInvariantFun τ - jInvariantFun z)) := by
  rw [hjz]
  simp only [NOne, DOne, thetaOne, phitVec, phiVec, phiNeg2, phi0, phi2, E8Fun, E10Fun, E14Fun,
    E2S, KernelFacts.kpc_slash_S_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, sg]
  rw [show E4Fun z = (z : ℂ) ^ (-4 : ℤ) * E4Fun (ModularGroup.S • z) from by
    have h := KernelFacts.smul_of_slash_inv KernelFacts.E4Fun_S_slash z
    rw [h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero z), show (-4:ℤ) + 4 = 0 by norm_num,
      zpow_zero, one_mul]]
  rw [show E6Fun z = (z : ℂ) ^ (-6 : ℤ) * E6Fun (ModularGroup.S • z) from by
    have h := KernelFacts.smul_of_slash_inv KernelFacts.E6Fun_S_slash z
    rw [h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero z), show (-6:ℤ) + 6 = 0 by norm_num,
      zpow_zero, one_mul]]
  rw [show DeltaFun z = (z : ℂ) ^ (-12 : ℤ) * DeltaFun (ModularGroup.S • z) from by
    have h := KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash z
    rw [h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero z), show (-12:ℤ) + 12 = 0 by norm_num,
      zpow_zero, one_mul]]
  have hD1' : E4Fun τ ^ 3 * DeltaFun (ModularGroup.S • z)
      - DeltaFun τ * E4Fun (ModularGroup.S • z) ^ 3 ≠ 0 := by
    simpa [DOne, sg, mul_comm] using hD1
  have hDs' : DeltaFun (ModularGroup.S • z) ≠ 0 := by simpa [sg] using hDs
  field_simp
  ring_nf

/-- **The regrouped kernel.**  For `j τ ≠ j z`,
`36π⁻²i·K_+^{(8)}(τ,z) = z²N₁/D₁`. -/
theorem KPlus_eight_regrouped (τ z : UpperHalfPlane)
    (hJ : jInvariantFun τ ≠ jInvariantFun z) :
    ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) * KPlus 8 τ z
      = (z : ℂ) ^ 2 * NOne τ z / DOne τ z := by
  have hJ' : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr hJ
  have hDs : DeltaFun (sg z) ≠ 0 := ClassicalFacts.DeltaFun_ne_zero (sg z)
  have hDτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hzc : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have hc : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have hD1ne : DOne τ z ≠ 0 := by
    rw [DOne_eq']
    exact mul_ne_zero (mul_ne_zero hDτ hDs) hJ'
  have hjz : jInvariantFun τ - jInvariantFun z
      = DOne τ z / (DeltaFun τ * DeltaFun (sg z)) := by
    have h := mul_jsub_eq_DOne τ z
    have h' : DeltaFun τ * DeltaFun (sg z) ≠ 0 := mul_ne_zero hDτ hDs
    rw [← jInvariantFun_sg z, ← h]
    field_simp
  have hdec := Work.Asymptotics.KPlus_eight_decomposition τ z hJ
  rw [hdec, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  exact (regroup_aux τ z hjz hD1ne hDτ hDs hzc).symm

/-! ## The decomposition `N₁ = Δ(σ)E₄(τ)²P + Δ(τ)Q` and the vanishing -/

/-- `N₁ = Δ(σ)E₄(τ)²·P(τ) + Δ(τ)·Q(τ,z)`. -/
lemma NOne_decomp (τ z : UpperHalfPlane) :
    NOne τ z = DeltaFun (sg z) * E4Fun τ ^ 2 * PFac τ + DeltaFun τ * QFac τ z := by
  simp only [NOne, DOne, thetaOne, PFac, QFac]
  ring

/-- `D₁ = 0` at the coincidence `τ = σ = S•z`. -/
lemma DOne_self (z : UpperHalfPlane) : DOne (sg z) z = 0 := by
  simp only [DOne]
  ring

/-- `N₁ = 0` at the coincidence `τ = σ = S•z`. -/
lemma NOne_self (z : UpperHalfPlane) : NOne (sg z) z = 0 := by
  rw [NOne_decomp]
  have h2 : E4Fun (sg z) ^ 2 * PFac (sg z) + QFac (sg z) z = 0 := by
    simp only [PFac, QFac, thetaOne, phi0, phi2]
    ring_nf
  calc DeltaFun (sg z) * E4Fun (sg z) ^ 2 * PFac (sg z) + DeltaFun (sg z) * QFac (sg z) z
      = DeltaFun (sg z) * (E4Fun (sg z) ^ 2 * PFac (sg z) + QFac (sg z) z) := by ring
    _ = 0 := by rw [h2]; ring

end Work.Asymptotics.CuspDecay
