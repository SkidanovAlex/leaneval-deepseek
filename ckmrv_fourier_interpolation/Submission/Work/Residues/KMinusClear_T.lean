import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Kernels.KernelFacts.KMinus_T2
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.fk_slash
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.TildeFacts.E6Fun_eq_theta
import Submission.Work.Modular.thetaSeries_E8_eq_E4

namespace Work.Residues

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

open Work.Kernels
open Work.Kernels.KernelFacts

/-! ## Theta expressions for `E₄`, `E₆`, `Δ`

The residue computation below reduces, through the two theta identities `theta_identity_one`
and `theta_identity_two`, to the classical expressions of the level-one modular forms
`E₄ = (U²+V²+W²)/2`, `E₆ = -U³+3U²W/2+3UW²/2-W³` and `Δ = U²V²W²/256` in terms of the
fourth powers `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴` of the Jacobi theta functions (with
`U = W + V`). -/

/-- `E₆ = -U³ + (3/2)U²W + (3/2)UW² - W³`, in the form used by the theta identities
below.  This is `Work.Kernels.TildeFacts.E6Fun_eq_theta` rewritten with `U = W + V`. -/
theorem KMinusT_E6Fun_eq_theta (z : UpperHalfPlane) :
    E6Fun z =
      - (UFun z ^ 3)
        + (3 : ℂ) / 2 * (UFun z ^ 2 * WFun z)
        + (3 : ℂ) / 2 * (UFun z * WFun z ^ 2)
        - WFun z ^ 3 := by
  rw [Work.Kernels.TildeFacts.E6Fun_eq_theta z, Work.Kernels.TildeFacts.theta_quartic z]
  ring

/-- `E₄ = (U²+V²+W²)/2`, from the identity `Θ_{E₈} = E₄` of `Work.Modular.thetaSeries_E8_eq_E4`
and the decomposition `Θ_{E₈} = (θ₀₀⁸+θ₀₁⁸+θ₁₀⁸)/2`. -/
theorem KMinusT_E4Fun_eq_theta (z : UpperHalfPlane) :
    E4Fun z = (UFun z ^ 2 + VFun z ^ 2 + WFun z ^ 2) / 2 := by
  have h := congr_fun Work.Modular.thetaSeries_E8_eq_E4 z
  rw [Work.Modular.thetaSeries_E8_decomposition z] at h
  rw [show Work.Modular.E4 z = E4Fun z from rfl] at h
  simp only [UFun, WFun, VFun, theta00Fun, theta01Fun, theta10Fun, Work.Modular.theta3,
    Work.Modular.theta4, Work.Modular.theta2] at h ⊢
  rw [← h]
  ring

/-- `Δ = U²V²W²/256`, from `Δ = (E₄³-E₆²)/1728`. -/
theorem KMinusT_DeltaFun_eq_theta (z : UpperHalfPlane) :
    DeltaFun z = UFun z ^ 2 * VFun z ^ 2 * WFun z ^ 2 / 256 := by
  have hdisc : DeltaFun z = (E4Fun z ^ 3 - E6Fun z ^ 2) / 1728 := by
    rw [show DeltaFun z = ModularForm.discriminant z from rfl]
    exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [hdisc, KMinusT_E4Fun_eq_theta z, KMinusT_E6Fun_eq_theta z, Work.Kernels.TildeFacts.theta_quartic z]
  ring

/-! ## The two pairings of the residue matrix with `ψ⃗`, `ψ̃⃗` -/

/-- `A₁ = E₄²W - E₆(U²-V²)`: the `W`-entry of the second row of the residue matrix paired
with `ψ̃⃗`. -/
private def A1 (z : UpperHalfPlane) : ℂ :=
  E4Fun z ^ 2 * WFun z - E6Fun z * (UFun z ^ 2 - VFun z ^ 2)

/-- `A₂ = -E₆W + E₄(U²-V²)`: the `(U²-V²)`-entry of the third row of the residue matrix
paired with `ψ̃⃗`. -/
private def A2 (z : UpperHalfPlane) : ℂ :=
  -(E6Fun z * WFun z) + E4Fun z * (UFun z ^ 2 - VFun z ^ 2)

/-- **First theta identity**: the coefficient of `𝓛(z)` in the pairing vanishes up to the
value `3456Δ`. -/
private theorem theta_identity_one (z : UpperHalfPlane) :
    xi2Fun z * A1 z + xi4Fun z * A2 z = 3456 * DeltaFun z := by
  simp only [xi2Fun, xi4Fun, A1, A2, KMinusT_E4Fun_eq_theta z, KMinusT_E6Fun_eq_theta z,
    KMinusT_DeltaFun_eq_theta z, Work.Kernels.TildeFacts.theta_quartic z]
  ring

/-- **Second theta identity**: the coefficient of `𝓛_S(z)` in the pairing vanishes. -/
private theorem theta_identity_two (z : UpperHalfPlane) :
    (UFun z + VFun z) * A1 z - (UFun z ^ 2 + VFun z ^ 2 - 2 * WFun z ^ 2) * A2 z = 0 := by
  simp only [A1, A2, KMinusT_E4Fun_eq_theta z, KMinusT_E6Fun_eq_theta z, Work.Kernels.TildeFacts.theta_quartic z]
  ring

/-! ## The values of `ψ_2`, `ψ_4` at `τ = z + 1` -/

private theorem psi2_vadd_one (ℓ : LogLambdaData) (z : UpperHalfPlane) :
    psi2 ℓ ((1 : ℝ) +ᵥ z) = xi2Fun z * ℓ.L z - (UFun z + VFun z) * ℓ.L_S z
      + (Real.pi : ℂ) * Complex.I * xi2Fun z := by
  simp only [psi2, xi2Fun, L_vadd_one, L_S_vadd_one, xi2Fun_slash_S,
    UFun_vadd_one, WFun_vadd_one, VFun_vadd_one]
  ring

private theorem psi4_vadd_one (ℓ : LogLambdaData) (z : UpperHalfPlane) :
    psi4 ℓ ((1 : ℝ) +ᵥ z) = xi4Fun z * ℓ.L z
      + (UFun z ^ 2 + VFun z ^ 2 - 2 * WFun z ^ 2) * ℓ.L_S z
      + (Real.pi : ℂ) * Complex.I * xi4Fun z := by
  simp only [psi4, xi4Fun, L_vadd_one, L_S_vadd_one, xi4S_vadd_one_km,
    UFun_vadd_one, VFun_vadd_one, WFun_vadd_one]
  ring

/-! ## The value of the bracket at `τ = z + 1` -/

private theorem KMinusClear_bracket (ℓ : LogLambdaData) (z : UpperHalfPlane) :
    -3456 * DeltaFun z * ℓ.L z + psi2 ℓ ((1 : ℝ) +ᵥ z) * A1 z
        + psi4 ℓ ((1 : ℝ) +ᵥ z) * A2 z
      = 3456 * (Real.pi : ℂ) * Complex.I * DeltaFun z := by
  rw [psi2_vadd_one ℓ z, psi4_vadd_one ℓ z]
  have h1 := theta_identity_one z
  have h2 := theta_identity_two z
  linear_combination ((ℓ.L z) + (Real.pi : ℂ) * Complex.I) * h1 - (ℓ.L_S z) * h2

/-! ## The evaluation of the cleared kernel at `(Tz, z)` -/

private theorem KMinusClear_vadd_one_eight (ℓ : LogLambdaData) (z : UpperHalfPlane) :
    KMinusClear ℓ 8 ((1 : ℝ) +ᵥ z) z =
      (2 * 1728 * (Real.pi : ℂ))⁻¹ * (E4Fun z ^ 2 * E6Fun z) *
        (-3456 * DeltaFun z * ℓ.L z + psi2 ℓ ((1 : ℝ) +ᵥ z) * A1 z
          + psi4 ℓ ((1 : ℝ) +ᵥ z) * A2 z) := by
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have h1728 : (1728 : ℂ) * DeltaFun z = E4Fun z ^ 3 - E6Fun z ^ 2 := by
    rw [show DeltaFun z = (E4Fun z ^ 3 - E6Fun z ^ 2) / 1728 from by
      rw [show DeltaFun z = ModularForm.discriminant z from rfl]
      exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z]
    field_simp
  have hj : DeltaFun z * jInvariantFun z = E4Fun z ^ 3 := by
    rw [jInvariantFun]
    field_simp
  have hA : DeltaFun z * (1728 - jInvariantFun z) = -(E6Fun z ^ 2) := by
    linear_combination h1728 - hj
  simp only [KMinusClear, UpsilonMinusClear, ite_true, c1728, jInvariantFun_vadd_one,
    PiMatDelta, PiMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_smul,
    Matrix.smul_apply, smul_eq_mul,
    fk_four, fk_two, fk_zero, fk_six, fk_eight, fk_ten, E8Fun, E10Fun, E14Fun,
    E4Fun_vadd_one, E6Fun_vadd_one, DeltaFun_vadd_one, Pi.div_apply, A1, A2,
    psiVec, psitVec, Pi.one_apply, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_one, one_mul, mul_zero, zero_mul, add_zero]
  rw [hA, hj]
  field_simp
  ring

private theorem KMinusClear_vadd_one_twentyfour (ℓ : LogLambdaData) (z : UpperHalfPlane) :
    KMinusClear ℓ 24 ((1 : ℝ) +ᵥ z) z =
      (2 * 1728 * (Real.pi : ℂ))⁻¹ * (DeltaFun z * (E4Fun z ^ 2 * E6Fun z)) *
        (-3456 * DeltaFun z * ℓ.L z + psi2 ℓ ((1 : ℝ) +ᵥ z) * A1 z
          + psi4 ℓ ((1 : ℝ) +ᵥ z) * A2 z) := by
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have h1728 : (1728 : ℂ) * DeltaFun z = E4Fun z ^ 3 - E6Fun z ^ 2 := by
    rw [show DeltaFun z = (E4Fun z ^ 3 - E6Fun z ^ 2) / 1728 from by
      rw [show DeltaFun z = ModularForm.discriminant z from rfl]
      exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z]
    field_simp
  have hj : DeltaFun z * jInvariantFun z = E4Fun z ^ 3 := by
    rw [jInvariantFun]
    field_simp
  have hA : DeltaFun z * (1728 - jInvariantFun z) = -(E6Fun z ^ 2) := by
    linear_combination h1728 - hj
  have hj' : DeltaFun z * (DeltaFun z * (E4Fun z * E6Fun z) * jInvariantFun z)
      = DeltaFun z * (E4Fun z * E6Fun z) * E4Fun z ^ 3 := by
    linear_combination (DeltaFun z * (E4Fun z * E6Fun z)) * hj
  have hA' : DeltaFun z * (DeltaFun z * E4Fun z ^ 2 * (1728 - jInvariantFun z))
      = -(DeltaFun z * E4Fun z ^ 2 * E6Fun z ^ 2) := by
    linear_combination (DeltaFun z * E4Fun z ^ 2) * hA
  simp only [KMinusClear, UpsilonMinusClear, show ((24 : ℕ) = 8) = False from by decide,
    ite_false, ite_true, c1728, jInvariantFun_vadd_one,
    PiMatDelta, PiMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_smul,
    Matrix.smul_apply, smul_eq_mul,
    fk_two, fk_zero, fk_eight, fk_ten, fk_twelve, fk_neg_two, E8Fun, E10Fun, E14Fun,
    E4Fun_vadd_one, E6Fun_vadd_one, DeltaFun_vadd_one, Pi.div_apply, A1, A2,
    psiVec, psitVec, Pi.one_apply, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_one, one_mul, mul_zero, zero_mul, add_zero, sub_self, sub_zero]
  rw [hA', hj']
  field_simp
  ring

/-- **The cleared kernel `K_-` at the pole `τ = z + 1` (i.e. `τ = Tz`).**  Dividing the value
of `Δ(τ)Δ(z)^e(j(τ)−j(z))K_-` at `(Tz,z)` by `Δ(Tz)Δ(z)^e` gives `iE₄²E₆/Δ(z)`; since
`j' = −2πiE₄²E₆/Δ`, the residue of `K_-` at the pole `Tz` is `−(1/2π)φ_-(T) = −1/(2π)`. -/
theorem KMinusClear_T (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) :
    Work.Kernels.KMinusClear ℓ d ((1 : ℝ) +ᵥ z) z =
      (Complex.I * Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z / Work.Kernels.DeltaFun z)
        * (Work.Kernels.DeltaFun ((1 : ℝ) +ᵥ z)
            * Work.Kernels.DeltaFun z ^ (if d = 8 then 1 else 2)) := by
  rcases hd with rfl | rfl
  · rw [KMinusClear_vadd_one_eight ℓ z, KMinusClear_bracket ℓ z,
      Work.Kernels.KernelFacts.DeltaFun_vadd_one,
      show (if (8 : ℕ) = 8 then (1 : ℕ) else 2) = 1 from by decide]
    have hD : Work.Kernels.DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
    field_simp
    ring
  · rw [KMinusClear_vadd_one_twentyfour ℓ z, KMinusClear_bracket ℓ z,
      Work.Kernels.KernelFacts.DeltaFun_vadd_one,
      show (if (24 : ℕ) = 8 then (1 : ℕ) else 2) = 2 from by decide]
    have hD : Work.Kernels.DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
    field_simp
    ring

end

end Work.Residues
