/-
# The cusp expansion of `K₊^{(24)}` on the funnel: algebraic core

This file sets up the *exact* algebraic decomposition of
`K₊^{(24)}(τ,z) - Compact.Gplus24(τ,z)` used by
`Work.Asymptotics.KPlus_funnel_tail_twentyfour`.

Notation (all for `z = i t`, `τ` in the funnel):

* `q = e^{2πiz}` (`qParamFun z`), `E = e^{πiz}` (`Ept z`), so `q = E²` and `q⁻¹ = (Ept z)^{-2}`;
* `s = E2S z = E₂(z) - 6i/(πz)` (`E2S_eq`), `S0 = 1 - 6i/(πz)` (its leading term);
* `D = Δ(z)`, `E4 = E₄(z)`, `E6 = E₆(z)`, `E14 = E₄(z)²E₆(z)`;
* `j = j(τ)`, `J = j(τ) - j(z)`, `c = (36·1728·π⁻²·i)⁻¹`;
* the `τ`-atoms `r0 = τE₁₄(τ)`, `r1 = φ₀(τ)Δ(τ)`, `r2 = φ₂(τ)E₁₀(τ)`, `R0 = φ₀(τ)E₄(τ)³ = r1·j(τ)`.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Kernels.KernelFacts.fk_slash
import Submission.Work.Asymptotics.Compact.kminus_tail_core

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Topology

noncomputable section

namespace Tail24

open Work.Kernels

/-- `c = (36·1728·π⁻²·i)⁻¹`. -/
def c : ℂ := ((36 : ℂ) * 1728 * ((Real.pi : ℂ)) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- `r0(τ) = τE₁₄(τ)`. -/
def r0 (τ : ℍ) : ℂ := (τ : ℂ) * E14Fun τ
/-- `r1(τ) = φ₀(τ)Δ(τ)`, `φ₀ = τE₂(τ) - 3i/π`. -/
def r1 (τ : ℍ) : ℂ := Compact.phi1 τ * DeltaFun τ
/-- `r2(τ) = φ₂(τ)E₁₀(τ)`, `φ₂ = τE₂(τ)² - (6i/π)E₂(τ)`. -/
def r2 (τ : ℍ) : ℂ := Compact.phi2t τ * E10Fun τ
/-- `R0(τ) = φ₀(τ)E₄(τ)³ = r1(τ)·j(τ)`. -/
def R0 (τ : ℍ) : ℂ := Compact.phi1 τ * E4Fun τ ^ 3

/-- `S0 z = 1 - 6i/(πz)`. -/
def S0 (z : ℍ) : ℂ := 1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))

/-- The `τ`-part of the bracket `P` multiplying `Δ(z)⁻¹`. -/
def Pfun (τ z : ℍ) : ℂ :=
  r0 τ * (6 * E4Fun z - 6 * (E2S z) ^ 2)
    + r1 τ * ((-12 * jInvariantFun τ + 8640) * E4Fun z
        + (12 * jInvariantFun τ - 12096) * (E2S z) ^ 2)
    + r2 τ * (6 * E4Fun z - 6 * (E2S z) ^ 2)

/-- `U`: the coefficient of `(Δ(z)J)⁻¹`. -/
def Ufun (τ z : ℍ) : ℂ :=
  1728 * r0 τ * (E2S z) ^ 2 + 1728 * r2 τ * E4Fun z

/-- `V`: the coefficient of `(Δ(z)²J)⁻¹`. -/
def Vfun (τ z : ℍ) : ℂ := -3456 * r1 τ * E14Fun z * E2S z

/-- `Φ = P - V/E₄(z)³`. -/
def Phi (τ z : ℍ) : ℂ := Pfun τ z - Vfun τ z / E4Fun z ^ 3

/-- `P` with the `z`-atoms replaced by their leading terms. -/
def Pref (τ z : ℍ) : ℂ :=
  6 * (r0 τ + r2 τ) * (1 - S0 z ^ 2)
    + r1 τ * ((-12 * jInvariantFun τ + 8640) + (12 * jInvariantFun τ - 12096) * S0 z ^ 2)

/-- `Φ` with the `z`-atoms replaced by their leading terms. -/
def Phiref (τ z : ℍ) : ℂ := Pref τ z + 3456 * r1 τ * S0 z

/-- `P⁽¹⁾`: the coefficient of `q` in the expansion of `P`. -/
def P1 (τ z : ℍ) : ℂ :=
  (1440 + 288 * S0 z) * (r0 τ + r2 τ)
    + r1 τ * (-2880 * jInvariantFun τ + 2073600 - 576 * jInvariantFun τ * S0 z
        + 580608 * S0 z)

/-- `Q⁽¹⁾`: the coefficient of `q` in the expansion of `Φ`. -/
def Q1 (τ z : ℍ) : ℂ := P1 τ z - 82944 * r1 τ - 2571264 * r1 τ * S0 z

/-- `U` with the `z`-atoms replaced by their leading terms. -/
def Uref (τ z : ℍ) : ℂ := 1728 * r0 τ * S0 z ^ 2 + 1728 * r2 τ

/-- `Θ0`: the `q⁰`-coefficient of the cusp expansion of `K₊^{(24)}/(c z²)`. -/
def Th0 (τ z : ℍ) : ℂ := Q1 τ z + 24 * Phiref τ z - Uref τ z + 3456 * R0 τ * S0 z

/-- `ρ = Δ(z)j(τ)/E₄(z)³`. -/
def rho (τ z : ℍ) : ℂ := DeltaFun z * jInvariantFun τ / E4Fun z ^ 3

/-- The `A1` coefficient of `𝒢₊^{(24)}`. -/
def A1 (τ z : ℍ) : ℂ :=
  ((Real.pi : ℂ) * Complex.I)⁻¹ * (-72 * (τ : ℂ) * E14Fun τ
      + Compact.phi1 τ * DeltaFun τ * (144 * jInvariantFun τ - 124416)
      - 72 * Compact.phi2t τ * E10Fun τ)

/-- The `A0` coefficient of `𝒢₊^{(24)}`. -/
def A0 (τ z : ℍ) : ℂ :=
  (216 * (τ : ℂ) * E14Fun τ / (Real.pi : ℂ) ^ 2
    - 36 * Compact.phi1 τ * DeltaFun τ * (12 * jInvariantFun τ - 12096) / (Real.pi : ℂ) ^ 2
    + 216 * Compact.phi2t τ * E10Fun τ / (Real.pi : ℂ) ^ 2)

/-- The `B1` coefficient of `𝒢₊^{(24)}`. -/
def B1 (τ z : ℍ) : ℂ :=
  (20736 / ((Real.pi : ℂ) * Complex.I)) *
    (Compact.phi1 τ * E4Fun τ ^ 3 - 720 * Compact.phi1 τ * DeltaFun τ
      - (τ : ℂ) * E14Fun τ)

/-- The `B0` coefficient of `𝒢₊^{(24)}`. -/
def B0 (τ z : ℍ) : ℂ :=
  (864 / (Real.pi : ℂ) ^ 2) *
    (78 * (τ : ℂ) * E14Fun τ
      - Compact.phi1 τ * DeltaFun τ * (12 * jInvariantFun τ - 12096)
      + 6 * Compact.phi2t τ * E10Fun τ)

lemma qParamFun_eq_Ept_sq' (z : ℍ) :
    qParamFun z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
  congr 1; ring

/-- `(qParamFun z)⁻¹ = (Ept z)^{-2}`. -/
lemma qinv_eq (z : ℍ) : (qParamFun z)⁻¹ = Work.Residues.Ept z ^ (-2 : ℤ) := by
  rw [show (-2 : ℤ) = -((2 : ℤ)) by norm_num, zpow_neg, zpow_ofNat, qParamFun_eq_Ept_sq' z]

/-- `Compact.Gplus 24 = c (q⁻¹(A1 z + A0) + (B1 z + B0))`. -/
lemma Gplus24_eq (τ z : ℍ) :
    Compact.Gplus 24 τ z = c * ((qParamFun z)⁻¹ * (A1 τ z * (z : ℂ) + A0 τ z)
      + (B1 τ z * (z : ℂ) + B0 τ z)) := by
  have hq : Work.Residues.Ept z ^ (-2 : ℤ) = (qParamFun z)⁻¹ := (qinv_eq z).symm
  rw [Compact.Gplus, if_neg (by norm_num : ¬ (24 = 8)), Compact.Gplus24, hq]
  simp only [c, A1, A0, B1, B0]
  ring

/-! ## The exact algebraic identities -/

lemma E4_cube_add_J (τ z : ℍ) :
    (jInvariantFun τ - jInvariantFun z) * DeltaFun z + E4Fun z ^ 3
      = DeltaFun z * jInvariantFun τ := by
  rw [sub_mul, mul_comm (jInvariantFun z) (DeltaFun z),
    ← ClassicalFacts.DeltaFun_mul_jInvariantFun z]
  ring

/-- `j(τ)Δ(τ) = E₄(τ)³`, in the form needed below. -/
lemma JmulDelta (τ z : ℍ) :
    (jInvariantFun τ - jInvariantFun z) * DeltaFun z
      = DeltaFun z * jInvariantFun τ - E4Fun z ^ 3 := by
  rw [← E4_cube_add_J τ z]; ring

/-- `j(τ)Δ(z) - E₄(z)³ = Δ(z)(j(τ)-j(z))`. -/
lemma mul_J_sub (τ z : ℍ) :
    jInvariantFun τ * DeltaFun z - E4Fun z ^ 3
      = DeltaFun z * (jInvariantFun τ - jInvariantFun z) := by
  rw [mul_comm (jInvariantFun τ) (DeltaFun z), ← E4_cube_add_J τ z]
  ring

/-- `J` written with `Δ(z)` in the denominator. -/
lemma JDelta (τ z : ℍ) : jInvariantFun τ - jInvariantFun z
    = (jInvariantFun τ * DeltaFun z - E4Fun z ^ 3) / DeltaFun z := by
  rw [eq_div_iff (ClassicalFacts.DeltaFun_ne_zero z), mul_J_sub]
  ring

/-- `r1 τ * j(τ) = R0 τ`. -/
lemma r1_mul_j (τ : ℍ) : r1 τ * jInvariantFun τ = R0 τ := by
  rw [r1, R0, mul_assoc, ClassicalFacts.DeltaFun_mul_jInvariantFun]

/-- `A1` in the form used by the algebra (with `i` to the first power). -/
def Ac1 (τ z : ℍ) : ℂ :=
  (72 * Complex.I / (Real.pi : ℂ)) * (r0 τ + r2 τ)
    - (144 * Complex.I / (Real.pi : ℂ)) * (r1 τ * jInvariantFun τ)
    + (124416 * Complex.I / (Real.pi : ℂ)) * r1 τ

/-- `A0` in the form used by the algebra. -/
def Ac0 (τ z : ℍ) : ℂ :=
  (216 / (Real.pi : ℂ) ^ 2) * (r0 τ + r2 τ)
    - (432 / (Real.pi : ℂ) ^ 2) * (r1 τ * jInvariantFun τ)
    + (435456 / (Real.pi : ℂ) ^ 2) * r1 τ

/-- `B1` in the form used by the algebra. -/
def Bc1 (τ z : ℍ) : ℂ :=
  -(20736 * Complex.I / (Real.pi : ℂ)) * (r1 τ * jInvariantFun τ - 720 * r1 τ - r0 τ)

/-- `B0` in the form used by the algebra. -/
def Bc0 (τ z : ℍ) : ℂ :=
  (864 / (Real.pi : ℂ) ^ 2)
    * (78 * r0 τ - 12 * (r1 τ * jInvariantFun τ) + 12096 * r1 τ + 6 * r2 τ)

lemma A1_eq_Ac1 (τ z : ℍ) : A1 τ z = Ac1 τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [A1, Ac1, r0, r1, r2, jInvariantFun]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

lemma A0_eq_Ac0 (τ z : ℍ) : A0 τ z = Ac0 τ z := by
  rw [A0, Ac0, r0, r1, r2]
  ring

lemma B1_eq_Bc1 (τ z : ℍ) : B1 τ z = Bc1 τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [B1, Bc1, r0, r1, jInvariantFun]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

lemma B0_eq_Bc0 (τ z : ℍ) : B0 τ z = Bc0 τ z := by
  rw [B0, Bc0, r0, r1, r2]
  ring

/-- **The matching identity at order `q⁻¹`**: `z²Φref = A1 z + A0`. -/
lemma Gplus24_A1A0 (τ z : ℍ) :
    (z : ℂ) ^ 2 * Phiref τ z = A1 τ z * (z : ℂ) + A0 τ z := by
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hz : (z : ℂ) ≠ 0 := fun h => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h]; simp)
  rw [A1_eq_Ac1, A0_eq_Ac0]
  simp only [Phiref, Pref, Ac1, Ac0, S0, r0, r1, r2, jInvariantFun]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- **The matching identity at order `q⁰`**: `z²Θ0 = B1 z + B0`. -/
lemma Gplus24_B1B0 (τ z : ℍ) :
    (z : ℂ) ^ 2 * Th0 τ z = B1 τ z * (z : ℂ) + B0 τ z := by
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hz : (z : ℂ) ≠ 0 := fun h => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h]; simp)
  rw [B1_eq_Bc1, B0_eq_Bc0]
  simp only [Th0, Q1, P1, Phiref, Pref, Uref, Bc1, Bc0, S0, r0, r1, r2, R0, jInvariantFun]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- `Gplus 24 = c z²(Φref/q + Θ0)`. -/
lemma Gplus24_eq' (τ z : ℍ) :
    Compact.Gplus 24 τ z = c * (z : ℂ) ^ 2 * (Phiref τ z / qParamFun z + Th0 τ z) := by
  rw [Gplus24_eq, ← Gplus24_A1A0, ← Gplus24_B1B0, div_eq_inv_mul]
  ring

/-- **The cusp form of `K₊^{(24)}`.**  Multiplying by `J = j(τ) - j(z)` clears the pole and
gives `J·K₊ = c z²(J·P/Δ + U/Δ + V/Δ²)`. -/
lemma KPlus24_cusp (τ z : ℍ) (hJ : jInvariantFun τ - jInvariantFun z ≠ 0) :
    (jInvariantFun τ - jInvariantFun z) * KPlus 24 τ z
      = c * (z : ℂ) ^ 2 * ((jInvariantFun τ - jInvariantFun z) * Pfun τ z / DeltaFun z
          + Ufun τ z / DeltaFun z + Vfun τ z / DeltaFun z ^ 2) := by
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hJ2 : E4Fun τ ^ 3 * DeltaFun z - DeltaFun τ * E4Fun z ^ 3 ≠ 0 := by
    intro hh
    have h' : E4Fun τ ^ 3 * DeltaFun z - DeltaFun τ * E4Fun z ^ 3
        = (jInvariantFun τ - jInvariantFun z) * (DeltaFun z * DeltaFun τ) := by
      rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ,
        ← ClassicalFacts.DeltaFun_mul_jInvariantFun z]
      ring
    rw [h'] at hh
    rcases mul_eq_zero.mp hh with h1 | h2
    · exact hJ h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hD h3
    · exact hDt h3
  simp only [KPlus, UpsilonPlus, if_neg (by norm_num : ¬ ((24 : ℕ) = 8)), if_true,
    PiMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    phiVec, phitVec, phiNeg2, phi0, phi2, Compact.phi1, Compact.phi2t, c1728,
    E14Fun, E10Fun, Pfun, Ufun, Vfun, r0, r1, r2, c,
    KernelFacts.fk_four, KernelFacts.fk_ten, KernelFacts.fk_twelve, KernelFacts.fk_fourteen,
    KernelFacts.fk_two, KernelFacts.fk_zero, Pi.one_apply, mul_one, div_eq_mul_inv,
    mul_inv, pow_two, Pi.mul_apply, Pi.inv_apply]
  field_simp [hD, hJ, hI, hDt, hJ2]
  ring

/-- `d1 = Δ(z)⁻¹ - q⁻¹ - 24`. -/
def d1 (z : ℍ) : ℂ := (DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24

/-- `S1`. -/
def Sm1 (τ z : ℍ) : ℂ :=
  jInvariantFun τ * (Phi τ z - Phiref τ z)
    - E4Fun z ^ 3 * Q1 τ z * (qParamFun z / DeltaFun z - 1)
    - E4Fun z ^ 3 * (Phi τ z - Phiref τ z - qParamFun z * Q1 τ z) / DeltaFun z

/-- `S2`. -/
def Sm2 (τ z : ℍ) : ℂ :=
  jInvariantFun τ * Phiref τ z * (1 - DeltaFun z / qParamFun z)
    - E4Fun z ^ 3 * Phiref τ z * d1 z

/-- `S3`. -/
def Sm3 (τ z : ℍ) : ℂ :=
  3456 * R0 τ * (E4Fun z ^ 3 * S0 z - E6Fun z * E2S z / E4Fun z)

/-- `S4`. -/
def Sm4 (τ z : ℍ) : ℂ := (Ufun τ z - Uref τ z) + Uref τ z * (1 - E4Fun z ^ 3)

/-- `S5`. -/
def Sm5 (τ z : ℍ) : ℂ := -(DeltaFun z * jInvariantFun τ) * Th0 τ z

/-- **The abstract five-term decomposition.**  Pure field identity: with `jz = E₄(z)³/Δ(z)`,
`R0 = r1·j(τ)`, `V = -3456·r1·E₁₄(z)·s` and `E₁₄(z) = E₄(z)²E₆(z)`, the bracket of `K₊`
decomposes as `S1 + … + S5`. -/
lemma Psi_split_alg (r1 R0 P U Uref V Q1 Phiref jt jz Dz q E4z E6z E14z E2S S0 : ℂ)
    (hDz : Dz ≠ 0) (hq : q ≠ 0) (hE4 : E4z ≠ 0)
    (hR : R0 = r1 * jt) (hV : V = -3456 * r1 * E14z * E2S)
    (hE14 : E14z = E4z ^ 2 * E6z) (hjz : Dz * jz = E4z ^ 3) :
    (jt - jz) * P + U + V / Dz
        - Dz * (jt - jz) * (Phiref / q + (Q1 + 24 * Phiref - Uref + 3456 * R0 * S0))
      = (jt * (P - V / E4z ^ 3 - Phiref) - E4z ^ 3 * Q1 * (q / Dz - 1)
            - E4z ^ 3 * (P - V / E4z ^ 3 - Phiref - q * Q1) / Dz)
        + (jt * Phiref * (1 - Dz / q) - E4z ^ 3 * Phiref * (Dz⁻¹ - q⁻¹ - 24))
        + 3456 * R0 * (E4z ^ 3 * S0 - E6z * E2S / E4z)
        + ((U - Uref) + Uref * (1 - E4z ^ 3))
        + (-(Dz * jt) * (Q1 + 24 * Phiref - Uref + 3456 * R0 * S0)) := by
  have hjz' : jz = E4z ^ 3 / Dz := by rw [eq_div_iff hDz, mul_comm]; exact hjz
  rw [hjz', hR, hV, hE14]
  field_simp
  ring

/-- **The exact decomposition**: `Δ(z)·J·(K₊ - 𝒢₊) = c z² (S1 + … + S5)`. -/
lemma KPlus24_diff (τ z : ℍ) (hJ : jInvariantFun τ - jInvariantFun z ≠ 0)
    (hE4 : E4Fun z ≠ 0) :
    DeltaFun z * (jInvariantFun τ - jInvariantFun z) * (KPlus 24 τ z - Compact.Gplus 24 τ z)
      = c * (z : ℂ) ^ 2
          * (Sm1 τ z + Sm2 τ z + Sm3 τ z + Sm4 τ z + Sm5 τ z) := by
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hq : qParamFun z ≠ 0 := qParamFun_ne_zero' z
  have hkey : DeltaFun z * (jInvariantFun τ - jInvariantFun z)
      * (KPlus 24 τ z - Compact.Gplus 24 τ z)
      = c * (z : ℂ) ^ 2 * ((jInvariantFun τ - jInvariantFun z) * Pfun τ z
          + Ufun τ z + Vfun τ z / DeltaFun z
          - DeltaFun z * (jInvariantFun τ - jInvariantFun z)
              * (Phiref τ z / qParamFun z + Th0 τ z)) := by
    rw [show DeltaFun z * (jInvariantFun τ - jInvariantFun z)
          * (KPlus 24 τ z - Compact.Gplus 24 τ z)
        = DeltaFun z * ((jInvariantFun τ - jInvariantFun z) * KPlus 24 τ z)
          - DeltaFun z * (jInvariantFun τ - jInvariantFun z) * Compact.Gplus 24 τ z
        from by ring]
    rw [KPlus24_cusp τ z hJ, Gplus24_eq']
    field_simp
  rw [hkey]
  rw [show (jInvariantFun τ - jInvariantFun z) * Pfun τ z
        + Ufun τ z + Vfun τ z / DeltaFun z
        - DeltaFun z * (jInvariantFun τ - jInvariantFun z)
            * (Phiref τ z / qParamFun z + Th0 τ z)
      = Sm1 τ z + Sm2 τ z + Sm3 τ z + Sm4 τ z + Sm5 τ z from by
    have h1 := Psi_split_alg (r1 τ) (R0 τ) (Pfun τ z) (Ufun τ z) (Uref τ z) (Vfun τ z)
      (Q1 τ z) (Phiref τ z) (jInvariantFun τ) (jInvariantFun z) (DeltaFun z) (qParamFun z)
      (E4Fun z) (E6Fun z) (E14Fun z) (E2S z) (S0 z)
      hD hq hE4 (r1_mul_j τ).symm rfl rfl (ClassicalFacts.DeltaFun_mul_jInvariantFun z)
    simpa only [Sm1, Sm2, Sm3, Sm4, Sm5, Phi, d1, Th0, Vfun] using h1]

end Tail24

end

end Work.Asymptotics
