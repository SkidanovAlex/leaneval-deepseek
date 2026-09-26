/-
# The tail expansion of `K₊^{(24)}` on the imaginary axis: algebraic core

This file proves the cusp expansion `K₊^{(24)}(τ,z) = 𝒢₊^{(24)}(τ,z) + O(q)` along
`z = i t` (`q = e^{2πiz}`), uniformly for `τ` in the region where the `τ`-atoms
`τE₁₄(τ)`, `φ₀(τ)Δ(τ)`, `φ₂(τ)E₁₀(τ)`, `j(τ)` are bounded.

The structure is the one of `Submission/Work/Asymptotics/KPlus_tail24.lean`: after multiplying
by `Δ(z)(j(τ)-j(z))` the difference `K₊^{(24)} - 𝒢₊^{(24)}` is an explicit sum `S₁ + … + S₅` of
terms each containing a small factor (`Φ-Φref`, `q/Δ-1`, `d₁ = Δ⁻¹-q⁻¹-24`, …).
-/
import Mathlib
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.cusp_inv_divisor_second
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Asymptotics.E4cube_cusp_second
import Submission.Work.Asymptotics.jInvariantFun_cusp_second
import Submission.Work.Kernels.KernelFacts.fk_slash

namespace Work.Asymptotics.Compact

open UpperHalfPlane
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

namespace K24

open Work.Kernels

/-! ## The atoms of the expansion -/

/-- `c = (36·1728·π⁻²·i)⁻¹`. -/
def cK : ℂ := ((36 : ℂ) * 1728 * ((Real.pi : ℂ)) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- `r0(τ) = τE₁₄(τ)`. -/
def r0 (τ : ℍ) : ℂ := (τ : ℂ) * E14Fun τ
/-- `r1(τ) = φ₀(τ)Δ(τ)`, `φ₀ = τE₂(τ) - 3i/π`. -/
def r1 (τ : ℍ) : ℂ := Compact.phi1 τ * DeltaFun τ
/-- `r2(τ) = φ₂(τ)E₁₀(τ)`, `φ₂ = τE₂(τ)² - (6i/π)E₂(τ)`. -/
def r2 (τ : ℍ) : ℂ := Compact.phi2t τ * E10Fun τ
/-- `R0(τ) = φ₀(τ)E₄(τ)³ = r1(τ)·j(τ)`. -/
def R0 (τ : ℍ) : ℂ := Compact.phi1 τ * E4Fun τ ^ 3

/-- `S0 z = 1 - 6i/(πz)`, the leading term of `E₂ˢ(z)`. -/
def S0 (z : ℍ) : ℂ := 1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))

/-- The `τ`-part of the bracket multiplying `Δ(z)⁻¹`. -/
def Pfun (τ z : ℍ) : ℂ :=
  r0 τ * (6 * E4Fun z - 6 * (E2S z) ^ 2)
    + r1 τ * ((-12 * jInvariantFun τ + 8640) * E4Fun z
        + (12 * jInvariantFun τ - 12096) * (E2S z) ^ 2)
    + r2 τ * (6 * E4Fun z - 6 * (E2S z) ^ 2)

/-- `U`: the coefficient of `(Δ(z))⁻¹`. -/
def Ufun (τ z : ℍ) : ℂ :=
  1728 * r0 τ * (E2S z) ^ 2 + 1728 * r2 τ * E4Fun z

/-- `V`: the coefficient of `(Δ(z)²)⁻¹`. -/
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

/-- `d1 = Δ(z)⁻¹ - q⁻¹ - 24`. -/
def d1 (z : ℍ) : ℂ := (DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24

/-! ## The five remainder groups -/

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

/-! ## The model coefficients -/

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

/-! ## Elementary identities -/

lemma qParamFun_eq_Ept_sq' (z : ℍ) : qParamFun z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
  congr 1; ring

/-- `(qParamFun z)⁻¹ = (Ept z)^{-2}`. -/
lemma qinv_eq (z : ℍ) : (qParamFun z)⁻¹ = Work.Residues.Ept z ^ (-2 : ℤ) := by
  rw [show (-2 : ℤ) = -((2 : ℤ)) by norm_num, zpow_neg, zpow_ofNat, qParamFun_eq_Ept_sq' z]

/-- `Compact.Gplus 24 = c (q⁻¹(A1 z + A0) + (B1 z + B0))`. -/
lemma Gplus24_eq (τ z : ℍ) :
    Compact.Gplus 24 τ z = cK * ((qParamFun z)⁻¹ * (A1 τ z * (z : ℂ) + A0 τ z)
      + (B1 τ z * (z : ℂ) + B0 τ z)) := by
  have hq : Work.Residues.Ept z ^ (-2 : ℤ) = (qParamFun z)⁻¹ := (qinv_eq z).symm
  rw [Compact.Gplus, if_neg (by norm_num : ¬ (24 = 8)), Compact.Gplus24, hq]
  simp only [cK, A1, A0, B1, B0]
  ring

lemma E4_cube_add_J (τ z : ℍ) :
    (jInvariantFun τ - jInvariantFun z) * DeltaFun z + E4Fun z ^ 3
      = DeltaFun z * jInvariantFun τ := by
  rw [sub_mul, mul_comm (jInvariantFun z) (DeltaFun z),
    ← ClassicalFacts.DeltaFun_mul_jInvariantFun z]
  ring

/-- `j(τ)Δ(z) - E₄(z)³ = Δ(z)(j(τ)-j(z))`. -/
lemma mul_J_sub (τ z : ℍ) :
    jInvariantFun τ * DeltaFun z - E4Fun z ^ 3
      = DeltaFun z * (jInvariantFun τ - jInvariantFun z) := by
  rw [mul_comm (jInvariantFun τ) (DeltaFun z), ← E4_cube_add_J τ z]
  ring

/-- `r1 τ * j(τ) = R0 τ`. -/
lemma r1_mul_j (τ : ℍ) : r1 τ * jInvariantFun τ = R0 τ := by
  rw [r1, R0, mul_assoc, ClassicalFacts.DeltaFun_mul_jInvariantFun]

lemma A1_eq_Ac1 (τ z : ℍ) : A1 τ z = Ac1 τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [A1, Ac1, r0, r1, r2]
  field_simp
  simp only [Complex.I_sq]
  ring

lemma A0_eq_Ac0 (τ z : ℍ) : A0 τ z = Ac0 τ z := by
  rw [A0, Ac0, r0, r1, r2]
  ring

lemma B1_eq_Bc1 (τ z : ℍ) : B1 τ z = Bc1 τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [B1, Bc1, r0, r1, jInvariantFun]
  field_simp
  simp only [Complex.I_sq]
  ring

lemma B0_eq_Bc0 (τ z : ℍ) : B0 τ z = Bc0 τ z := by
  rw [B0, Bc0, r0, r1, r2]
  ring

/-- The pointwise forms of the `f_k` at the weights occurring in `Υ_+^{(24)}`. -/
lemma fk_two_pt (z : ℍ) : fk 2 z = E14Fun z / DeltaFun z := by
  simpa using congrFun KernelFacts.fk_two z
lemma fk_four_pt (z : ℍ) : fk 4 z = E4Fun z := by
  simpa using congrFun KernelFacts.fk_four z
lemma fk_zero_pt (z : ℍ) : fk 0 z = 1 := by
  simpa using congrFun KernelFacts.fk_zero z
lemma fk_ten_pt (z : ℍ) : fk 10 z = E10Fun z := by
  simpa using congrFun KernelFacts.fk_ten z
lemma fk_twelve_pt (z : ℍ) : fk 12 z = DeltaFun z := by
  simpa using congrFun KernelFacts.fk_twelve z
lemma fk_fourteen_pt (z : ℍ) : fk 14 z = E14Fun z := by
  simpa using congrFun KernelFacts.fk_fourteen z

/-- **The bracket `S`**: `K₊^{(24)}(τ,z) = c·Δ(z)⁻¹·S(τ,z)`. -/
def Sbr (τ z : ℍ) : ℂ :=
  ((τ:ℂ) * E14Fun τ) * (6 * ((z:ℂ)^2 * E4Fun z)
      + (1728 * (jInvariantFun τ - jInvariantFun z)⁻¹ - 6) * ((z:ℂ)^2 * (E2S z)^2))
  + (Work.Kernels.phi0 τ * DeltaFun τ) * ((-12 * jInvariantFun τ + 5 * (1728:ℂ)) * ((z:ℂ)^2 * E4Fun z)
      - 2 * 1728 * (jInvariantFun τ - jInvariantFun z)⁻¹
          * ((E14Fun z / DeltaFun z) * ((z:ℂ)^2 * E2S z))
      + (12 * jInvariantFun τ - 7 * (1728:ℂ)) * ((z:ℂ)^2 * (E2S z)^2))
  + (Work.Kernels.phi2 τ * E10Fun τ) * ((1728 * (jInvariantFun τ - jInvariantFun z)⁻¹ + 6) * ((z:ℂ)^2 * E4Fun z)
      - 6 * ((z:ℂ)^2 * (E2S z)^2))

/-- **Unfolding `K₊^{(24)}`**: it is `c Δ(z)⁻¹` times the bracket `S`. -/
lemma KPlus24_eq_Sbr (τ z : ℍ) :
    KPlus 24 τ z = cK * (DeltaFun z)⁻¹ * Sbr τ z := by
  simp only [KPlus, UpsilonPlus, if_neg (by norm_num : ¬ ((24 : ℕ) = 8)), if_true,
    PiMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    phiVec, phitVec, phiNeg2, c1728, cK,
    fk_two_pt, fk_four_pt, fk_zero_pt, fk_ten_pt, fk_twelve_pt, fk_fourteen_pt,
    Pi.one_apply, one_mul, mul_one, Sbr]
  ring

/-- **The algebraic core of the cusp expansion** (free variables). -/
lemma Sbr_algebra (c z Jd Δ E4z E2Sz E14z r0 r1 r2 jT : ℂ) (hΔ : Δ ≠ 0) (hJd : Jd ≠ 0) :
    Jd * (c * Δ⁻¹ * (r0 * (6 * (z^2 * E4z) + (1728 * Jd⁻¹ - 6) * ((z * E2Sz)^2))
        + r1 * ((-12 * jT + 5 * 1728) * (z^2 * E4z)
            - 2 * 1728 * Jd⁻¹ * ((E14z / Δ) * (z^2 * E2Sz))
            + (12 * jT - 7 * 1728) * ((z * E2Sz)^2))
        + r2 * ((1728 * Jd⁻¹ + 6) * (z^2 * E4z) - 6 * ((z * E2Sz)^2))))
      = c * z^2 * (Jd * (r0 * (6 * E4z - 6 * E2Sz^2)
            + r1 * ((-12 * jT + 8640) * E4z + (12 * jT - 12096) * E2Sz^2)
            + r2 * (6 * E4z - 6 * E2Sz^2)) / Δ
          + (1728 * r0 * E2Sz^2 + 1728 * r2 * E4z) / Δ
          + (-3456 * r1 * E14z * E2Sz) / Δ^2) := by
  field_simp
  ring

/-- **The cusp form of `K₊^{(24)}`.**  Multiplying by `J = j(τ)-j(z)` clears the pole. -/
lemma KPlus24_cusp (τ z : ℍ) (hJ : jInvariantFun τ - jInvariantFun z ≠ 0) :
    (jInvariantFun τ - jInvariantFun z) * KPlus 24 τ z
      = cK * (z : ℂ) ^ 2 * ((jInvariantFun τ - jInvariantFun z) * Pfun τ z / DeltaFun z
          + Ufun τ z / DeltaFun z + Vfun τ z / DeltaFun z ^ 2) := by
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  rw [KPlus24_eq_Sbr τ z]
  rw [show Sbr τ z
      = ((τ:ℂ) * E14Fun τ) * (6 * ((z:ℂ)^2 * E4Fun z)
          + (1728 * (jInvariantFun τ - jInvariantFun z)⁻¹ - 6) * (((z:ℂ) * E2S z)^2))
        + (Work.Kernels.phi0 τ * DeltaFun τ) * ((-12 * jInvariantFun τ + 5 * (1728:ℂ)) * ((z:ℂ)^2 * E4Fun z)
            - 2 * 1728 * (jInvariantFun τ - jInvariantFun z)⁻¹
                * ((E14Fun z / DeltaFun z) * ((z:ℂ)^2 * E2S z))
            + (12 * jInvariantFun τ - 7 * (1728:ℂ)) * (((z:ℂ) * E2S z)^2))
        + (Work.Kernels.phi2 τ * E10Fun τ) * ((1728 * (jInvariantFun τ - jInvariantFun z)⁻¹ + 6)
            * ((z:ℂ)^2 * E4Fun z) - 6 * (((z:ℂ) * E2S z)^2)) from by
      rw [Sbr]; ring]
  rw [show Pfun τ z = ((τ:ℂ) * E14Fun τ) * (6 * E4Fun z - 6 * (E2S z)^2)
        + (Compact.phi1 τ * DeltaFun τ) * ((-12 * jInvariantFun τ + 8640) * E4Fun z
            + (12 * jInvariantFun τ - 12096) * (E2S z)^2)
        + (Compact.phi2t τ * E10Fun τ) * (6 * E4Fun z - 6 * (E2S z)^2) from rfl]
  rw [show Ufun τ z = 1728 * ((τ:ℂ) * E14Fun τ) * (E2S z)^2
        + 1728 * (Compact.phi2t τ * E10Fun τ) * E4Fun z from rfl]
  rw [show Vfun τ z = -3456 * (Compact.phi1 τ * DeltaFun τ) * E14Fun z * E2S z from rfl]
  exact Sbr_algebra cK (z:ℂ) (jInvariantFun τ - jInvariantFun z) (DeltaFun z) (E4Fun z)
    (E2S z) (E14Fun z) ((τ:ℂ) * E14Fun τ) (Work.Kernels.phi0 τ * DeltaFun τ)
    (Work.Kernels.phi2 τ * E10Fun τ) (jInvariantFun τ) hD hJ

/-- **The matching identity at order `q⁻¹`**: `z²Φref = A1 z + A0`. -/
lemma Gplus24_A1A0 (τ z : ℍ) :
    (z : ℂ) ^ 2 * Phiref τ z = A1 τ z * (z : ℂ) + A0 τ z := by
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hz : (z : ℂ) ≠ 0 := fun h => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h]; simp)
  rw [A1_eq_Ac1, A0_eq_Ac0]
  simp only [Phiref, Pref, Ac1, Ac0, S0, r0, r1, r2, jInvariantFun]
  field_simp
  ring_nf
  try simp only [Complex.I_sq]
  ring

/-- **The matching identity at order `q⁰`**: `z²Θ0 = B1 z + B0`. -/
lemma Gplus24_B1B0 (τ z : ℍ) :
    (z : ℂ) ^ 2 * Th0 τ z = B1 τ z * (z : ℂ) + B0 τ z := by
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hz : (z : ℂ) ≠ 0 := fun h => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h]; simp)
  rw [B1_eq_Bc1, B0_eq_Bc0]
  simp only [Th0, Q1, P1, Phiref, Pref, Uref, Bc1, Bc0, S0, r0, r1, r2, R0, jInvariantFun]
  field_simp
  ring_nf
  try simp only [Complex.I_sq]
  ring

/-- `Gplus 24 = c z²(Φref/q + Θ0)`. -/
lemma Gplus24_eq' (τ z : ℍ) :
    Compact.Gplus 24 τ z = cK * (z : ℂ) ^ 2 * (Phiref τ z / qParamFun z + Th0 τ z) := by
  rw [Gplus24_eq, ← Gplus24_A1A0, ← Gplus24_B1B0, div_eq_inv_mul]
  ring

/-- `φ₀(τ)E₄(τ)³ = (φ₀(τ)Δ(τ))·j(τ)`, i.e. `R0 τ = r1 τ · j(τ)`. -/
lemma phi1_E4cube_eq (τ : ℍ) :
    Compact.phi1 τ * E4Fun τ ^ 3 = (Compact.phi1 τ * DeltaFun τ) * jInvariantFun τ := by
  rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  ring

/-- `Gplus24 = Compact.Gplus 24`. -/
lemma Gplus24_eq_Gplus (τ z : ℍ) : Gplus24 τ z = Compact.Gplus 24 τ z := rfl

/-- **The exact decomposition of the difference**: after clearing the pole at `j(τ) = j(z)`,
`Δ(z)(j(τ)-j(z))(K₊-𝒢₊)` is the sum of the five remainder groups `S₁,…,S₅`. -/
lemma KPlus24_diff (τ z : ℍ) (hJ : jInvariantFun τ - jInvariantFun z ≠ 0)
    (hE4 : E4Fun z ≠ 0) :
    DeltaFun z * (jInvariantFun τ - jInvariantFun z) * (KPlus 24 τ z - Gplus24 τ z)
      = cK * (z : ℂ) ^ 2 * (Sm1 τ z + Sm2 τ z + Sm3 τ z + Sm4 τ z + Sm5 τ z) := by
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hq : qParamFun z ≠ 0 := qParamFun_ne_zero' z
  have hz : (z : ℂ) ≠ 0 := fun h => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h]; simp)
  rw [show DeltaFun z * (jInvariantFun τ - jInvariantFun z) * (KPlus 24 τ z - Gplus24 τ z)
      = DeltaFun z * ((jInvariantFun τ - jInvariantFun z) * KPlus 24 τ z)
        - DeltaFun z * ((jInvariantFun τ - jInvariantFun z) * Gplus24 τ z) from by ring]
  rw [KPlus24_cusp τ z hJ, Gplus24_eq_Gplus τ z, Gplus24_eq']
  simp only [Sm1, Sm2, Sm3, Sm4, Sm5, d1, Phi, Pfun, Ufun, Vfun, Uref, Pref, Phiref, P1, Q1, Th0,
    R0, r0, r1, r2, S0, E14Fun, E10Fun, jInvariantFun, c1728]
  rw [phi1_E4cube_eq]
  simp only [div_eq_mul_inv, mul_inv]
  field_simp
  ring_nf
  try simp only [Complex.I_sq]
  try ring

end K24


open Work.Kernels

section Est

/-- The imaginary part of `imagAxis t ht` is `t`. -/
lemma imagAxis_im_eq (t : ℝ) (ht : 0 < t) : (imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

/-- `‖qParamFun (it)‖ = e^{-2πt}`. -/
lemma norm_qParamFun_axis (t : ℝ) (ht : 0 < t) :
    ‖qParamFun (imagAxis t ht)‖ = Real.exp (-(2 * Real.pi * t)) := by
  rw [Work.Asymptotics.norm_qParamFun, imagAxis_im_eq t ht]

/-- `‖(it : ℂ)‖ = t`. -/
lemma norm_coe_axis (t : ℝ) (ht : 0 < t) : ‖((imagAxis t ht : ℍ) : ℂ)‖ = t := by
  rw [show ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

/-- `(Ept z)⁻¹ ^ 2 = (qParamFun z)⁻¹`. -/
lemma Ept_inv_sq_eq (z : ℍ) : (Work.Residues.Ept z)⁻¹ ^ 2 = (qParamFun z)⁻¹ := by
  rw [inv_pow, ← K24.qParamFun_eq_Ept_sq' z]

/-- `E₄(it) → 1`. -/
lemma E4_axis_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
    ‖E4Fun (imagAxis t ht) - 1‖ ≤ C * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E4Fun_two_term
  refine ⟨C + 240 + 1, by positivity, fun t ht ht1 => ?_⟩
  have him : 1 ≤ (imagAxis t ht).im := by rw [imagAxis_im_eq t ht]; exact ht1
  have h1 := h _ him
  have h2 : E4Fun (imagAxis t ht) - 1
      = (E4Fun (imagAxis t ht) - 1 - 240 * qParamFun (imagAxis t ht))
        + 240 * qParamFun (imagAxis t ht) := by ring
  rw [h2]
  have hq : ‖qParamFun (imagAxis t ht)‖ = Real.exp (-(2 * Real.pi * t)) := norm_qParamFun_axis t ht
  have hq1 : ‖qParamFun (imagAxis t ht)‖ ≤ 1 := by
    rw [hq]; exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  calc ‖(E4Fun (imagAxis t ht) - 1 - 240 * qParamFun (imagAxis t ht))
          + 240 * qParamFun (imagAxis t ht)‖
      ≤ ‖E4Fun (imagAxis t ht) - 1 - 240 * qParamFun (imagAxis t ht)‖
          + ‖(240 : ℂ) * qParamFun (imagAxis t ht)‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun (imagAxis t ht)‖ ^ 2 + 240 * ‖qParamFun (imagAxis t ht)‖ := by
        rw [norm_mul, Complex.norm_ofNat]
        exact add_le_add h1 (le_refl _)
    _ ≤ (C + 240 + 1) * Real.exp (-(2 * Real.pi * t)) := by
        rw [hq]
        have hqpos : 0 < Real.exp (-(2 * Real.pi * t)) := Real.exp_pos _
        have : Real.exp (-(2 * Real.pi * t)) ^ 2 ≤ Real.exp (-(2 * Real.pi * t)) := by
          nlinarith [hqpos, Real.exp_nonneg (-(2 * Real.pi * t)), hq1]
        nlinarith [hC.le, this, hqpos]

/-- `E₆(it) → 1`. -/
lemma E6_axis_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
    ‖E6Fun (imagAxis t ht) - 1‖ ≤ C * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E6Fun_two_term
  refine ⟨C + 504 + 1, by positivity, fun t ht ht1 => ?_⟩
  have him : 1 ≤ (imagAxis t ht).im := by rw [imagAxis_im_eq t ht]; exact ht1
  have h1 := h _ him
  have h2 : E6Fun (imagAxis t ht) - 1
      = (E6Fun (imagAxis t ht) - 1 + 504 * qParamFun (imagAxis t ht))
        - 504 * qParamFun (imagAxis t ht) := by ring
  rw [h2]
  have hq : ‖qParamFun (imagAxis t ht)‖ = Real.exp (-(2 * Real.pi * t)) := norm_qParamFun_axis t ht
  have hq1 : ‖qParamFun (imagAxis t ht)‖ ≤ 1 := by
    rw [hq]; exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  calc ‖(E6Fun (imagAxis t ht) - 1 + 504 * qParamFun (imagAxis t ht))
          - 504 * qParamFun (imagAxis t ht)‖
      ≤ ‖E6Fun (imagAxis t ht) - 1 + 504 * qParamFun (imagAxis t ht)‖
          + ‖(504 : ℂ) * qParamFun (imagAxis t ht)‖ := norm_sub_le _ _
    _ ≤ C * ‖qParamFun (imagAxis t ht)‖ ^ 2 + 504 * ‖qParamFun (imagAxis t ht)‖ := by
        rw [norm_mul, Complex.norm_ofNat]
        exact add_le_add h1 (le_refl _)
    _ ≤ (C + 504 + 1) * Real.exp (-(2 * Real.pi * t)) := by
        rw [hq]
        have hqpos : 0 < Real.exp (-(2 * Real.pi * t)) := Real.exp_pos _
        have : Real.exp (-(2 * Real.pi * t)) ^ 2 ≤ Real.exp (-(2 * Real.pi * t)) := by
          nlinarith [hqpos, Real.exp_nonneg (-(2 * Real.pi * t)), hq1]
        nlinarith [hC.le, this, hqpos]

/-- `E₂(it) → 1`. -/
lemma E2_axis_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
    ‖E2Fun (imagAxis t ht) - 1‖ ≤ C * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E2Fun_two_term
  refine ⟨C + 24 + 1, by positivity, fun t ht ht1 => ?_⟩
  have him : 1 ≤ (imagAxis t ht).im := by rw [imagAxis_im_eq t ht]; exact ht1
  have h1 := h _ him
  have h2 : E2Fun (imagAxis t ht) - 1
      = (E2Fun (imagAxis t ht) - 1 + 24 * qParamFun (imagAxis t ht))
        - 24 * qParamFun (imagAxis t ht) := by ring
  rw [h2]
  have hq : ‖qParamFun (imagAxis t ht)‖ = Real.exp (-(2 * Real.pi * t)) := norm_qParamFun_axis t ht
  have hq1 : ‖qParamFun (imagAxis t ht)‖ ≤ 1 := by
    rw [hq]; exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  calc ‖(E2Fun (imagAxis t ht) - 1 + 24 * qParamFun (imagAxis t ht))
          - 24 * qParamFun (imagAxis t ht)‖
      ≤ ‖E2Fun (imagAxis t ht) - 1 + 24 * qParamFun (imagAxis t ht)‖
          + ‖(24 : ℂ) * qParamFun (imagAxis t ht)‖ := norm_sub_le _ _
    _ ≤ C * ‖qParamFun (imagAxis t ht)‖ ^ 2 + 24 * ‖qParamFun (imagAxis t ht)‖ := by
        rw [norm_mul, Complex.norm_ofNat]
        exact add_le_add h1 (le_refl _)
    _ ≤ (C + 24 + 1) * Real.exp (-(2 * Real.pi * t)) := by
        rw [hq]
        have hqpos : 0 < Real.exp (-(2 * Real.pi * t)) := Real.exp_pos _
        have : Real.exp (-(2 * Real.pi * t)) ^ 2 ≤ Real.exp (-(2 * Real.pi * t)) := by
          nlinarith [hqpos, Real.exp_nonneg (-(2 * Real.pi * t)), hq1]
        nlinarith [hC.le, this, hqpos]


end Est

end
end Work.Asymptotics.Compact
