import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix


/-- The entry `(Π_{a}(x)·M·Π_{b}(y))_{im}` of a product of diagonal matrices. -/
private lemma PiMat_mul_apply_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (x y : ℍ) (i m : Fin 3) :
    (Work.Kernels.PiMat a x * M * Work.Kernels.PiMat b y) i m
      = Work.Kernels.fk (a i) x * M i m * Work.Kernels.fk (b m) y := by
  simp only [Work.Kernels.PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- The `(i,j)` entry of `Υ_+^{(8)}` written out. -/
private lemma UpsilonPlus_eight_apply (τ z : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonPlus 8 τ z i j =
      (((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))⁻¹) *
        (Work.Kernels.fk ((![6,4,2] : Fin 3 → ℤ) i) τ *
          ((!![Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z, 0, 1;
              -2*(Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), -2, 0; 1,0,0] :
              Matrix (Fin 3) (Fin 3) ℂ) i j) *
          Work.Kernels.fk ((![12,10,8] : Fin 3 → ℤ) j) z) := by
  simp only [Work.Kernels.UpsilonPlus, Matrix.smul_apply, ↓reduceIte, PiMat_mul_apply_entry,
    smul_eq_mul]

/-- `z^{-12}·z^{v_j}·z^{2j} = 1` for `v = (12,10,8)`. -/
private lemma pow_cancel (z : ℂ) (hz : z ≠ 0) (j : Fin 3) :
    z^(-12:ℤ) * z^((![12,10,8] : Fin 3 → ℤ) j) * z^(2 * (j:ℕ)) = 1 := by
  fin_cases j
  · norm_num
    exact inv_mul_cancel₀ (pow_ne_zero 12 hz)
  · norm_num
    rw [mul_assoc, ← pow_add, inv_mul_cancel₀ (pow_ne_zero 12 hz)]
  · norm_num
    rw [mul_assoc, ← pow_add, inv_mul_cancel₀ (pow_ne_zero 12 hz)]

/-- The scalar cancellation `c(ΔJ)·(cZΔJ)^{-1} = Z^{-1}`. -/
private lemma cancel_aux {c Z Δ J Y : ℂ} (hc : c ≠ 0) (hΔ : Δ ≠ 0) (hJ : J ≠ 0) :
    c * (Δ * J) * ((c * (Z * Δ) * J)⁻¹ * Y) = Z⁻¹ * Y := by
  have hA : c * Δ * J ≠ 0 := mul_ne_zero (mul_ne_zero hc hΔ) hJ
  have h1 : c * (Δ * J) * (c * Δ * J)⁻¹ = 1 := by
    have h : c * (Δ * J) = c * Δ * J := by ring
    rw [h, mul_inv_cancel₀ hA]
  have h2 : (c * (Z * Δ) * J)⁻¹ = (c * Δ * J)⁻¹ * Z⁻¹ := by
    rw [show c * (Z * Δ) * J = Z * (c * Δ * J) by ring, _root_.mul_inv_rev]
  rw [h2]
  calc c * (Δ * J) * ((c * Δ * J)⁻¹ * Z⁻¹ * Y)
      = (c * (Δ * J) * (c * Δ * J)⁻¹) * (Z⁻¹ * Y) := by ring
    _ = Z⁻¹ * Y := by rw [h1, one_mul]

/-- The purely algebraic core of the termwise computation. -/
private lemma scalar_key (c Z W PW E Δ J φ F MM g : ℂ) (hc : c ≠ 0) (hΔ : Δ ≠ 0) (hJ : J ≠ 0)
    (hpow : Z⁻¹ * W * PW = 1) :
    c * (Δ*J) * (φ * ((c*(Z*Δ)*J)⁻¹ * (F*MM*(W*g))) * (PW * E)) = φ * F * MM * g * E := by
  rw [show c*(Δ*J)*(φ * ((c*(Z*Δ)*J)⁻¹ * (F*MM*(W*g))) * (PW*E))
      = φ * (c*(Δ*J)*((c*(Z*Δ)*J)⁻¹ * (F*MM*(W*g)))) * (PW*E) by ring]
  rw [cancel_aux (Y := F*MM*(W*g)) hc hΔ hJ]
  rw [show φ * (Z⁻¹ * (F*MM*(W*g))) * (PW * E) = φ * F * MM * g * E * (Z⁻¹ * W * PW) by ring]
  rw [hpow, mul_one]

/-- Termwise form of the identity: the `(i,j)` summand of the left-hand side equals the
`(i,j)` summand of `Ξ_8`. -/
private lemma termwise (τ z : ℍ) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z)
    (i j : Fin 3) :
    ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) *
        (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
        (Work.Kernels.phiVec τ i * Work.Kernels.UpsilonPlus 8 τ (ModularGroup.S • z) i j *
            ((z : ℂ) ^ 2 * Work.Kernels.phitVec (ModularGroup.S • z) j))
      = Work.Kernels.phiVec τ i * Work.Kernels.fk ((![6,4,2] : Fin 3 → ℤ) i) τ *
          ((!![Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z, 0, 1;
              -2*(Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), -2, 0; 1, 0, 0] :
              Matrix (Fin 3) (Fin 3) ℂ) i j) *
          Work.Kernels.fk ((![12,10,8] : Fin 3 → ℤ) j) z * Work.Kernels.E2Fun z ^ (j : ℕ) := by
  have hz : (z : ℂ) ≠ 0 := Work.Kernels.KernelFacts.kpc_tau_ne_zero z
  have hDne : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hJne : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 := sub_ne_zero.mpr h
  have hCne : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have hDzS : Work.Kernels.DeltaFun (ModularGroup.S • z)
      = (z : ℂ) ^ (12 : ℤ) * Work.Kernels.DeltaFun z :=
    Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.DeltaFun_S_slash z
  have hfk : Work.Kernels.fk ((![12,10,8] : Fin 3 → ℤ) j) (ModularGroup.S • z)
      = (z : ℂ) ^ ((![12,10,8] : Fin 3 → ℤ) j) * Work.Kernels.fk ((![12,10,8] : Fin 3 → ℤ) j) z :=
    Work.Kernels.KernelFacts.fk_S_smul _ (by fin_cases j <;> decide) z
  have hphit : (z : ℂ) ^ 2 * Work.Kernels.phitVec (ModularGroup.S • z) j
      = (z : ℂ) ^ (2 * (j : ℕ)) * Work.Kernels.E2Fun z ^ (j : ℕ) := by
    rw [mul_comm]; exact Work.Asymptotics.phitVec_S_smul z j
  have hpow : ((z : ℂ)^(12:ℤ))⁻¹ * (z : ℂ)^((![12,10,8] : Fin 3 → ℤ) j) *
      (z : ℂ)^(2 * (j:ℕ)) = 1 := by
    have h0 : ((z : ℂ)^(12:ℤ))⁻¹ = z^(-12:ℤ) := by
      rw [← _root_.zpow_neg]
    rw [h0]; exact pow_cancel z hz j
  rw [UpsilonPlus_eight_apply τ (ModularGroup.S • z) i j,
      Work.Kernels.KernelFacts.jInvariantFun_S_smul z, hDzS, hfk, hphit]
  exact scalar_key ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) ((z:ℂ)^(12:ℤ))
    ((z:ℂ)^((![12,10,8]:Fin 3 → ℤ) j)) ((z:ℂ)^(2*(j:ℕ))) (Work.Kernels.E2Fun z ^ (j:ℕ))
    (Work.Kernels.DeltaFun z) (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
    (Work.Kernels.phiVec τ i) (Work.Kernels.fk ((![6,4,2]:Fin 3 → ℤ) i) τ)
    ((!![Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z, 0, 1;
        -2*(Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), -2, 0; 1,0,0] :
        Matrix (Fin 3) (Fin 3) ℂ) i j)
    (Work.Kernels.fk ((![12,10,8]:Fin 3 → ℤ) j) z)
    hCne hDne hJne hpow

theorem Xi8_eq (τ z : UpperHalfPlane) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) *
        (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
        ((z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)) = Work.Asymptotics.Xi8 τ z := by
  rw [Work.Asymptotics.Xi8, Work.Kernels.KPlus]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [show ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) *
        (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
        ((z : ℂ) ^ 2 *
          (Work.Kernels.phiVec τ i * Work.Kernels.UpsilonPlus 8 τ (ModularGroup.S • z) i j *
            Work.Kernels.phitVec (ModularGroup.S • z) j))
      = ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) *
        (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
        (Work.Kernels.phiVec τ i * Work.Kernels.UpsilonPlus 8 τ (ModularGroup.S • z) i j *
          ((z : ℂ) ^ 2 * Work.Kernels.phitVec (ModularGroup.S • z) j)) by ring]
  exact termwise τ z h i j

end Work.Asymptotics
