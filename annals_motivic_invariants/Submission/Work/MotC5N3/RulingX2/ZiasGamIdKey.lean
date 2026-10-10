import Submission.Work.MotC5N3.RulingX2.ZiasGamNeTopInfra
import Submission.Work.MotC5N3.RulingX2.ZiasGamIdE1
import Submission.Work.MotC5N3.RulingX2.ZiasGamIdE2
import Submission.Work.MotC5N3.RulingX2.ZiasGamIdE3
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.MotC5N3.RulingX2

open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

lemma PhiAlpha_eq (a b g : K) :
    Slice.PhiAlpha a b g = C ((2 * (a - 3 * b) ^ 5)⁻¹) * A0mv a b g := by
  dsimp only [Slice.PhiAlpha, A0mv, A0mv_0]
  simp only [map_add, map_mul, map_pow, map_one, map_zero, map_ofNat, MvPolynomial.C_mul]
  refl_ring1

lemma PhiBeta_eq (a b g : K) :
    Slice.PhiBeta a b g = C ((2 * (a - 3 * b) ^ 5)⁻¹) * B0mv a b g := by
  dsimp only [Slice.PhiBeta, B0mv, B0mv_0, B0mv_1]
  simp only [map_add, map_mul, map_pow, map_one, map_zero, map_ofNat, MvPolynomial.C_mul]
  refl_ring1

lemma A0mv_eq (a b g : K) (hden : (2 : K) * (a - 3 * b) ^ 5 ≠ 0) :
    A0mv a b g = C ((2 : K) * (a - 3 * b) ^ 5) * Slice.PhiAlpha a b g := by
  rw [PhiAlpha_eq]
  rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hden, MvPolynomial.C_1, one_mul]

lemma B0mv_eq (a b g : K) (hden : (2 : K) * (a - 3 * b) ^ 5 ≠ 0) :
    B0mv a b g = C ((2 : K) * (a - 3 * b) ^ 5) * Slice.PhiBeta a b g := by
  rw [PhiBeta_eq]
  rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hden, MvPolynomial.C_1, one_mul]

theorem key4 (a b g : K) :
    C (P4v a b g) * (E1v a b g - E2v a b g + E3v a b g)
      = C (N5v a b g) * X 1 * Slice.PhatPoly a b g + 5 * C4v a b g := by
  dsimp only [P4v, N5v, E1v, E1v_0, E1v_1, E1v_2, E1v_3, E1v_4, E1v_5, E1v_6, E1v_7, E1v_8,
    E1v_9, E1v_10, E2v, E2v_0, E2v_1, E2v_2, E2v_3, E2v_4, E2v_5, E2v_6, E2v_7, E2v_8, E2v_9,
    E2v_10, E3v, E3v_0, E3v_1, E3v_2, E3v_3, E3v_4, E3v_5, E3v_6, E3v_7, E3v_8, E3v_9, E3v_10,
    E3v_11, C4v, C4v_0, C4v_1, C4v_2, C4v_3, C4v_4, C4v_5, C4v_6, C4v_7, C4v_8, C4v_9, C4v_10,
    C4v_11, C4v_12, C4v_13, C4v_14, Slice.PhatPoly, Slice.Phat, Slice.Phat_p0, Slice.Phat_p1]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

lemma den_nrmMv (a b g : K) (hden : (2 : K) * (a - 3 * b) ^ 5 ≠ 0) :
    C ((2 : K) * (a - 3 * b) ^ 5) * nrmMv a b g
      = E1v a b g - E2v a b g + E3v a b g := by
  have hstep : C ((2 : K) * (a - 3 * b) ^ 5) * nrmMv a b g
      = C ((2 : K) * (a - 3 * b) ^ 5) * Slice.Rhat a b g ^ 2
        - (C ((2 : K) * (a - 3 * b) ^ 5) * Slice.PhiAlpha a b g) * Slice.Rhat a b g
            * Slice.Dhat a b g
        + (C ((2 : K) * (a - 3 * b) ^ 5) * Slice.PhiBeta a b g) * Slice.Dhat a b g ^ 2 := by
    simp only [nrmMv, mul_add, mul_sub, mul_assoc]
  rw [hstep, ← A0mv_eq a b g hden, ← B0mv_eq a b g hden, E1_eq, E2_eq, E3_eq]

lemma keymv (a b g : K) (hden : (2 : K) * (a - 3 * b) ^ 5 ≠ 0) :
    C (P4v a b g * ((2 : K) * (a - 3 * b) ^ 5)) * nrmMv a b g
      = C (N5v a b g) * X 1 * Slice.PhatPoly a b g := by
  have h4 := key4 a b g
  have hd := den_nrmMv a b g hden
  rw [← hd] at h4
  rw [show (5 : MvPolynomial (Fin 2) K) = 0 from CharP.cast_eq_zero _ 5, zero_mul, add_zero] at h4
  rwa [← mul_assoc, ← MvPolynomial.C_mul] at h4

lemma nrmMv_eq (a b g : K) (hden : (2 : K) * (a - 3 * b) ^ 5 ≠ 0) (hP4 : P4v a b g ≠ 0) :
    nrmMv a b g = C ((P4v a b g * ((2 : K) * (a - 3 * b) ^ 5))⁻¹)
      * (C (N5v a b g) * X 1 * Slice.PhatPoly a b g) := by
  have h := keymv a b g hden
  have hne : P4v a b g * ((2 : K) * (a - 3 * b) ^ 5) ≠ 0 := mul_ne_zero hP4 hden
  have hw : C ((P4v a b g * ((2 : K) * (a - 3 * b) ^ 5))⁻¹)
      * C (P4v a b g * ((2 : K) * (a - 3 * b) ^ 5)) = (1 : MvPolynomial (Fin 2) K) := by
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hne, MvPolynomial.C_1]
  calc nrmMv a b g
      = C ((P4v a b g * ((2 : K) * (a - 3 * b) ^ 5))⁻¹)
          * (C (P4v a b g * ((2 : K) * (a - 3 * b) ^ 5)) * nrmMv a b g) := by
        rw [← mul_assoc, hw, one_mul]
      _ = C ((P4v a b g * ((2 : K) * (a - 3 * b) ^ 5))⁻¹)
          * (C (N5v a b g) * X 1 * Slice.PhatPoly a b g) := by rw [h]

lemma Phat_dvd_nrmMv (a b g : K) (hden : (2 : K) * (a - 3 * b) ^ 5 ≠ 0)
    (hP4 : P4v a b g ≠ 0) : Slice.PhatPoly a b g ∣ nrmMv a b g :=
  ⟨C ((P4v a b g * ((2 : K) * (a - 3 * b) ^ 5))⁻¹) * C (N5v a b g) * X 1, by
    rw [nrmMv_eq a b g hden hP4]; ring⟩

end Work.MotC5N3.RulingX2
