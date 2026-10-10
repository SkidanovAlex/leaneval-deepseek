import Submission.Work.MotC5N3.RulingX2.GamCert.Ids0
import Submission.Work.MotC5N3.RulingX2.GamCert.Ids1
import Submission.Work.MotC5N3.RulingX2.GamCert.Ids2
import Submission.Work.MotC5N3.RulingX2.GamCert.Ids3
import Submission.Work.MotC5N3.RulingX2.GamCert.Ids4
import Submission.Work.MotC5N3.RulingX2.SlicePhi
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotC5N3.RulingX2

open MvPolynomial
open Work.MotC5N3.RulingX2.GamCert

variable {K : Type*} [Field K] [CharP K 5]

/-!
# `Slice.fhatF k` lies in the ideal `(Phisq, Gam, PhatPoly)`

`Slice.Phisq = X 0 ^ 2 + PhiAlpha * X 0 + PhiBeta` has coefficients with denominator
`2 * (a - 3 * b) ^ 5`; its numerator-cleared form is `P1_ = E_ * X0_ ^ 2 + c1_ * X0_ + c0_`
(`GamCert`), where `E_ = C (2 * (a - 3 * b) ^ 5)` and `c1_`/`c0_` are the numerators of
`PhiAlpha`/`PhiBeta`.  The lemmas `zsgm_hAlpha`, `zsgm_hBeta`, `zsgm_hP1` are the coefficient-wise
comparison, and give `P1_ = E_ * Phisq`, hence `P1_ ∈ (Phisq, ...)` (`E_` is a unit).

The five certificates `GamCert.Idents.idR_k`, `idA_k`, `idB_k` (proved over `K` by reducing the
integer coefficients modulo the characteristic `5`) give
`E_ ^ 3 * fhat_k = (E_ * Eq_k - Y_k * Dh_) * P1_ + (Z_k + E_ * Y_k * X0_) * Gam
  - (W0_k + W1_k * X0_) * P_`,
which exhibits `E_ ^ 3 * fhat_k` in the ideal; dividing by the unit `E_ ^ 3` finishes. -/

theorem zsgm_hEk (a b g : K) :
    E_ (K := K) a b g = C ((2 : K) * (a - 3 * b) ^ 5) := by
  dsimp only [E_]
  rw [← map_add]
  congr 1
  ring_nf
  try reduce_mod_char!
  try ring

theorem zsgm_hfac (a b : K) :
    a ^ 2 - a * b - b ^ 2 = (a - 3 * b) * (a + 2 * b) := by
  ring_nf
  try reduce_mod_char!
  try ring

theorem zsgm_two_ne (a b : K) : (2 : K) ≠ 0 := by
  intro h
  have h5 : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp h
  norm_num at h5

theorem zsgm_hden (a b : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    (2 : K) * (a - 3 * b) ^ 5 ≠ 0 := by
  have h3 : a - 3 * b ≠ 0 := fun h => ha (by rw [zsgm_hfac, h, zero_mul])
  exact mul_ne_zero (zsgm_two_ne a b) (pow_ne_zero 5 h3)

theorem zsgm_hAlpha (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    E_ (K := K) a b g * Slice.PhiAlpha a b g = c1_ (K := K) a b g := by
  rw [zsgm_hEk]
  dsimp only [Slice.PhiAlpha, c1_]
  simp only [pow_one]
  set den : K := (2 : K) * (a - 3 * b) ^ 5 with hd
  have hne : den ≠ 0 := by rw [hd]; exact zsgm_hden a b ha
  have hmul : ∀ n : K, den * (n * den⁻¹) = n := by
    intro n
    rw [mul_comm n _, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  simp only [mul_add, ← mul_assoc, ← map_mul, hmul]
  first | refl_ring1 | ring

theorem zsgm_hBeta (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    E_ (K := K) a b g * Slice.PhiBeta a b g = c0_ (K := K) a b g := by
  rw [zsgm_hEk]
  dsimp only [Slice.PhiBeta, c0_]
  simp only [pow_one]
  set den : K := (2 : K) * (a - 3 * b) ^ 5 with hd
  have hne : den ≠ 0 := by rw [hd]; exact zsgm_hden a b ha
  have hmul : ∀ n : K, den * (n * den⁻¹) = n := by
    intro n
    rw [mul_comm n _, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  simp only [mul_add, ← mul_assoc, ← map_mul, hmul]
  first | refl_ring1 | ring

theorem zsgm_hP1 (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    P1_ (K := K) a b g = E_ (K := K) a b g * Slice.Phisq a b g := by
  have hA := zsgm_hAlpha a b g ha
  have hB := zsgm_hBeta a b g ha
  dsimp only [P1_, X0_, Slice.Phisq]
  rw [mul_add, mul_add, ← mul_assoc]
  rw [hA, hB]

theorem zsgm_Gam_eq (a b g : K) :
    Slice.Gam a b g = Dh_ (K := K) a b g * X0_ (K := K) + Rh_ (K := K) a b g := by
  dsimp only [Slice.Gam, Slice.Dhat, Slice.Rhat, Dh_, Rh_, X0_]
  first | refl_ring1 | ring

theorem zsgm_Phat_eq (a b g : K) :
    Slice.PhatPoly a b g = P_ (K := K) a b g := by
  dsimp only [Slice.PhatPoly, Slice.Phat, Slice.Phat_p0, Slice.Phat_p1, P_]
  first | refl_ring1 | ring

theorem zsgm_fhat0_mem (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    Slice.fhat0 a b g ∈
      Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} := by
  set I := Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} with hI
  have hPhisq : Slice.Phisq a b g ∈ I := Ideal.subset_span (by simp)
  have hGam : Slice.Gam a b g ∈ I := Ideal.subset_span (by simp)
  have hPhat : Slice.PhatPoly a b g ∈ I := Ideal.subset_span (by simp)
  have hP1m : P1_ (K := K) a b g ∈ I := by
    rw [zsgm_hP1 a b g ha]
    exact Ideal.mul_mem_left _ _ hPhisq
  have h1 := Work.MotC5N3.RulingX2.GamCert.Idents.idR_0 a b g
  have h2 := Work.MotC5N3.RulingX2.GamCert.Idents.idA_0 a b g
  have h3 := Work.MotC5N3.RulingX2.GamCert.Idents.idB_0 a b g
  have hP1d : P1_ (K := K) a b g
      = E_ (K := K) a b g * X0_ (K := K) ^ 2 + c1_ (K := K) a b g * X0_ (K := K)
        + c0_ (K := K) a b g := rfl
  have hkey : E_ (K := K) a b g ^ 3 * Slice.fhat0 a b g
      = (E_ (K := K) a b g * Eq_0 (K := K) a b g - Y_0 (K := K) a b g * Dh_ (K := K) a b g)
          * P1_ (K := K) a b g
        + (Z_0 (K := K) a b g + E_ (K := K) a b g * Y_0 (K := K) a b g * X0_ (K := K))
          * Slice.Gam a b g
        - (W0_0 (K := K) a b g + W1_0 (K := K) a b g * X0_ (K := K)) * Slice.PhatPoly a b g := by
    rw [zsgm_Gam_eq, zsgm_Phat_eq]
    linear_combination (norm := first | refl_ring1 | ring1) (E_ (K := K) a b g) * h1 + h2 + X0_ (K := K) * h3
      + (Y_0 (K := K) a b g * Dh_ (K := K) a b g) * hP1d
  have hmem : E_ (K := K) a b g ^ 3 * Slice.fhat0 a b g ∈ I := by
    rw [hkey]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hP1m
    · exact Ideal.mul_mem_left _ _ hGam
    · exact Ideal.mul_mem_left _ _ hPhat
  have hEv : (2 : K) * (a - 3 * b) ^ 5 ≠ 0 := zsgm_hden a b ha
  have hscal : ((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3 * ((2 : K) * (a - 3 * b) ^ 5) ^ 3 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hEv, one_pow]
  have hfin : Slice.fhat0 a b g
      = C (((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3)
          * (E_ (K := K) a b g ^ 3 * Slice.fhat0 a b g) := by
    rw [zsgm_hEk, ← map_pow, ← mul_assoc, ← map_mul, hscal, map_one, one_mul]
  rw [hfin]
  exact Ideal.mul_mem_left _ _ hmem

theorem zsgm_fhat1_mem (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    Slice.fhat1 a b g ∈
      Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} := by
  set I := Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} with hI
  have hPhisq : Slice.Phisq a b g ∈ I := Ideal.subset_span (by simp)
  have hGam : Slice.Gam a b g ∈ I := Ideal.subset_span (by simp)
  have hPhat : Slice.PhatPoly a b g ∈ I := Ideal.subset_span (by simp)
  have hP1m : P1_ (K := K) a b g ∈ I := by
    rw [zsgm_hP1 a b g ha]
    exact Ideal.mul_mem_left _ _ hPhisq
  have h1 := Work.MotC5N3.RulingX2.GamCert.Idents.idR_1 a b g
  have h2 := Work.MotC5N3.RulingX2.GamCert.Idents.idA_1 a b g
  have h3 := Work.MotC5N3.RulingX2.GamCert.Idents.idB_1 a b g
  have hP1d : P1_ (K := K) a b g
      = E_ (K := K) a b g * X0_ (K := K) ^ 2 + c1_ (K := K) a b g * X0_ (K := K)
        + c0_ (K := K) a b g := rfl
  have hkey : E_ (K := K) a b g ^ 3 * Slice.fhat1 a b g
      = (E_ (K := K) a b g * Eq_1 (K := K) a b g - Y_1 (K := K) a b g * Dh_ (K := K) a b g)
          * P1_ (K := K) a b g
        + (Z_1 (K := K) a b g + E_ (K := K) a b g * Y_1 (K := K) a b g * X0_ (K := K))
          * Slice.Gam a b g
        - (W0_1 (K := K) a b g + W1_1 (K := K) a b g * X0_ (K := K)) * Slice.PhatPoly a b g := by
    rw [zsgm_Gam_eq, zsgm_Phat_eq]
    linear_combination (norm := first | refl_ring1 | ring1) (E_ (K := K) a b g) * h1 + h2 + X0_ (K := K) * h3
      + (Y_1 (K := K) a b g * Dh_ (K := K) a b g) * hP1d
  have hmem : E_ (K := K) a b g ^ 3 * Slice.fhat1 a b g ∈ I := by
    rw [hkey]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hP1m
    · exact Ideal.mul_mem_left _ _ hGam
    · exact Ideal.mul_mem_left _ _ hPhat
  have hEv : (2 : K) * (a - 3 * b) ^ 5 ≠ 0 := zsgm_hden a b ha
  have hscal : ((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3 * ((2 : K) * (a - 3 * b) ^ 5) ^ 3 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hEv, one_pow]
  have hfin : Slice.fhat1 a b g
      = C (((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3)
          * (E_ (K := K) a b g ^ 3 * Slice.fhat1 a b g) := by
    rw [zsgm_hEk, ← map_pow, ← mul_assoc, ← map_mul, hscal, map_one, one_mul]
  rw [hfin]
  exact Ideal.mul_mem_left _ _ hmem

theorem zsgm_fhat2_mem (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    Slice.fhat2 a b g ∈
      Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} := by
  set I := Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} with hI
  have hPhisq : Slice.Phisq a b g ∈ I := Ideal.subset_span (by simp)
  have hGam : Slice.Gam a b g ∈ I := Ideal.subset_span (by simp)
  have hPhat : Slice.PhatPoly a b g ∈ I := Ideal.subset_span (by simp)
  have hP1m : P1_ (K := K) a b g ∈ I := by
    rw [zsgm_hP1 a b g ha]
    exact Ideal.mul_mem_left _ _ hPhisq
  have h1 := Work.MotC5N3.RulingX2.GamCert.Idents.idR_2 a b g
  have h2 := Work.MotC5N3.RulingX2.GamCert.Idents.idA_2 a b g
  have h3 := Work.MotC5N3.RulingX2.GamCert.Idents.idB_2 a b g
  have hP1d : P1_ (K := K) a b g
      = E_ (K := K) a b g * X0_ (K := K) ^ 2 + c1_ (K := K) a b g * X0_ (K := K)
        + c0_ (K := K) a b g := rfl
  have hkey : E_ (K := K) a b g ^ 3 * Slice.fhat2 a b g
      = (E_ (K := K) a b g * Eq_2 (K := K) a b g - Y_2 (K := K) a b g * Dh_ (K := K) a b g)
          * P1_ (K := K) a b g
        + (Z_2 (K := K) a b g + E_ (K := K) a b g * Y_2 (K := K) a b g * X0_ (K := K))
          * Slice.Gam a b g
        - (W0_2 (K := K) a b g + W1_2 (K := K) a b g * X0_ (K := K)) * Slice.PhatPoly a b g := by
    rw [zsgm_Gam_eq, zsgm_Phat_eq]
    linear_combination (norm := first | refl_ring1 | ring1) (E_ (K := K) a b g) * h1 + h2 + X0_ (K := K) * h3
      + (Y_2 (K := K) a b g * Dh_ (K := K) a b g) * hP1d
  have hmem : E_ (K := K) a b g ^ 3 * Slice.fhat2 a b g ∈ I := by
    rw [hkey]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hP1m
    · exact Ideal.mul_mem_left _ _ hGam
    · exact Ideal.mul_mem_left _ _ hPhat
  have hEv : (2 : K) * (a - 3 * b) ^ 5 ≠ 0 := zsgm_hden a b ha
  have hscal : ((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3 * ((2 : K) * (a - 3 * b) ^ 5) ^ 3 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hEv, one_pow]
  have hfin : Slice.fhat2 a b g
      = C (((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3)
          * (E_ (K := K) a b g ^ 3 * Slice.fhat2 a b g) := by
    rw [zsgm_hEk, ← map_pow, ← mul_assoc, ← map_mul, hscal, map_one, one_mul]
  rw [hfin]
  exact Ideal.mul_mem_left _ _ hmem

theorem zsgm_fhat3_mem (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    Slice.fhat3 a b g ∈
      Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} := by
  set I := Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} with hI
  have hPhisq : Slice.Phisq a b g ∈ I := Ideal.subset_span (by simp)
  have hGam : Slice.Gam a b g ∈ I := Ideal.subset_span (by simp)
  have hPhat : Slice.PhatPoly a b g ∈ I := Ideal.subset_span (by simp)
  have hP1m : P1_ (K := K) a b g ∈ I := by
    rw [zsgm_hP1 a b g ha]
    exact Ideal.mul_mem_left _ _ hPhisq
  have h1 := Work.MotC5N3.RulingX2.GamCert.Idents.idR_3 a b g
  have h2 := Work.MotC5N3.RulingX2.GamCert.Idents.idA_3 a b g
  have h3 := Work.MotC5N3.RulingX2.GamCert.Idents.idB_3 a b g
  have hP1d : P1_ (K := K) a b g
      = E_ (K := K) a b g * X0_ (K := K) ^ 2 + c1_ (K := K) a b g * X0_ (K := K)
        + c0_ (K := K) a b g := rfl
  have hkey : E_ (K := K) a b g ^ 3 * Slice.fhat3 a b g
      = (E_ (K := K) a b g * Eq_3 (K := K) a b g - Y_3 (K := K) a b g * Dh_ (K := K) a b g)
          * P1_ (K := K) a b g
        + (Z_3 (K := K) a b g + E_ (K := K) a b g * Y_3 (K := K) a b g * X0_ (K := K))
          * Slice.Gam a b g
        - (W0_3 (K := K) a b g + W1_3 (K := K) a b g * X0_ (K := K)) * Slice.PhatPoly a b g := by
    rw [zsgm_Gam_eq, zsgm_Phat_eq]
    linear_combination (norm := first | refl_ring1 | ring1) (E_ (K := K) a b g) * h1 + h2 + X0_ (K := K) * h3
      + (Y_3 (K := K) a b g * Dh_ (K := K) a b g) * hP1d
  have hmem : E_ (K := K) a b g ^ 3 * Slice.fhat3 a b g ∈ I := by
    rw [hkey]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hP1m
    · exact Ideal.mul_mem_left _ _ hGam
    · exact Ideal.mul_mem_left _ _ hPhat
  have hEv : (2 : K) * (a - 3 * b) ^ 5 ≠ 0 := zsgm_hden a b ha
  have hscal : ((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3 * ((2 : K) * (a - 3 * b) ^ 5) ^ 3 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hEv, one_pow]
  have hfin : Slice.fhat3 a b g
      = C (((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3)
          * (E_ (K := K) a b g ^ 3 * Slice.fhat3 a b g) := by
    rw [zsgm_hEk, ← map_pow, ← mul_assoc, ← map_mul, hscal, map_one, one_mul]
  rw [hfin]
  exact Ideal.mul_mem_left _ _ hmem

theorem zsgm_fhat4_mem (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    Slice.fhat4 a b g ∈
      Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} := by
  set I := Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} with hI
  have hPhisq : Slice.Phisq a b g ∈ I := Ideal.subset_span (by simp)
  have hGam : Slice.Gam a b g ∈ I := Ideal.subset_span (by simp)
  have hPhat : Slice.PhatPoly a b g ∈ I := Ideal.subset_span (by simp)
  have hP1m : P1_ (K := K) a b g ∈ I := by
    rw [zsgm_hP1 a b g ha]
    exact Ideal.mul_mem_left _ _ hPhisq
  have h1 := Work.MotC5N3.RulingX2.GamCert.Idents.idR_4 a b g
  have h2 := Work.MotC5N3.RulingX2.GamCert.Idents.idA_4 a b g
  have h3 := Work.MotC5N3.RulingX2.GamCert.Idents.idB_4 a b g
  have hP1d : P1_ (K := K) a b g
      = E_ (K := K) a b g * X0_ (K := K) ^ 2 + c1_ (K := K) a b g * X0_ (K := K)
        + c0_ (K := K) a b g := rfl
  have hkey : E_ (K := K) a b g ^ 3 * Slice.fhat4 a b g
      = (E_ (K := K) a b g * Eq_4 (K := K) a b g - Y_4 (K := K) a b g * Dh_ (K := K) a b g)
          * P1_ (K := K) a b g
        + (Z_4 (K := K) a b g + E_ (K := K) a b g * Y_4 (K := K) a b g * X0_ (K := K))
          * Slice.Gam a b g
        - (W0_4 (K := K) a b g + W1_4 (K := K) a b g * X0_ (K := K)) * Slice.PhatPoly a b g := by
    rw [zsgm_Gam_eq, zsgm_Phat_eq]
    linear_combination (norm := first | refl_ring1 | ring1) (E_ (K := K) a b g) * h1 + h2 + X0_ (K := K) * h3
      + (Y_4 (K := K) a b g * Dh_ (K := K) a b g) * hP1d
  have hmem : E_ (K := K) a b g ^ 3 * Slice.fhat4 a b g ∈ I := by
    rw [hkey]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hP1m
    · exact Ideal.mul_mem_left _ _ hGam
    · exact Ideal.mul_mem_left _ _ hPhat
  have hEv : (2 : K) * (a - 3 * b) ^ 5 ≠ 0 := zsgm_hden a b ha
  have hscal : ((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3 * ((2 : K) * (a - 3 * b) ^ 5) ^ 3 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hEv, one_pow]
  have hfin : Slice.fhat4 a b g
      = C (((2 : K) * (a - 3 * b) ^ 5)⁻¹ ^ 3)
          * (E_ (K := K) a b g ^ 3 * Slice.fhat4 a b g) := by
    rw [zsgm_hEk, ← map_pow, ← mul_assoc, ← map_mul, hscal, map_one, one_mul]
  rw [hfin]
  exact Ideal.mul_mem_left _ _ hmem

theorem ZiasSliceGamMem (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) (k : Fin 5) :
    Work.MotC5N3.RulingX2.Slice.fhatF a b g k ∈
      Ideal.span {Work.MotC5N3.RulingX2.Slice.Phisq a b g,
                  Work.MotC5N3.RulingX2.Slice.Gam a b g,
                  Work.MotC5N3.RulingX2.Slice.PhatPoly a b g} := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by fin_cases k <;> decide
  rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;>
    simp only [Work.MotC5N3.RulingX2.Slice.fhatF, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue]
  · exact zsgm_fhat0_mem a b g ha
  · exact zsgm_fhat1_mem a b g ha
  · exact zsgm_fhat2_mem a b g ha
  · exact zsgm_fhat3_mem a b g ha
  · exact zsgm_fhat4_mem a b g ha

end Work.MotC5N3.RulingX2
