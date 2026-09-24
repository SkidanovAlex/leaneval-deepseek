
import Mathlib

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.GM.Affine.crude_b

private lemma caseA {T Mbig J ε : ℝ} (hT : 0 ≤ T) (hMb : 1 ≤ Mbig) (hJ : 3 ≤ J)
    (h : T ^ (4 + 4*ε + 2*J) * Mbig ^ (6 - 2*J) ≤ Mbig ^ (6:ℝ)) :
    T ^ (2 + (4 + 4*ε)/J) * Mbig ^ (4:ℝ) ≤ Mbig ^ (6:ℝ) := by
  have hMbpos : 0 < Mbig := lt_of_lt_of_le one_pos hMb
  have hJpos : 0 < J := by linarith
  have h1 : T ^ (4 + 4*ε + 2*J) ≤ Mbig ^ (2*J) := by
    have hm := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (le_of_lt hMbpos) (2*J - 6))
    rw [mul_assoc, ← Real.rpow_add hMbpos (6 - 2*J) (2*J - 6),
        show (6 - 2*J) + (2*J - 6) = (0:ℝ) by ring, Real.rpow_zero, mul_one,
        ← Real.rpow_add hMbpos (6:ℝ) (2*J - 6),
        show (6:ℝ) + (2*J - 6) = 2*J by ring] at hm
    exact hm
  have h2 : T ^ (1 + (4 + 4*ε)/(2*J)) ≤ Mbig := by
    have hm : (T ^ (4 + 4*ε + 2*J)) ^ (1/(2*J)) ≤ (Mbig ^ (2*J)) ^ (1/(2*J)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hT (4 + 4*ε + 2*J)) h1
        (div_nonneg (by norm_num) (by linarith : (0:ℝ) ≤ 2*J))
    rw [(Real.rpow_mul hT (4 + 4*ε + 2*J) (1/(2*J))).symm,
        (Real.rpow_mul (le_of_lt hMbpos) (2*J) (1/(2*J))).symm] at hm
    rw [show (4 + 4*ε + 2*J) * (1/(2*J)) = 1 + (4+4*ε)/(2*J) by field_simp; try ring,
        show (2*J) * (1/(2*J)) = 1 by field_simp, Real.rpow_one] at hm
    exact hm
  have h3 : T ^ (2 + (4 + 4*ε)/J) ≤ Mbig ^ (2:ℝ) := by
    have hs : (T ^ (1 + (4 + 4*ε)/(2*J)))^2 ≤ Mbig^2 :=
      by nlinarith [h2, Real.rpow_nonneg hT (1 + (4+4*ε)/(2*J)), hMb]
    have e3 : (T ^ (1 + (4 + 4*ε)/(2*J)))^2 = T ^ (2 + (4 + 4*ε)/J) := by
      rw [← Real.rpow_natCast (T ^ (1 + (4 + 4*ε)/(2*J))) 2,
          ← Real.rpow_mul hT (1 + (4+4*ε)/(2*J)) ((2:ℕ):ℝ),
          show (1 + (4+4*ε)/(2*J)) * ((2:ℕ):ℝ) = 2 + (4+4*ε)/J by push_cast; field_simp]
    rw [e3, ← Real.rpow_natCast Mbig 2] at hs
    exact hs
  have h4 : T ^ (2 + (4 + 4*ε)/J) * Mbig ^ (4:ℝ) ≤ Mbig ^ (2:ℝ) * Mbig ^ (4:ℝ) :=
    mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (le_of_lt hMbpos) _)
  rw [← Real.rpow_add hMbpos (2:ℝ) (4:ℝ), show (2:ℝ) + 4 = (6:ℝ) by norm_num] at h4
  exact h4

private lemma caseB {T Mbig J ε : ℝ} (hT : 0 ≤ T) (hMb : 1 ≤ Mbig) (hJ : 3 ≤ J) (hε : 0 < ε)
    (h : Mbig ^ (6:ℝ) ≤ T ^ (4 + 4*ε + 2*J) * Mbig ^ (6 - 2*J)) :
    T ^ (2 + (4 + 4*ε)/J) * Mbig ^ (4:ℝ) ≤ T ^ (4 + 4*ε + 2*J) * Mbig ^ (6 - 2*J) := by
  have hMbpos : 0 < Mbig := lt_of_lt_of_le one_pos hMb
  have hJpos : 0 < J := by linarith
  have h1 : Mbig ^ (2*J) ≤ T ^ (4 + 4*ε + 2*J) := by
    have hm := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (le_of_lt hMbpos) (2*J - 6))
    rw [mul_assoc, ← Real.rpow_add hMbpos (6 - 2*J) (2*J - 6),
        show (6 - 2*J) + (2*J - 6) = (0:ℝ) by ring, Real.rpow_zero, mul_one,
        ← Real.rpow_add hMbpos (6:ℝ) (2*J - 6),
        show (6:ℝ) + (2*J - 6) = 2*J by ring] at hm
    exact hm
  have h2 : Mbig ^ (2*J - 2) ≤ T ^ (4 + 4*ε + 2*J - 2 - (4+4*ε)/J) := by
    have hm : (Mbig ^ (2*J)) ^ ((2*J-2)/(2*J)) ≤ (T ^ (4 + 4*ε + 2*J)) ^ ((2*J-2)/(2*J)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hMbpos) (2*J)) h1
        (div_nonneg (by linarith) (by linarith : (0:ℝ) ≤ 2*J))
    rw [(Real.rpow_mul (le_of_lt hMbpos) (2*J) ((2*J-2)/(2*J))).symm,
        (Real.rpow_mul hT (4+4*ε+2*J) ((2*J-2)/(2*J))).symm] at hm
    rw [show (2*J) * ((2*J-2)/(2*J)) = 2*J-2 by field_simp; try ring,
        show (4+4*ε+2*J) * ((2*J-2)/(2*J)) = 4+4*ε+2*J-2-(4+4*ε)/J by field_simp; try ring] at hm
    exact hm
  have h3 : Mbig ^ (4:ℝ) ≤ T ^ (4 + 4*ε + 2*J - 2 - (4+4*ε)/J) * Mbig ^ (6 - 2*J) := by
    have hmm : Mbig ^ (2*J - 2) * Mbig ^ (6 - 2*J) = Mbig ^ (4:ℝ) := by
      rw [← Real.rpow_add hMbpos (2*J-2) (6-2*J),
          show (2*J-2) + (6-2*J) = (4:ℝ) by ring]
    rw [← hmm]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hMbpos) (6 - 2*J))
  have h4 : T ^ (2 + (4 + 4*ε)/J) * Mbig ^ (4:ℝ) ≤
      T ^ (2 + (4 + 4*ε)/J) * (T ^ (4 + 4*ε + 2*J - 2 - (4+4*ε)/J) * Mbig ^ (6 - 2*J)) :=
    mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hT _)
  have hw : (4 + 4*ε + 2*J) ≠ 0 := by
    have hp : (0:ℝ) < 4 + 4*ε + 2*J := by linarith
    exact ne_of_gt hp
  have e2 : T ^ (2 + (4+4*ε)/J) * T ^ (4 + 4*ε + 2*J - 2 - (4+4*ε)/J) = T ^ (4 + 4*ε + 2*J) :=
    (Real.rpow_of_add_eq (x := T) (w := 4 + 4*ε + 2*J)
      (y := 2 + (4+4*ε)/J) (z := 4 + 4*ε + 2*J - 2 - (4+4*ε)/J) hT hw
      (by ring)).symm
  calc T ^ (2 + (4 + 4*ε)/J) * Mbig ^ (4:ℝ)
      ≤ T ^ (2 + (4 + 4*ε)/J) * (T ^ (4 + 4*ε + 2*J - 2 - (4+4*ε)/J) * Mbig ^ (6 - 2*J)) := h4
    _ = (T ^ (2 + (4 + 4*ε)/J) * T ^ (4 + 4*ε + 2*J - 2 - (4+4*ε)/J)) * Mbig ^ (6 - 2*J) := by ring
    _ = T ^ (4 + 4*ε + 2*J) * Mbig ^ (6 - 2*J) := by rw [e2]

private lemma key_bound {T Mbig cj c2 J ε : ℝ}
    (hε : 0 < ε) (hJ : 3 ≤ J) (hT : 0 ≤ T) (hMb : 1 ≤ Mbig) (hcj : 0 ≤ cj) (hc2 : 0 ≤ c2) :
    ((16 * cj * c2 * T ^ (J + 2 + 2*ε)) ^ (1/J))^2 * Mbig^(4:ℝ) ≤
      16^(2/J) * (cj*c2)^(2/J) *
        max (Mbig^(6:ℝ)) (T^(4 + 4*ε + 2*J) * Mbig^(6 - 2*J)) := by
  have hMbpos : 0 < Mbig := lt_of_lt_of_le one_pos hMb
  have hJpos : 0 < J := by linarith
  have hb : (0:ℝ) ≤ cj * c2 := mul_nonneg hcj hc2
  have hX : (0:ℝ) ≤ 16 * cj * c2 * T ^ (J + 2 + 2*ε) := by positivity
  have hY : ((16 * cj * c2 * T ^ (J + 2 + 2*ε)) ^ (1/J))^2 * Mbig^(4:ℝ)
      = 16^(2/J) * (cj*c2)^(2/J) * (T ^ (2 + (4 + 4*ε)/J) * Mbig^(4:ℝ)) := by
    have hb16 : (0:ℝ) ≤ 16 * (cj*c2) := by positivity
    have hTp : (0:ℝ) ≤ T ^ (J + 2 + 2*ε) := Real.rpow_nonneg hT (J + 2 + 2*ε)
    have hY2 : ((16 * cj * c2 * T ^ (J + 2 + 2*ε)) ^ (1/J))^2
        = (16 * cj * c2 * T ^ (J + 2 + 2*ε)) ^ (2/J) := by
      rw [← Real.rpow_natCast ((16 * cj * c2 * T ^ (J + 2 + 2*ε)) ^ (1/J)) 2,
          ← Real.rpow_mul hX (1/J) ((2:ℕ):ℝ),
          show (1/J) * ((2:ℕ):ℝ) = 2/J by push_cast; field_simp]
    rw [hY2, show (16 * cj * c2 * T ^ (J + 2 + 2*ε)) = (16 * (cj*c2)) * T ^ (J + 2 + 2*ε) by ring,
        Real.mul_rpow hb16 hTp, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hb,
        ← Real.rpow_mul hT (J + 2 + 2*ε) (2/J),
        show (J + 2 + 2*ε) * (2/J) = 2 + (4 + 4*ε)/J by field_simp; try ring]
    ring
  rw [hY]
  have hK0 : (0:ℝ) ≤ 16^(2/J) * (cj*c2)^(2/J) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hb _)
  rcases le_total (T ^ (4 + 4*ε + 2*J) * Mbig ^ (6 - 2*J)) (Mbig ^ (6:ℝ)) with hle | hle
  · rw [max_eq_left hle]
    exact mul_le_mul_of_nonneg_left (caseA hT hMb hJ hle) hK0
  · rw [max_eq_right hle]
    exact mul_le_mul_of_nonneg_left (caseB hT hMb hJ hε hle) hK0


theorem final_arith {C₀ K T Mbig U cj c2 : ℝ} {j : ℕ} {ε : ℝ}
    (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hj : 3 ≤ j) (hε : 0 < ε) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hMb : 1 ≤ Mbig) (hcj : 0 ≤ cj) (hc2 : 0 ≤ c2) :
    2048 * (2 * C₀ + K) * Mbig ^ 6 * U ^ 2 + 8192 * (2 * C₀ + K) *
        ((16 * cj * c2 * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ))) ^ 2 * Mbig ^ 4 * U ^ 2 ≤
      2 ^ 22 * (1 + cj) ^ 2 * (1 + c2) ^ 2 * (C₀ + K + 1) *
        max (Mbig ^ 6 * U ^ 2) (T ^ (4 + 4 * ε + 2 * j) * U ^ 2 * Mbig ^ (6 - 2 * (j : ℝ))) := by
  set Mx : ℝ := max (Mbig ^ 6 * U ^ 2) (T ^ (4 + 4*ε + 2*(j:ℝ)) * U ^ 2 * Mbig ^ (6 - 2*(j:ℝ))) with hMxdef
  have hJ : (3:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hJpos : (0:ℝ) < (j:ℝ) := by linarith
  have hMb0 : (0:ℝ) ≤ Mbig := by linarith
  have hU2 : (0:ℝ) ≤ U^2 := sq_nonneg U
  have hA0 : (0:ℝ) ≤ 2*C₀+K := by linarith
  have hB0 : (0:ℝ) ≤ C₀+K+1 := by linarith
  have hA2B : 2*C₀+K ≤ 2*(C₀+K+1) := by linarith
  have hG1 : (1:ℝ) ≤ (1+cj)^2 * (1+c2)^2 := by
    have h1 : (1:ℝ) ≤ (1+cj)^2 := by nlinarith [hcj]
    have h2 : (1:ℝ) ≤ (1+c2)^2 := by nlinarith [hc2]
    nlinarith [h1, h2]
  have hG0 : (0:ℝ) ≤ (1+cj)^2 * (1+c2)^2 := by linarith
  have hb : (0:ℝ) ≤ cj*c2 := mul_nonneg hcj hc2
  have hexp_le : 2/(j:ℝ) ≤ 1 := by rw [div_le_one hJpos]; linarith
  have h16 : (16:ℝ)^(2/(j:ℝ)) ≤ 16 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (16:ℝ)) (by norm_num) hexp_le
    rw [Real.rpow_one] at h
    exact h
  have hcdup : (cj*c2)^(2/(j:ℝ)) ≤ (1+cj)^2 * (1+c2)^2 := by
    have h1 : (cj*c2)^(2/(j:ℝ)) ≤ ((1+cj)*(1+c2))^(2/(j:ℝ)) :=
      Real.rpow_le_rpow hb (by nlinarith) (div_nonneg (by norm_num) hJpos.le)
    rw [Real.mul_rpow (by linarith : (0:ℝ) ≤ 1+cj) (by linarith : (0:ℝ) ≤ 1+c2)] at h1
    have h2 : (1+cj)^(2/(j:ℝ)) ≤ 1+cj :=
      Real.rpow_le_self_of_one_le (by linarith : (1:ℝ) ≤ 1+cj) hexp_le
    have h3 : (1+c2)^(2/(j:ℝ)) ≤ 1+c2 :=
      Real.rpow_le_self_of_one_le (by linarith : (1:ℝ) ≤ 1+c2) hexp_le
    have h4 : (1+cj)^(2/(j:ℝ)) * (1+c2)^(2/(j:ℝ)) ≤ (1+cj)*(1+c2) :=
      mul_le_mul h2 h3 (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1+c2) _)
        (by linarith : (0:ℝ) ≤ 1+cj)
    have h5 : (1+cj)*(1+c2) ≤ (1+cj)^2 * (1+c2)^2 := by nlinarith [hcj, hc2]
    linarith [h1, h4, h5]
  have hK0G : 16^(2/(j:ℝ)) * (cj*c2)^(2/(j:ℝ)) ≤ 16 * ((1+cj)^2 * (1+c2)^2) :=
    mul_le_mul h16 hcdup (Real.rpow_nonneg hb _) (by norm_num)
  have hK00 : (0:ℝ) ≤ 16^(2/(j:ℝ)) * (cj*c2)^(2/(j:ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hb _)
  have hconst : 2048*(2*C₀+K) + 8192*(2*C₀+K)*(16^(2/(j:ℝ)) * (cj*c2)^(2/(j:ℝ)))
      ≤ 2^22 * ((1+cj)^2 * (1+c2)^2) * (C₀+K+1) := by
    nlinarith [hA2B, hG1, hA0, hK0G, hK00, hG0, hB0]
  have hkey : ((16 * cj * c2 * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ))) ^ 2 * Mbig^4
      ≤ (16^(2/(j:ℝ)) * (cj*c2)^(2/(j:ℝ))) *
        max (Mbig^6) (T ^ (4 + 4*ε + 2*(j:ℝ)) * Mbig ^ (6 - 2*(j:ℝ))) := by
    have h := key_bound (T:=T) (Mbig:=Mbig) (cj:=cj) (c2:=c2) (J:=(j:ℝ)) (ε:=ε)
      hε hJ hT hMb hcj hc2
    rw [Real.rpow_ofNat Mbig 4, Real.rpow_ofNat Mbig 6] at h
    exact h
  have hMx : Mx = max (Mbig^6) (T ^ (4 + 4*ε + 2*(j:ℝ)) * Mbig ^ (6 - 2*(j:ℝ))) * U^2 := by
    rw [hMxdef,
        max_mul_of_nonneg (Mbig^6) (T ^ (4 + 4*ε + 2*(j:ℝ)) * Mbig ^ (6 - 2*(j:ℝ))) (sq_nonneg U)]
    congr 1
    ring
  have hMx0 : (0:ℝ) ≤ Mx := by
    rw [hMxdef]
    exact le_trans (mul_nonneg (pow_nonneg hMb0 6) hU2) (le_max_left _ _)
  have step1 : 2048 * (2*C₀+K) * Mbig ^ 6 * U ^ 2 ≤ 2048*(2*C₀+K)*Mx := by
    have h := mul_le_mul_of_nonneg_left
      (le_max_left (Mbig^6 * U^2) (T^(4+4*ε+2*(j:ℝ))*U^2*Mbig^(6-2*(j:ℝ))))
      (by linarith : (0:ℝ) ≤ 2048*(2*C₀+K))
    rw [← hMxdef] at h
    nlinarith [h]
  have step2 : 8192 * (2*C₀+K) * ((16*cj*c2*T^((j:ℝ)+2+2*ε))^(1/(j:ℝ)))^2 * Mbig^4 * U^2
      ≤ 8192*(2*C₀+K)*(16^(2/(j:ℝ))*(cj*c2)^(2/(j:ℝ)))*Mx := by
    have h1 : ((16*cj*c2*T^((j:ℝ)+2+2*ε))^(1/(j:ℝ)))^2 * Mbig^4 * U^2
        ≤ (16^(2/(j:ℝ))*(cj*c2)^(2/(j:ℝ))) * Mx := by
      rw [hMx]
      have h2 := mul_le_mul_of_nonneg_right hkey hU2
      nlinarith [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 8192*(2*C₀+K))
    nlinarith [h3]
  have hsum : 2048 * (2*C₀+K) * Mbig^6 * U^2 + 8192*(2*C₀+K)*((16*cj*c2*T^((j:ℝ)+2+2*ε))^(1/(j:ℝ)))^2*Mbig^4*U^2
      ≤ (2048*(2*C₀+K) + 8192*(2*C₀+K)*(16^(2/(j:ℝ))*(cj*c2)^(2/(j:ℝ)))) * Mx := by
    nlinarith [step1, step2]
  have hfin : (2048*(2*C₀+K) + 8192*(2*C₀+K)*(16^(2/(j:ℝ))*(cj*c2)^(2/(j:ℝ)))) * Mx
      ≤ 2 ^ 22 * (1 + cj) ^ 2 * (1 + c2) ^ 2 * (C₀ + K + 1) * Mx := by
    have h := mul_le_mul_of_nonneg_right hconst hMx0
    nlinarith [h]
  linarith [hsum, hfin]

end Work.GM.Affine.crude_b

