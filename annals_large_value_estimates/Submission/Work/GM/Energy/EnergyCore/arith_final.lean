import Mathlib

namespace Work.GM.Energy.EnergyCore

/-- The abstract arithmetic core of `arith_final`: a pure inequality between nonnegative
quantities, with the three "analytic" inputs supplied as hypotheses
(`hsp`, `hT1q`, `hRr`). -/
lemma arith_core (C1 Chb Cloc K E Wc MM kk q T1 S f4 R Rt e34 coeff : ℝ)
    (hC1 : 0 ≤ C1) (hChb : 0 ≤ Chb) (hCloc : 0 ≤ Cloc) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hWc : 0 ≤ Wc) (hMM : 0 ≤ MM) (hf4 : 0 ≤ f4) (hT1 : 0 ≤ T1) (hq : 0 ≤ q)
    (_hS : 0 ≤ S) (hR : 0 ≤ R) (hRt : 0 ≤ Rt) (he34 : 0 ≤ e34) (_hcoeff : 0 ≤ coeff)
    (hsp : S * T1 ≤ f4 * q) (hT1q : T1 ≤ q) (hRr : R ≤ 2 * Rt)
    (hc1 : 32 * C1 * Chb * f4 ≤ coeff) (hc2 : 8 * C1 ≤ coeff) :
    C1 * T1 * (16 * K ^ 2 * Cloc ^ 2 * Chb * S *
          (Wc ^ 4 * MM + E * MM ^ 2 + R * e34 * Wc * MM)
        + 8 * (Cloc / kk * (MM + 1)) ^ 2 * E * Wc ^ 2)
      ≤ coeff * (Cloc + 1) ^ 2 * q * (K + 1) ^ 2 *
          (Wc ^ 4 * MM + E * MM ^ 2 + Rt * e34 * Wc * MM)
        + coeff * (Cloc + 1) ^ 2 * q * ((MM + 1) / kk) ^ 2 * E * Wc ^ 2 := by
  have hX : (0:ℝ) ≤ Wc^4*MM := by positivity
  have hY : (0:ℝ) ≤ E*MM^2 := by positivity
  have hZtnn : (0:ℝ) ≤ Rt*e34*Wc*MM := by positivity
  have hBZnn : (0:ℝ) ≤ Wc^4*MM + E*MM^2 + R*e34*Wc*MM := by positivity
  have hf4q : (0:ℝ) ≤ f4*q := mul_nonneg hf4 hq
  have hDtnn : (0:ℝ) ≤ ((MM+1)/kk)^2 := by positivity
  have hZle : R*e34*Wc*MM ≤ 2*(Rt*e34*Wc*MM) := by
    have he : (0:ℝ) ≤ e34*Wc*MM := by positivity
    calc R*e34*Wc*MM = R*(e34*Wc*MM) := by ring
      _ ≤ (2*Rt)*(e34*Wc*MM) := mul_le_mul_of_nonneg_right hRr he
      _ = 2*(Rt*e34*Wc*MM) := by ring
  have hBZle : Wc^4*MM + E*MM^2 + R*e34*Wc*MM ≤ 2*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM) := by
    linarith [hX, hY, hZle]
  have hSTBZ : S*T1*(Wc^4*MM + E*MM^2 + R*e34*Wc*MM)
      ≤ f4*q*(2*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)) := by
    calc S*T1*(Wc^4*MM + E*MM^2 + R*e34*Wc*MM)
        ≤ f4*q*(Wc^4*MM + E*MM^2 + R*e34*Wc*MM) := mul_le_mul_of_nonneg_right hsp hBZnn
      _ ≤ f4*q*(2*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)) := mul_le_mul_of_nonneg_left hBZle hf4q
  have h16 : (0:ℝ) ≤ 16*C1*K^2*Cloc^2*Chb := by positivity
  have hKsq : K^2 ≤ (K+1)^2 := by
    have h : (K+1)^2 = K^2 + (2*K+1) := by ring
    rw [h]; linarith
  have hClocsq : Cloc^2 ≤ (Cloc+1)^2 := by
    have h : (Cloc+1)^2 = Cloc^2 + (2*Cloc+1) := by ring
    rw [h]; linarith
  have hKC : K^2*Cloc^2 ≤ (K+1)^2*(Cloc+1)^2 :=
    mul_le_mul hKsq hClocsq (by positivity) (by positivity)
  have s2 : 32*C1*K^2*Cloc^2*Chb*f4*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)
      ≤ 32*C1*Chb*f4*(K+1)^2*(Cloc+1)^2*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM) := by
    rw [show 32*C1*K^2*Cloc^2*Chb*f4*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)
          = (32*C1*Chb*f4*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM))*(K^2*Cloc^2) from by ring,
        show 32*C1*Chb*f4*(K+1)^2*(Cloc+1)^2*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)
          = (32*C1*Chb*f4*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM))*((K+1)^2*(Cloc+1)^2) from by ring]
    exact mul_le_mul_of_nonneg_left hKC (by positivity)
  have s3 : 32*C1*Chb*f4*(K+1)^2*(Cloc+1)^2*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)
      ≤ coeff*(Cloc+1)^2*q*(K+1)^2*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM) := by
    rw [show 32*C1*Chb*f4*(K+1)^2*(Cloc+1)^2*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)
          = (32*C1*Chb*f4)*((K+1)^2*(Cloc+1)^2*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)) from by ring,
        show coeff*(Cloc+1)^2*q*(K+1)^2*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)
          = coeff*((K+1)^2*(Cloc+1)^2*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM)) from by ring]
    exact mul_le_mul_of_nonneg_right hc1 (by positivity)
  have hA1 : C1*T1*(16*K^2*Cloc^2*Chb*S*(Wc^4*MM + E*MM^2 + R*e34*Wc*MM))
      ≤ coeff*(Cloc+1)^2*q*(K+1)^2*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM) := by
    calc C1*T1*(16*K^2*Cloc^2*Chb*S*(Wc^4*MM + E*MM^2 + R*e34*Wc*MM))
        = 16*C1*K^2*Cloc^2*Chb*(S*T1*(Wc^4*MM + E*MM^2 + R*e34*Wc*MM)) := by ring
      _ ≤ 16*C1*K^2*Cloc^2*Chb*(f4*q*(2*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM))) :=
            mul_le_mul_of_nonneg_left hSTBZ h16
      _ = 32*C1*K^2*Cloc^2*Chb*f4*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM) := by ring
      _ ≤ 32*C1*Chb*f4*(K+1)^2*(Cloc+1)^2*q*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM) := s2
      _ ≤ coeff*(Cloc+1)^2*q*(K+1)^2*(Wc^4*MM + E*MM^2 + Rt*e34*Wc*MM) := s3
  have hDle : (Cloc/kk*(MM+1))^2 ≤ (Cloc+1)^2*((MM+1)/kk)^2 := by
    have e : (Cloc/kk*(MM+1))^2 = Cloc^2*((MM+1)/kk)^2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hClocsq hDtnn
  have hA2 : C1*T1*(8*(Cloc/kk*(MM+1))^2*E*Wc^2)
      ≤ coeff*(Cloc+1)^2*q*((MM+1)/kk)^2*E*Wc^2 := by
    calc C1*T1*(8*(Cloc/kk*(MM+1))^2*E*Wc^2)
        = (C1*T1*8*E*Wc^2)*((Cloc/kk*(MM+1))^2) := by ring
      _ ≤ (C1*T1*8*E*Wc^2)*((Cloc+1)^2*((MM+1)/kk)^2) :=
            mul_le_mul_of_nonneg_left hDle (by positivity)
      _ = 8*C1*T1*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2 := by ring
      _ ≤ 8*C1*q*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2 := by
            rw [show 8*C1*T1*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2
                  = T1*(8*C1*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2) from by ring,
                show 8*C1*q*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2
                  = q*(8*C1*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2) from by ring]
            exact mul_le_mul_of_nonneg_right hT1q (by positivity)
      _ ≤ coeff*(Cloc+1)^2*q*((MM+1)/kk)^2*E*Wc^2 := by
            rw [show 8*C1*q*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2
                  = (8*C1)*(q*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2) from by ring,
                show coeff*(Cloc+1)^2*q*((MM+1)/kk)^2*E*Wc^2
                  = coeff*(q*(Cloc+1)^2*((MM+1)/kk)^2*E*Wc^2) from by ring]
            exact mul_le_mul_of_nonneg_right hc2 (by positivity)
  have hsplit : C1*T1*(16*K^2*Cloc^2*Chb*S*(Wc^4*MM + E*MM^2 + R*e34*Wc*MM)
        + 8*(Cloc/kk*(MM+1))^2*E*Wc^2)
      = C1*T1*(16*K^2*Cloc^2*Chb*S*(Wc^4*MM + E*MM^2 + R*e34*Wc*MM))
        + C1*T1*(8*(Cloc/kk*(MM+1))^2*E*Wc^2) := by ring
  rw [hsplit]
  exact add_le_add hA1 hA2

theorem arith_final (ε : ℝ) (hε : 0 < ε) (C1 Chb T K Cloc E Wc MM m : ℝ)
    (hT : 1 ≤ T) (hK : 0 < K) (hCloc : 0 ≤ Cloc)
    (hC1 : 0 ≤ C1) (hChb : 0 ≤ Chb) (hE : 0 ≤ E) (hWc : 0 ≤ Wc) (hMM : 0 ≤ MM) :
    C1 * T ^ (ε / 2) *
        (16 * K ^ 2 * Cloc ^ 2 * Chb * (2 * (T + 1)) ^ (ε / 2) *
              (Wc ^ 4 * MM + E * MM ^ 2
                + (2 * (T + 1)) ^ ((1 : ℝ) / 2) * E ^ ((3 : ℝ) / 4) * Wc * MM)
          + 8 * (Cloc / K ^ m * (MM + 1)) ^ 2 * E * Wc ^ 2)
      ≤ (32 * C1 * Chb * 4 ^ (ε / 2) + 8 * C1 + 1) * (Cloc + 1) ^ 2 * T ^ ε * (K + 1) ^ 2 *
            (Wc ^ 4 * MM + E * MM ^ 2 + T ^ ((1 : ℝ) / 2) * E ^ ((3 : ℝ) / 4) * Wc * MM)
        + (32 * C1 * Chb * 4 ^ (ε / 2) + 8 * C1 + 1) * (Cloc + 1) ^ 2 * T ^ ε *
            ((MM + 1) / K ^ m) ^ 2 * E * Wc ^ 2 := by
  have hTnn : (0:ℝ) ≤ T := by linarith
  have hKnn : (0:ℝ) ≤ K := le_of_lt hK
  have hf4 : (0:ℝ) ≤ (4:ℝ) ^ (ε / 2) := Real.rpow_nonneg (by norm_num) _
  have hT1nn : (0:ℝ) ≤ T ^ (ε / 2) := Real.rpow_nonneg hTnn _
  have hq : (0:ℝ) ≤ T ^ ε := Real.rpow_nonneg hTnn _
  have hSnn : (0:ℝ) ≤ (2 * (T + 1)) ^ (ε / 2) := Real.rpow_nonneg (by linarith) _
  have hRnn : (0:ℝ) ≤ (2 * (T + 1)) ^ ((1:ℝ)/2) := Real.rpow_nonneg (by linarith) _
  have hRtnn : (0:ℝ) ≤ T ^ ((1:ℝ)/2) := Real.rpow_nonneg hTnn _
  have he34 : (0:ℝ) ≤ E ^ ((3:ℝ)/4) := Real.rpow_nonneg hE _
  have hε2 : (0:ℝ) ≤ ε / 2 := by linarith
  have hsp : (2 * (T + 1)) ^ (ε / 2) * T ^ (ε / 2) ≤ (4:ℝ) ^ (ε / 2) * T ^ ε := by
    have h1 : (0:ℝ) ≤ 2 * (T + 1) := by linarith
    have h2 : 2 * (T + 1) * T ≤ 4 * T ^ 2 := by nlinarith [hT]
    have h3 : (2 * (T + 1) * T) ^ (ε / 2) ≤ (4 * T ^ 2) ^ (ε / 2) :=
      Real.rpow_le_rpow (by linarith) h2 hε2
    have h4 : (2 * (T + 1)) ^ (ε / 2) * T ^ (ε / 2) = (2 * (T + 1) * T) ^ (ε / 2) := by
      rw [Real.mul_rpow h1 hTnn]
    have h5 : (4 * T ^ 2) ^ (ε / 2) = (4:ℝ) ^ (ε / 2) * T ^ ε := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ T ^ 2)]
      have : (T ^ 2) ^ (ε / 2) = T ^ ε := by
        rw [← Real.rpow_two, ← Real.rpow_mul hTnn]
        ring_nf
      rw [this]
    linarith only [h3, h4, h5]
  have hT1q : T ^ (ε / 2) ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hRr : (2 * (T + 1)) ^ ((1:ℝ)/2) ≤ 2 * T ^ ((1:ℝ)/2) := by
    have h1 : (0:ℝ) ≤ 2 * (T + 1) := by linarith
    have h2 : 2 * (T + 1) ≤ 4 * T := by linarith
    have h3 : (2 * (T + 1)) ^ ((1:ℝ)/2) ≤ (4 * T) ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow h1 h2 (by norm_num)
    have h4 : (4 * T) ^ ((1:ℝ)/2) = 2 * T ^ ((1:ℝ)/2) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hTnn]
      norm_num
    linarith only [h3, h4]
  have hc3 : (0:ℝ) ≤ 32 * C1 * Chb * (4:ℝ) ^ (ε / 2) := by positivity
  have hcoeffnn : (0:ℝ) ≤ 32 * C1 * Chb * (4:ℝ) ^ (ε / 2) + 8 * C1 + 1 := by linarith
  have hc1 : 32 * C1 * Chb * (4:ℝ) ^ (ε / 2) ≤ 32 * C1 * Chb * (4:ℝ) ^ (ε / 2) + 8 * C1 + 1 := by
    linarith
  have hc2 : 8 * C1 ≤ 32 * C1 * Chb * (4:ℝ) ^ (ε / 2) + 8 * C1 + 1 := by linarith
  exact arith_core C1 Chb Cloc K E Wc MM (K ^ m) (T ^ ε) (T ^ (ε / 2))
    ((2 * (T + 1)) ^ (ε / 2)) ((4:ℝ) ^ (ε / 2)) ((2 * (T + 1)) ^ ((1:ℝ)/2))
    (T ^ ((1:ℝ)/2)) (E ^ ((3:ℝ)/4)) (32 * C1 * Chb * (4:ℝ) ^ (ε / 2) + 8 * C1 + 1)
    hC1 hChb hCloc hKnn hE hWc hMM hf4 hT1nn hq hSnn hRnn hRtnn he34 hcoeffnn
    hsp hT1q hRr hc1 hc2

end Work.GM.Energy.EnergyCore
