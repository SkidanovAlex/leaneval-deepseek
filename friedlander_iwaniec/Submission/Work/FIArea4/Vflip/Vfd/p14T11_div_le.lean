import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup

namespace Work.FIArea4.Vflip.Vfd

/-- The bracket `p14T11`, evaluated at `R' = ⌈R/ρ⌉ = (R+ρ-1)/ρ` in place of `R`, is bounded by
the same bracket with `R` restored, at the price of the factors `4ρ⁻¹` (on the `D^{-1/2}RS` and
`R S^{3/4}` parts) and `4ρ^{-1/2}` (on the `D√(RS)` and `S R^{3/4}` parts).

The point is the ratio `q = R'/R ≤ 2/(ρ+1) ≤ 2/ρ ≤ 1`: writing `p14T11` as `pT1+…+pT4` and
scaling every occurrence of `R'` to `R·q`, the four terms acquire the exponents
`1`, `1/2+ε`, `1+ε`, `3/4+ε` on `q ≤ 1`, and since every exponent is `≥ 1/2` (for the `1/2`-terms)
or `≥ 1` (for the `1`-terms), each is bounded by `4ρ^{-1/2}` resp. `4ρ⁻¹`. -/
theorem p14T11_div_le (D R S ρ : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hρ : 1 ≤ ρ) (hρR : ρ ≤ R) :
    Work.FIArea4.p14T11 D ((R+ρ-1)/ρ) S ε
      ≤ 4 * ((ρ:ℝ))⁻¹ * (Work.FIArea4.Vflip.Vfd.pT1 D R S + Work.FIArea4.Vflip.Vfd.pT3 D R S ε)
        + 4 * ((ρ:ℝ)) ^ (-(1:ℝ)/2)
            * (Work.FIArea4.Vflip.Vfd.pT2 D R S ε + Work.FIArea4.Vflip.Vfd.pT4 D R S ε) := by
  set rp : ℕ := (R+ρ-1)/ρ with hrp
  set q : ℝ := (rp:ℝ)/(R:ℝ) with hq
  have hρrpos : (0:ℝ) < ρ := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hρ)
  have hρrnn : (0:ℝ) ≤ ρ := hρrpos.le
  have hRrpos : (0:ℝ) < R := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hRrnn : (0:ℝ) ≤ R := hRrpos.le
  have hSrnn : (0:ℝ) ≤ S := by positivity
  have hρinv_nn : 0 ≤ (ρ:ℝ)⁻¹ := inv_nonneg.mpr hρrnn
  have hrp1 : 1 ≤ rp := by
    rw [hrp]; apply Nat.le_div_iff_mul_le hρ |>.mpr; omega
  have hrprpos : (0:ℝ) < rp := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hrp1)
  have hrprnn : (0:ℝ) ≤ rp := hrprpos.le
  -- `⌈R/ρ⌉ ≤ R`
  have hrp_le_R : (rp:ℝ) ≤ R := by
    rw [hrp]
    have step1 : (((R+ρ-1)/ρ : ℕ) : ℝ) ≤ ((R+ρ-1 : ℕ) : ℝ) / (ρ:ℝ) := Nat.cast_div_le
    have hc : ((R+ρ-1 : ℕ) : ℝ) = (R:ℝ)+(ρ:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ R + ρ)]; push_cast; ring
    rw [hc] at step1
    have step2 : ((R:ℝ)+(ρ:ℝ)-1) / (ρ:ℝ) ≤ (R:ℝ) := by
      rw [div_le_iff₀ hρrpos]
      have hR1 : (1:ℝ) ≤ R := by exact_mod_cast hR
      have hρ1 : (1:ℝ) ≤ ρ := by exact_mod_cast hρ
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (R:ℝ)-1 by linarith) (show (0:ℝ) ≤ (ρ:ℝ)-1 by linarith)]
    linarith
  -- `⌈R/ρ⌉ ≤ 2R/ρ`
  have hrp_le2 : (rp:ℝ) ≤ 2*(R:ℝ)/(ρ:ℝ) := by
    rw [hrp]
    have hρR' : (ρ:ℝ) ≤ R := by exact_mod_cast hρR
    have step1 : (((R+ρ-1)/ρ : ℕ) : ℝ) ≤ ((R+ρ-1 : ℕ) : ℝ) / (ρ:ℝ) := Nat.cast_div_le
    have hc : ((R+ρ-1 : ℕ) : ℝ) = (R:ℝ)+(ρ:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ R + ρ)]; push_cast; ring
    rw [hc] at step1
    have step2 : ((R:ℝ)+(ρ:ℝ)-1) / (ρ:ℝ) ≤ 2*(R:ℝ)/(ρ:ℝ) := by
      rw [div_le_div_iff_of_pos_right hρrpos]; linarith
    linarith
  have hqpos : 0 < q := by rw [hq]; exact div_pos hrprpos hRrpos
  have hqnn : 0 ≤ q := hqpos.le
  have hqle1 : q ≤ 1 := by rw [hq, div_le_one hRrpos]; exact hrp_le_R
  have hqle2 : q ≤ 2*(ρ:ℝ)⁻¹ := by
    rw [hq]
    have : (rp:ℝ)/(R:ℝ) ≤ (2*(R:ℝ)/(ρ:ℝ))/(R:ℝ) := div_le_div_of_nonneg_right hrp_le2 hRrnn
    have heq : (2*(R:ℝ)/(ρ:ℝ))/(R:ℝ) = 2*(ρ:ℝ)⁻¹ := by field_simp
    linarith
  -- `(2ρ⁻¹)^{1/2} ≤ 4ρ^{-1/2}`
  have h2half : (2*(ρ:ℝ)⁻¹)^((1:ℝ)/2) ≤ 4*(ρ:ℝ)^(-(1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow (2*(ρ:ℝ)⁻¹)]
    have hRHS : 4*(ρ:ℝ)^(-(1:ℝ)/2) = 4/Real.sqrt ρ := by
      rw [show (-(1:ℝ)/2 : ℝ) = -((1:ℝ)/2) from by ring]
      rw [Real.rpow_neg hρrnn (1/2), Real.sqrt_eq_rpow]; ring
    rw [hRHS]
    rw [show (2*(ρ:ℝ)⁻¹) = 2/ρ by rw [div_eq_mul_inv]]
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2)]
    rw [div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hρrpos)]
    have h4 : Real.sqrt (2:ℝ) ≤ 4 := by
      have h := Real.sqrt_le_sqrt (show (2:ℝ) ≤ 16 by norm_num)
      rwa [show Real.sqrt (16:ℝ) = 4 by norm_num] at h
    linarith
  have hqhalf : q^((1:ℝ)/2) ≤ 4*(ρ:ℝ)^(-(1:ℝ)/2) :=
    (Real.rpow_le_rpow hqnn hqle2 (by norm_num)).trans h2half
  have hrprEq : (rp:ℝ) = (R:ℝ) * q := by rw [hq]; field_simp
  have hsq : (rp:ℝ) * (S:ℝ) = ((R:ℝ)*(S:ℝ)) * q := by rw [hrprEq]; ring
  -- the four terms rescale by `q^e`
  have hA : pT1 D rp S = pT1 D R S * q := by
    unfold pT1; rw [hrprEq]; ring
  have hB : pT2 D rp S ε = pT2 D R S ε * q ^ ((1:ℝ)/2 + ε) := by
    unfold pT2
    rw [hsq, Real.sqrt_mul (mul_nonneg hRrnn hSrnn), Real.mul_rpow (mul_nonneg hRrnn hSrnn) hqnn]
    rw [Real.sqrt_eq_rpow q, Real.rpow_add hqpos]; ring
  have hC : pT3 D rp S ε = pT3 D R S ε * q ^ (1 + ε) := by
    unfold pT3
    rw [hsq, Real.mul_rpow (mul_nonneg hRrnn hSrnn) hqnn, hrprEq]
    rw [Real.rpow_add hqpos, Real.rpow_one]; ring
  have hD : pT4 D rp S ε = pT4 D R S ε * q ^ ((3:ℝ)/4 + ε) := by
    unfold pT4
    rw [hsq, Real.mul_rpow (mul_nonneg hRrnn hSrnn) hqnn, hrprEq]
    rw [Real.mul_rpow hRrnn hqnn, Real.rpow_add hqpos]; ring
  have bA : pT1 D R S * q ≤ 4 * (ρ:ℝ)⁻¹ * pT1 D R S := by
    have hp1 : 0 ≤ pT1 D R S := pT1_nonneg D R S
    calc pT1 D R S * q ≤ pT1 D R S * (2*(ρ:ℝ)⁻¹) := mul_le_mul_of_nonneg_left hqle2 hp1
      _ = 2*(ρ:ℝ)⁻¹ * pT1 D R S := by ring
      _ ≤ 4*(ρ:ℝ)⁻¹ * pT1 D R S := by
          apply mul_le_mul_of_nonneg_right _ hp1; nlinarith [hρinv_nn]
  have bB : pT2 D R S ε * q ^ ((1:ℝ)/2+ε) ≤ 4*(ρ:ℝ)^(-(1:ℝ)/2) * pT2 D R S ε := by
    have hp2 : 0 ≤ pT2 D R S ε := pT2_nonneg D R S ε
    have hpow : q^((1:ℝ)/2+ε) ≤ 4*(ρ:ℝ)^(-(1:ℝ)/2) :=
      (Real.rpow_le_rpow_of_exponent_ge hqpos hqle1 (by linarith)).trans hqhalf
    calc pT2 D R S ε * q^((1:ℝ)/2+ε) ≤ pT2 D R S ε * (4*(ρ:ℝ)^(-(1:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left hpow hp2
      _ = 4*(ρ:ℝ)^(-(1:ℝ)/2) * pT2 D R S ε := by ring
  have bC : pT3 D R S ε * q ^ (1+ε) ≤ 4*(ρ:ℝ)⁻¹ * pT3 D R S ε := by
    have hp3 : 0 ≤ pT3 D R S ε := pT3_nonneg D R S ε
    have hpow : q^(1+ε) ≤ 4*(ρ:ℝ)⁻¹ := by
      have h1 : q^(1+ε) ≤ q^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_ge hqpos hqle1 (by linarith)
      rw [Real.rpow_one] at h1
      linarith [hqle2, hρinv_nn]
    calc pT3 D R S ε * q^(1+ε) ≤ pT3 D R S ε * (4*(ρ:ℝ)⁻¹) := mul_le_mul_of_nonneg_left hpow hp3
      _ = 4*(ρ:ℝ)⁻¹ * pT3 D R S ε := by ring
  have bD : pT4 D R S ε * q ^ ((3:ℝ)/4+ε) ≤ 4*(ρ:ℝ)^(-(1:ℝ)/2) * pT4 D R S ε := by
    have hp4 : 0 ≤ pT4 D R S ε := pT4_nonneg D R S ε
    have hpow : q^((3:ℝ)/4+ε) ≤ 4*(ρ:ℝ)^(-(1:ℝ)/2) :=
      (Real.rpow_le_rpow_of_exponent_ge hqpos hqle1 (by linarith)).trans hqhalf
    calc pT4 D R S ε * q^((3:ℝ)/4+ε) ≤ pT4 D R S ε * (4*(ρ:ℝ)^(-(1:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left hpow hp4
      _ = 4*(ρ:ℝ)^(-(1:ℝ)/2) * pT4 D R S ε := by ring
  rw [p14T11_eq_sum D rp S ε, hA, hB, hC, hD]
  have hexpand : 4*(ρ:ℝ)⁻¹*(pT1 D R S + pT3 D R S ε) + 4*(ρ:ℝ)^(-(1:ℝ)/2)*(pT2 D R S ε + pT4 D R S ε)
      = 4*(ρ:ℝ)⁻¹*pT1 D R S + 4*(ρ:ℝ)^(-(1:ℝ)/2)*pT2 D R S ε
        + 4*(ρ:ℝ)⁻¹*pT3 D R S ε + 4*(ρ:ℝ)^(-(1:ℝ)/2)*pT4 D R S ε := by ring
  linarith [bA, bB, bC, bD, hexpand]

end Work.FIArea4.Vflip.Vfd
