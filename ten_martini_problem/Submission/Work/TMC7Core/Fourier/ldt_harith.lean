import Mathlib

namespace Work.TMC7Core.Fourier

/-- The logarithmic factor bound used in `ldt_harith`:
the `exp` on the right of `hKle9` dominates `log (1 + K/q)`. -/
theorem ldt_harith_log (κ q K : ℝ) (hκ0 : 0 < κ) (hq : 1 ≤ q) (hK1 : 1 ≤ K)
    (hKle9 : K ≤ 9 * Real.exp ((1 / 1000) * κ * q) / κ ^ 2) :
    Real.log (1 + K / q) ≤ (1 / 1000) * κ * q + 9 / (κ ^ 2 * q) := by
  have hqpos : 0 < q := by linarith
  have hKpos : 0 < K := by linarith
  have hKqpos : 0 < 1 + K / q := by
    have : 0 < K / q := div_pos hKpos hqpos
    linarith
  rw [Real.log_le_iff_le_exp hKqpos]
  have heq : Real.exp ((1/1000)*κ*q) * (9/(κ^2*q)) * q = 9*Real.exp ((1/1000)*κ*q)/κ^2 := by
    field_simp
  have hKq_le : K/q ≤ Real.exp ((1/1000)*κ*q) * (9/(κ^2*q)) := by
    rw [div_le_iff₀ hqpos]
    rw [heq]
    exact hKle9
  have hexp1 : (1:ℝ) ≤ Real.exp ((1/1000)*κ*q) := Real.one_le_exp (by positivity)
  have hnonneg : 0 ≤ 9/(κ^2*q) := by positivity
  have hstep : 1 + K/q ≤ Real.exp ((1/1000)*κ*q) * (1 + 9/(κ^2*q)) := by
    have hh : (1:ℝ) * (9/(κ^2*q)) ≤ Real.exp ((1/1000)*κ*q) * (9/(κ^2*q)) :=
      mul_le_mul_of_nonneg_right hexp1 hnonneg
    nlinarith [hKq_le, hh]
  rw [Real.exp_add]
  calc 1 + K/q ≤ Real.exp ((1/1000)*κ*q) * (1 + 9/(κ^2*q)) := hstep
    _ ≤ Real.exp ((1/1000)*κ*q) * Real.exp (9/(κ^2*q)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
        have := Real.add_one_le_exp (9/(κ^2*q))
        linarith

theorem ldt_harith (κ q K s Cv : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hq : 1 ≤ q)
    (hs100 : 100 ≤ s) (hsk2 : 100 ^ 2 ≤ s ^ 2 * κ) (hK1 : 1 ≤ K)
    (hKle9 : K ≤ 9 * Real.exp ((1 / 1000) * κ * q) / κ ^ 2)
    (hqinv : 1 / q ≤ κ ^ 2 / Cv) (hCv1 : 1 ≤ Cv) (hCv864 : 864 ≤ Cv) (hCv9600 : 9600 ≤ Cv) :
    50 / s ^ 2 + (1 + 50 / s) * (1 / q) * Real.log (1 + K / q) + 100 / q ≤ κ / 16 := by
  have hqpos : 0 < q := by linarith
  have hspos : 0 < s := by linarith
  -- First term: `50 / s^2 ≤ κ / 200`.
  have h1 : 50 / s ^ 2 ≤ κ / 200 := by
    have hs2pos : 0 < s ^ 2 := by positivity
    rw [div_le_div_iff₀ hs2pos (by norm_num : (0:ℝ) < 200)]
    nlinarith [hsk2]
  -- Consequence of `hqinv`: `9600 ≤ κ^2 q`.
  have h1q : 1 / q ≤ κ ^ 2 / 9600 := by
    calc 1 / q ≤ κ ^ 2 / Cv := hqinv
      _ ≤ κ ^ 2 / 9600 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hCv9600
  have h96 : (9600:ℝ) ≤ κ ^ 2 * q := by
    have := (div_le_div_iff₀ hqpos (by norm_num : (0:ℝ) < 9600)).mp h1q
    linarith
  have hkk : κ ^ 2 ≤ κ := by nlinarith [hκ0, hκ1]
  have h96kq : (9600:ℝ) ≤ κ * q := le_trans h96 (mul_le_mul_of_nonneg_right hkk (le_of_lt hqpos))
  -- Third term: `100 / q ≤ κ / 96`.
  have h2 : 100 / q ≤ κ / 96 := by
    rw [div_le_div_iff₀ hqpos (by norm_num : (0:ℝ) < 96)]
    nlinarith [h96kq]
  -- Second term: `(1 + 50/s) * (1/q) * log (1 + K/q) ≤ κ / 400`.
  have hlog := ldt_harith_log κ q K hκ0 hq hK1 hKle9
  have hLnn : 0 ≤ Real.log (1 + K / q) := by
    apply Real.log_nonneg
    have hKq : 0 < K / q := div_pos (by linarith) hqpos
    linarith
  have hs3 : (1 + 50/s) ≤ 3/2 := by
    have : (50:ℝ)/s ≤ 1/2 := by
      rw [div_le_div_iff₀ hspos (by norm_num : (0:ℝ)<2)]
      nlinarith [hs100]
    linarith
  have h3 : (1 + 50 / s) * (1 / q) * Real.log (1 + K / q) ≤ κ / 400 := by
    have hstep1 : (1 + 50 / s) * (1 / q) * Real.log (1 + K / q)
        ≤ (3 / 2) * ((1 / q) * Real.log (1 + K / q)) := by
      have hnonneg : 0 ≤ (1/q) * Real.log (1 + K / q) := mul_nonneg (by positivity) hLnn
      have h := mul_le_mul_of_nonneg_right hs3 hnonneg
      calc (1 + 50 / s) * (1 / q) * Real.log (1 + K / q)
          = (1 + 50 / s) * ((1 / q) * Real.log (1 + K / q)) := by ring
        _ ≤ (3/2) * ((1 / q) * Real.log (1 + K / q)) := h
    have hstep2 : (3 / 2) * ((1 / q) * Real.log (1 + K / q))
        ≤ (3 / 2) * ((1 / q) * ((1 / 1000) * κ * q + 9 / (κ ^ 2 * q))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left hlog (by positivity)
    have harith : (3 / 2) * ((1 / q) * ((1 / 1000) * κ * q + 9 / (κ ^ 2 * q))) ≤ κ / 400 := by
      have h3' : (3 / 2) * ((1 / q) * ((1 / 1000) * κ * q + 9 / (κ ^ 2 * q)))
          = 3*κ/2000 + 27/(2*κ^2*q^2) := by
        field_simp
        ring
      rw [h3']
      have hcube : (27000:ℝ) ≤ κ^3 * q^2 := by
        have hmul : (9600:ℝ) * 9600 ≤ (κ^2*q) * (κ*q) :=
          mul_le_mul h96 h96kq (by norm_num) (by positivity)
        nlinarith [hmul]
      have hb : 27/(2*κ^2*q^2) ≤ κ/1000 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*κ^2*q^2)]
        nlinarith [hcube]
      linarith
    linarith
  -- Assemble the three bounds.
  have htot : 50 / s ^ 2 + (1 + 50 / s) * (1 / q) * Real.log (1 + K / q) + 100 / q
      ≤ κ / 200 + κ / 400 + κ / 96 := by linarith
  have hconst : (1:ℝ)/200 + 1/400 + 1/96 ≤ (1:ℝ)/16 := by norm_num
  have hbudget : κ / 200 + κ / 400 + κ / 96 ≤ κ / 16 := by
    have hre : κ / 200 + κ / 400 + κ / 96 = κ * (1/200 + 1/400 + 1/96) := by ring
    rw [hre]
    calc κ * (1/200 + 1/400 + 1/96) ≤ κ * (1/16) :=
          mul_le_mul_of_nonneg_left hconst (le_of_lt hκ0)
      _ = κ / 16 := by ring
  linarith

end Work.TMC7Core.Fourier
