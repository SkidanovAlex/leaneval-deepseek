import Submission.Work.Deep.Sparse.Prelude
namespace Work.Deep.Sparse

/-- Numeric fact used to bound `((K-1)/K)^(2D) = (1 + 1/(K-1))^{-(2D)}` from below:
`(1 + 1/(K-1))^(2D) = exp ((2D)·log (1 + 1/(K-1))) ≤ exp (2D/(K-1))` and `2D/(K-1) < 2.05`
in the regime of `pt_key_arith`; since `exp 2.05 < 8` the reciprocal factor is at least `1/8`.
The bound `exp 2.05 < 8` is proved here from `exp 1 < 2.72` and `exp (1/20) ≤ 1/(1-1/20)`. -/
lemma exp_205_lt_eight : Real.exp 2.05 < 8 := by
  have h41 : (2.05 : ℝ) = 41/20 := by norm_num
  rw [h41]
  have hsplit : Real.exp (41/20 : ℝ) = Real.exp (2:ℝ) * Real.exp (1/20 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have he2 : Real.exp (2:ℝ) < 7.4 := by
    have h : Real.exp (2:ℝ) = Real.exp 1 ^ 2 := by
      simpa using (Real.exp_nat_mul (1:ℝ) 2)
    rw [h]
    nlinarith only [Real.exp_one_lt_d9, Real.exp_pos 1]
  have he20 : Real.exp (1/20:ℝ) ≤ 20/19 := by
    have h := Real.one_sub_le_exp_neg (1/20 : ℝ)
    rw [show (1:ℝ) - 1/20 = 19/20 by norm_num, Real.exp_neg] at h
    have h2 := (le_inv_comm₀ (show (0:ℝ) < 19/20 by norm_num) (Real.exp_pos (1/20))).mp h
    simpa [inv_div] using h2
  have := mul_lt_mul he2 he20 (Real.exp_pos (1/20)) (by norm_num : (0:ℝ) ≤ 7.4)
  have hnum : 7.4 * (20/19 : ℝ) < 8 := by norm_num
  linarith

/-- The quantitative core of the naive colouring procedure: at a vertex of degree `d` (with
`0 ≤ d ≤ Δ` and `d + 1 - k > 0`) the expected number of repeated colours inside the
neighbourhood, namely `(1/4) * |non-adjacent pairs| * (1/k) * ((k-1)/k)^(2D) * (1 - D/(3k))`,
dominates the requirement `d + 1 - k` of the extension step.  The only information used about
the graph is the sparsity bound `e(G[N(v)]) ≤ (1-δ)Δ²/2`, which is why the factor
`d*(d-1) - (1-δ)*Δ^2` appears. -/
theorem pt_key_arith {δ Δ : ℝ} {k D : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : (10 : ℝ) ^ 24 / δ ^ 8 ≤ Δ)
    (hDle : Δ ≤ (D : ℝ)) (hDlt : (D : ℝ) < Δ + 1)
    (hk : (1 - δ / 100) * (Δ + 1) - 1 ≤ (k : ℝ)) (hk' : (k : ℝ) ≤ (1 - δ / 100) * (Δ + 1))
    (d : ℝ) (hd0 : 0 ≤ d) (hdΔ : d ≤ Δ) (hpos : 0 < d + 1 - (k : ℝ)) :
    d + 1 - (k : ℝ)
      ≤ (1 / 4) * (d * (d - 1) - (1 - δ) * Δ ^ 2)
          * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
          * (1 - (D : ℝ) / (3 * (k : ℝ))) := by
  -- ## Basic consequences of the threshold hypothesis on `Δ`
  have hδ8pos : (0:ℝ) < δ^8 := by positivity
  have hΔδ8 : (10:ℝ)^24 ≤ Δ * δ^8 := by
    rw [div_le_iff₀ hδ8pos] at hΔ
    linarith only [hΔ]
  have hδ8le1 : δ^8 ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hδ7le : δ^7 ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hδ8leδ : δ^8 ≤ δ := by nlinarith only [hδ7le, hδ0]
  have hΔpos : (0:ℝ) < Δ := by nlinarith only [hΔδ8, hδ8pos]
  have hΔ0 : (0:ℝ) ≤ Δ := le_of_lt hΔpos
  have hδΔ : (10:ℝ)^24 ≤ δ * Δ := by nlinarith only [hΔδ8, hδ8leδ, hΔ0]
  have hΔge : (10:ℝ)^24 ≤ Δ := by
    have : (10:ℝ)^24 ≤ (10:ℝ)^24 / δ^8 := by
      rw [le_div_iff₀ hδ8pos]; nlinarith only [hδ8le1]
    linarith
  have hΔ1000 : (1000:ℝ) ≤ Δ := by linarith only [hΔge]
  have hc99 : (99/100:ℝ) ≤ 1 - δ/100 := by linarith only [hδ1]
  have hc1 : (1:ℝ) - δ/100 ≤ 1 := by linarith only [hδ0]
  -- ## Facts about `k`
  have hK_le : (k:ℝ) ≤ 1.02*Δ := by nlinarith only [hk', hc1, hΔ1000]
  have hKpos : (0:ℝ) < (k:ℝ) := by nlinarith only [hk, hc99, hΔ1000]
  have hK1pos : (0:ℝ) < (k:ℝ) - 1 := by nlinarith only [hk, hc99, hΔ1000]
  -- ## The last factor `1 - D/(3k)`
  have hQ : (0.65:ℝ) ≤ 1 - (D:ℝ)/(3*(k:ℝ)) := by
    have h3K : (0:ℝ) < 3*(k:ℝ) := by positivity
    have : (D:ℝ)/(3*(k:ℝ)) ≤ 0.35 := by
      rw [div_le_iff₀ h3K]
      nlinarith only [hDlt, hk, hc99, hΔ1000]
    linarith
  -- ## The middle factor `((k-1)/k)^(2D)` dominates `1/8`
  have h2D_le : 2*(D:ℝ) ≤ 2*(Δ+1) := by linarith only [hDlt]
  have hPK1 : 2*(Δ+1) ≤ 2.05*((k:ℝ)-1) := by nlinarith only [hk, hc99, hΔ1000]
  have h2Ddiv : (2*(D:ℝ))/((k:ℝ)-1) ≤ 2.05 := by
    rw [div_le_iff₀ hK1pos]; linarith only [h2D_le, hPK1]
  have hP : (1/8:ℝ) ≤ (((k:ℝ)-1)/(k:ℝ))^(2*D) := by
    have hfrac : (k:ℝ)/((k:ℝ)-1) = 1 + 1/((k:ℝ)-1) := by
      field_simp
      ring
    have hbase_le : (k:ℝ)/((k:ℝ)-1) ≤ Real.exp (1/((k:ℝ)-1)) := by
      have h := Real.add_one_le_exp (1/((k:ℝ)-1))
      rw [hfrac]
      linarith
    have hpow_le : ((k:ℝ)/((k:ℝ)-1))^(2*D) ≤ 8 := by
      have h1 : ((k:ℝ)/((k:ℝ)-1))^(2*D) ≤ (Real.exp (1/((k:ℝ)-1)))^(2*D) :=
        pow_le_pow_left₀ (by positivity) hbase_le (2*D)
      have h2 : (Real.exp (1/((k:ℝ)-1)))^(2*D) = Real.exp ((2*D : ℕ) * (1/((k:ℝ)-1))) :=
        (Real.exp_nat_mul _ _).symm
      rw [h2] at h1
      have h3 : ((2*D : ℕ) : ℝ) * (1/((k:ℝ)-1)) ≤ 2.05 := by
        have hcast : ((2*D:ℕ):ℝ) = 2*(D:ℝ) := by push_cast; ring
        rw [hcast, mul_one_div]
        exact h2Ddiv
      have h4 : Real.exp (((2*D:ℕ):ℝ) * (1/((k:ℝ)-1))) ≤ Real.exp 2.05 :=
        Real.exp_le_exp.mpr h3
      linarith only [h1, h4, exp_205_lt_eight]
    have hinv : (((k:ℝ)-1)/(k:ℝ)) = ((k:ℝ)/((k:ℝ)-1))⁻¹ := by rw [inv_div]
    rw [hinv, inv_pow]
    rw [show (1/8:ℝ) = (8:ℝ)⁻¹ by norm_num]
    have hb : (0:ℝ) < ((k:ℝ)/((k:ℝ)-1))^(2*D) := pow_pos (div_pos hKpos hK1pos) _
    exact (inv_le_inv₀ (by norm_num : (0:ℝ)<8) hb).mpr hpow_le
  -- ## The first factor: `d*(d-1) - (1-δ)Δ²` is `Ω(δΔ²)`
  have hX : (0.9:ℝ)*δ*Δ^2 ≤ d*(d-1) - (1-δ)*Δ^2 := by
    have hdc : (1-δ/100)*(Δ+1)-2 ≤ d := by linarith only [hpos, hk]
    have hm : (1/2:ℝ) ≤ (1-δ/100)*(Δ+1)-2 := by nlinarith only [hc99, hΔ1000]
    have hfac : 0 ≤ (d - ((1-δ/100)*(Δ+1)-2)) * (d + ((1-δ/100)*(Δ+1)-2) - 1) :=
      mul_nonneg (by linarith only [hdc]) (by linarith only [hdc, hm])
    have hmono : ((1-δ/100)*(Δ+1)-2)*((1-δ/100)*(Δ+1)-3) ≤ d*(d-1) := by nlinarith only [hfac]
    have hprod : 3*Δ ≤ 0.08*δ*Δ^2 := by
      have h1 : 3.2*Δ ≤ 0.08*Δ*(δ*Δ) := by
        have h2 := mul_le_mul_of_nonneg_left hδΔ (by linarith only [hΔ0] : (0:ℝ) ≤ 0.08*Δ)
        linarith only [h2, hΔ0]
      nlinarith only [h1, hΔ0]
    nlinarith only [hmono, hprod, hδΔ, hδ0, hδ1, hΔ0]
  -- ## The left-hand side is at most `0.0101·δΔ`
  have hL : d + 1 - (k:ℝ) ≤ 0.0101*δ*Δ := by
    have h1 : d + 1 - (k:ℝ) ≤ δ/100*(Δ+1) + 1 := by nlinarith only [hdΔ, hk]
    nlinarith only [h1, hδΔ, hδ0, hδ1, hΔ0, hΔ1000]
  -- ## Assembly
  have hXnn : (0:ℝ) ≤ d*(d-1) - (1-δ)*Δ^2 := by nlinarith only [hX, hδ0, hΔpos]
  have hKin : (1:ℝ)/(1.02*Δ) ≤ 1/(k:ℝ) := by
    have h := one_div_le_one_div_of_le hKpos hK_le
    simpa using h
  have hstep1 : (1/4)*(0.9*δ*Δ^2) ≤ (1/4)*(d*(d-1) - (1-δ)*Δ^2) :=
    mul_le_mul_of_nonneg_left hX (by norm_num)
  have hstep2 : (1/(1.02*Δ))*(1/8) ≤ (1/(k:ℝ))*(((k:ℝ)-1)/(k:ℝ))^(2*D) :=
    mul_le_mul hKin hP (by norm_num) (by positivity)
  have hstep4 : ((1/4)*(0.9*δ*Δ^2)) * ((1/(1.02*Δ))*(1/8)) ≤
                ((1/4)*(d*(d-1) - (1-δ)*Δ^2)) * ((1/(k:ℝ))*(((k:ℝ)-1)/(k:ℝ))^(2*D)) :=
    mul_le_mul hstep1 hstep2 (by positivity) (by linarith only [hXnn])
  have hstep5 : (((1/4)*(0.9*δ*Δ^2)) * ((1/(1.02*Δ))*(1/8))) * 0.65 ≤
                (((1/4)*(d*(d-1) - (1-δ)*Δ^2)) * ((1/(k:ℝ))*(((k:ℝ)-1)/(k:ℝ))^(2*D)))
                  * (1 - (D:ℝ)/(3*(k:ℝ))) :=
    mul_le_mul hstep4 hQ (by norm_num) (by positivity)
  have hnum : (0.0101:ℝ)*δ*Δ ≤ ((1/4)*(0.9*δ*Δ^2))*((1/(1.02*Δ))*(1/8))*0.65 := by
    have hΔne : Δ ≠ 0 := ne_of_gt hΔpos
    have key : ((1/4)*(0.9*δ*Δ^2))*((1/(1.02*Δ))*(1/8))*0.65
              = ((1/4)*0.9*(1/1.02)*(1/8)*0.65)*(δ*Δ) := by
      field_simp
    rw [key]
    have hc' : (0.0101:ℝ) ≤ (1/4)*0.9*(1/1.02)*(1/8)*0.65 := by norm_num
    have hnn : (0:ℝ) ≤ δ*Δ := by positivity
    calc (0.0101:ℝ)*δ*Δ = 0.0101*(δ*Δ) := by ring
      _ ≤ ((1/4)*0.9*(1/1.02)*(1/8)*0.65)*(δ*Δ) := mul_le_mul_of_nonneg_right hc' hnn
  linarith only [hL, hnum, hstep5]

end Work.Deep.Sparse
