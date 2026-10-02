import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.log_large_of_growth

/-!
# The Azuma exponents of the naive-colouring concentration proof

This module proves `Work.Deep.Sparse.ncp_azuma_exponents`: the purely arithmetic step
which turns the two Azuma–Hoeffding estimates of the concentration proof of
`X = pairTerm v - tripleTerm v` into the paper's tail `exp (-(log (D+2))^4/5000 - 2)`.

Setting: `D` is a degree bound, `k` the number of colours, `δ ∈ (0,1]` the density slack and
`ω = ncpOmega G k D v` the expectation lower bound.  The hypotheses `hsp` and `hbig` are the
paper's two saturation hypotheses; together with `D ≤ 2k` they force

* `log (D+2) ≥ 44` and `D ≥ 10^6` (hence `k ≥ 5`),
* `ω ≥ δ D / 2048`.

The two conclusions are the statements that each of the exponents produced by the two Azuma
arguments,

`2 (ω/18)^2 / (D · (2 · occWsum 18)^2)`  and  `2 (ω/18)^2 / (7200000 · D)`,

dominates `(log (D+2))^4/5000 + 3`, whence the factor `2` in front of the Gaussian tail is paid
for by the shift `-2` in the exponent.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The Lipschitz constant `occWsum ncpJ = 667` -/

/-- The Lipschitz constant of the truncated occupancy statistic at level `ncpJ = 18` is `667`. -/
lemma occWsum_ncpJ : occWsum ncpJ = 667 := by
  have h18 : (Finset.Icc 2 18 : Finset ℕ) =
      {2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18} := by decide
  unfold occWsum ncpJ
  rw [h18]
  norm_num [occW]

/-! ## 2. Paying for the factor `2` with the shift `-2` -/

/-- If `s + 3 ≤ t` then `2 exp(-t) ≤ exp(-s-2)`: the factor `2` is absorbed by `exp 3 ≥ 2`
together with the shift `-2`, and the missing `exp 1 ≥ 2`. -/
lemma two_mul_exp_le_exp {s t : ℝ} (h : s + 3 ≤ t) :
    2 * Real.exp (-t) ≤ Real.exp (-s - 2) := by
  have h1 : Real.exp (-t) ≤ Real.exp (-(s + 3)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : 2 * Real.exp (-t) ≤ 2 * Real.exp (-(s + 3)) := by linarith
  have hsplit : Real.exp (-(s + 3)) = Real.exp (-s - 2) * Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcoef : 2 * Real.exp (-1) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
    have := Real.add_one_le_exp 1
    linarith
  have hnonneg : 0 ≤ Real.exp (-s - 2) := Real.exp_nonneg _
  calc 2 * Real.exp (-t) ≤ 2 * Real.exp (-(s + 3)) := h2
    _ = (2 * Real.exp (-1)) * Real.exp (-s - 2) := by rw [hsplit]; ring
    _ ≤ 1 * Real.exp (-s - 2) := mul_le_mul_of_nonneg_right hcoef hnonneg
    _ = Real.exp (-s - 2) := one_mul _

/-! ## 3. The arithmetic core -/

/-- **The Azuma exponent dominates the target.**  If `log (D+2)` is at least `44`, if
`10^6 L^8 ≤ δ^2 D` and `δ D ≤ 2048 ω`, if `C ≤ 7200000` is a positive denominator constant,
then `2 exp(-2 (ω/18)^2/(D C)) ≤ exp(-L^4/5000 - 2)`.  Both Azuma exponents of the
concentration proof have this shape. -/
lemma azuma_exp_aux {δ Ω L D C : ℝ} (hδ : 0 < δ) (hD : 0 < D) (hC : 0 < C)
    (hCle : C ≤ 7200000) (hL : 44 ≤ L)
    (hbig : (10:ℝ)^6 * L^8 ≤ δ^2 * D) (hΩ : δ * D ≤ 2048 * Ω) :
    2 * Real.exp (-(2 * ((1/3) * ((1/6) * Ω))^2) / (D * C))
      ≤ Real.exp (-(L^4)/5000 - 2) := by
  have hLpos : 0 < L := by linarith
  have hCD : (0:ℝ) < C*D := mul_pos hC hD
  have hQ : (1/3) * ((1/6) * Ω) = Ω/18 := by ring
  have hQlow : δ * D / 36864 ≤ Ω / 18 := by linarith [hΩ]
  have hsq : (δ * D / 36864)^2 ≤ (Ω/18)^2 := pow_le_pow_left₀ (by positivity) hQlow 2
  have hstep1 : 2 * (δ*D/36864)^2 / (C*D) ≤ 2 * (Ω/18)^2 / (C*D) := by
    refine div_le_div_of_nonneg_right ?_ hCD.le
    nlinarith [hsq]
  have hsimp : 2 * (δ*D/36864)^2 / (C*D) = 2*δ^2*D/(36864^2*C) := by
    field_simp
  have hstep2 : 2 * ((10:ℝ)^6 * L^8) / (36864^2 * 7200000) ≤ 2*δ^2*D/(36864^2*C) := by
    have hnum : 2 * ((10:ℝ)^6 * L^8) ≤ 2 * (δ^2 * D) := by linarith [hbig]
    have hden : 36864^2 * C ≤ 36864^2 * (7200000:ℝ) := by nlinarith [hCle, hC]
    have h1 : 2 * ((10:ℝ)^6 * L^8) / (36864^2 * 7200000)
        ≤ 2 * (δ^2*D) / (36864^2*(7200000:ℝ)) :=
      div_le_div_of_nonneg_right hnum (by norm_num)
    have h2 : 2 * (δ^2*D) / (36864^2 * (7200000:ℝ)) ≤ 2 * (δ^2*D) / (36864^2 * C) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    exact le_trans h1 (by simpa [mul_assoc] using h2)
  have hL4 : (3748096:ℝ) ≤ L^4 := by
    have h44 : (44:ℝ)^4 ≤ L^4 := pow_le_pow_left₀ (by norm_num) hL 4
    norm_num at h44 ⊢
    exact h44
  have hL8 : (3748096:ℝ) * L^4 ≤ L^8 := by
    calc (3748096:ℝ) * L^4 ≤ L^4 * L^4 := mul_le_mul_of_nonneg_right hL4 (by positivity)
      _ = L^8 := by ring
  have hstep3 : L^4/2000 ≤ 2 * ((10:ℝ)^6 * L^8) / (36864^2 * 7200000) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hL4nn : (0:ℝ) ≤ L^4 := by positivity
    nlinarith [hL8, hL4, hL4nn]
  have hstep4 : L^4/5000 + 3 ≤ L^4/2000 := by
    have h1 : L^4/5000 + 3 = (L^4 + 15000)/5000 := by field_simp; ring
    rw [h1, div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [hL4]
  have hchain : L^4/5000 + 3 ≤ 2 * ((1/3) * ((1/6) * Ω))^2 / (D * C) := by
    rw [hQ]
    calc L^4/5000 + 3 ≤ L^4/2000 := hstep4
      _ ≤ 2 * ((10:ℝ)^6 * L^8) / (36864^2 * 7200000) := hstep3
      _ ≤ 2*δ^2*D/(36864^2*C) := hstep2
      _ = 2 * (δ*D/36864)^2 / (C*D) := hsimp.symm
      _ ≤ 2 * (Ω/18)^2 / (C*D) := hstep1
      _ = 2 * (Ω/18)^2 / (D*C) := by rw [mul_comm C D]
  have hfin := two_mul_exp_le_exp hchain
  simpa only [neg_div] using hfin

/-! ## 4. The power bound `((k-1)/k)^(2D) ≥ 1/256` -/

/-- For `k ≥ 5 ≤ k` and `D ≤ 2k` one has `((k-1)/k)^(2D) ≥ 1/256`.  This is the sharp form of
`(1-1/k)^(2D) ≥ (1-1/k)^(4k)` (the base lies in `[0,1]`), evaluated through the elementary
logarithmic bound `log (1+t) ≤ t`. -/
lemma pow_ratio_ge {k D : ℕ} (hk : 5 ≤ k) (hDk : D ≤ 2*k) :
    (1:ℝ)/256 ≤ (((k:ℝ)-1)/(k:ℝ))^(2*D) := by
  have hK1 : (0:ℝ) < (k:ℝ) - 1 := by
    have : (1:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 1 < k)
    linarith
  have hKpos : (0:ℝ) < (k:ℝ) := by linarith
  have hqpos : 0 < ((k:ℝ)-1)/(k:ℝ) := div_pos hK1 hKpos
  have hlog : -(1/((k:ℝ)-1)) ≤ Real.log (((k:ℝ)-1)/(k:ℝ)) := by
    have h1 : Real.log (((k:ℝ)-1)/(k:ℝ)) = - Real.log ((k:ℝ)/((k:ℝ)-1)) := by
      rw [← Real.log_inv]; congr 1; field_simp
    rw [h1]
    have h2 : Real.log ((k:ℝ)/((k:ℝ)-1)) ≤ 1/((k:ℝ)-1) := by
      have hpos : 0 < (k:ℝ)/((k:ℝ)-1) := div_pos hKpos hK1
      have h3 := Real.log_le_sub_one_of_pos hpos
      have h4 : (k:ℝ)/((k:ℝ)-1) - 1 = 1/((k:ℝ)-1) := by field_simp; ring
      linarith [h3, h4]
    linarith [h2]
  have h2D : (↑(2*D) : ℝ) ≤ 5 * ((k:ℝ) - 1) := by
    have hnat : 2*D ≤ 5*(k-1) := by omega
    have hcast : ((2*D : ℕ) : ℝ) ≤ ((5*(k-1) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hk1 : ((k-1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
    push_cast at hcast
    rw [hk1] at hcast
    push_cast
    linarith [hcast]
  have harg : -(5:ℝ) ≤ (↑(2*D) : ℝ) * Real.log (((k:ℝ)-1)/(k:ℝ)) := by
    have h2Dnn : (0:ℝ) ≤ (↑(2*D) : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog h2Dnn
    have hquot : (↑(2*D) : ℝ) * (1/((k:ℝ)-1)) ≤ 5 := by
      rw [mul_one_div, div_le_iff₀ hK1]; linarith [h2D]
    linarith [hmul, hquot]
  have hconv : (((k:ℝ)-1)/(k:ℝ))^(2*D)
      = Real.exp ((↑(2*D) : ℝ) * Real.log (((k:ℝ)-1)/(k:ℝ))) := by
    rw [Real.exp_nat_mul, Real.exp_log hqpos]
  have hexp5 : Real.exp (-(5:ℝ)) ≤ (((k:ℝ)-1)/(k:ℝ))^(2*D) := by
    rw [hconv]; exact Real.exp_le_exp.mpr harg
  have he5 : Real.exp 5 ≤ (256:ℝ) := by
    have h1 : Real.exp 5 = (Real.exp 1)^5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    calc (Real.exp 1)^5 ≤ ((68:ℝ)/25)^5 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_le_68_div_25 5
      _ ≤ 256 := by norm_num
  have h256 : (1:ℝ)/256 ≤ Real.exp (-(5:ℝ)) := by
    have h5 : Real.exp (-(5:ℝ)) = (Real.exp 5)⁻¹ := by rw [← Real.exp_neg]
    rw [one_div, h5, inv_le_inv₀ (by norm_num : (0:ℝ) < 256) (Real.exp_pos 5)]
    exact he5
  exact le_trans h256 hexp5

/-! ## 5. The lower bound `ω ≥ δ D / 2048` -/

/-- **The expectation lower bound** `δ D ≤ 2048 ω`.  The three factors of
`ω = (N/2)·(1/k)·((k-1)/k)^(2D)` are bounded below by `δD²/4` (`hsp`), by `1/(2D)` (`k ≤ 2D`)
and by `1/256` (`D ≤ 2k`, `pow_ratio_ge`); moreover `hbig` forces `D ≥ 10^6`, hence `k ≥ 5`. -/
lemma ncpOmega_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) (hkD : (k : ℝ) ≤ 2 * D)
    (v : V) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((nonAdjPairs G v).card : ℝ) / 2)
    (hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ)) :
    δ * (D : ℝ) ≤ 2048 * ncpOmega G k D v := by
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hexp3 : Real.exp 1 ≤ (D:ℝ) + 2 := by have := exp_one_le_68_div_25; linarith
  have hL1 : (1:ℝ) ≤ Real.log ((D:ℝ)+2) :=
    (Real.le_log_iff_exp_le (by linarith : (0:ℝ) < (D:ℝ)+2)).mpr hexp3
  have hpow1 : (1:ℝ) ≤ (Real.log ((D:ℝ)+2))^8 := one_le_pow₀ hL1
  have hδ2le : δ^2 ≤ 1 := by nlinarith [hδ, hδ1]
  have hDbig : (10:ℝ)^6 ≤ (D:ℝ) := by
    calc (10:ℝ)^6 ≤ (10:ℝ)^6 * (Real.log ((D:ℝ)+2))^8 :=
          le_mul_of_one_le_right (by norm_num) hpow1
      _ ≤ δ^2 * (D:ℝ) := hbig
      _ ≤ 1 * (D:ℝ) := mul_le_mul_of_nonneg_right hδ2le (by linarith)
      _ = (D:ℝ) := one_mul _
  have hDge6 : 1000000 ≤ D := by
    have h : ((1000000 : ℕ) : ℝ) ≤ (D:ℝ) := by norm_num at hDbig ⊢; exact hDbig
    exact_mod_cast h
  have hk5 : 5 ≤ k := by omega
  have hN : δ * (D:ℝ)^2/4 ≤ ((nonAdjPairs G v).card : ℝ)/2 := by
    have := hsp; ring_nf at this ⊢; linarith
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have h1k : (1:ℝ)/(2*(D:ℝ)) ≤ 1/(k:ℝ) := one_div_le_one_div_of_le hkpos hkD
  have h3 : (1:ℝ)/256 ≤ (((k:ℝ)-1)/(k:ℝ))^(2*D) := pow_ratio_ge hk5 hDk
  have hmono : (δ * (D:ℝ)^2/4) * ((1/(2*(D:ℝ))) * (1/256))
      ≤ (((nonAdjPairs G v).card : ℝ)/2) * ((1/(k:ℝ)) * (((k:ℝ)-1)/(k:ℝ))^(2*D)) := by
    apply mul_le_mul hN
    · exact mul_le_mul h1k h3 (by norm_num) (by positivity)
    · positivity
    · positivity
  have hval : (δ * (D:ℝ)^2/4) * ((1/(2*(D:ℝ))) * (1/256)) = δ*(D:ℝ)/2048 := by
    field_simp; ring
  have hΩeq : ncpOmega G k D v
      = (((nonAdjPairs G v).card : ℝ)/2) * ((1/(k:ℝ)) * (((k:ℝ)-1)/(k:ℝ))^(2*D)) := rfl
  calc δ * (D:ℝ) = 2048 * (δ*(D:ℝ)/2048) := by ring
    _ = 2048 * ((δ * (D:ℝ)^2/4) * ((1/(2*(D:ℝ))) * (1/256))) := by rw [hval]
    _ ≤ 2048 * ((((nonAdjPairs G v).card : ℝ)/2)
          * ((1/(k:ℝ)) * (((k:ℝ)-1)/(k:ℝ))^(2*D))) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 2048 * ncpOmega G k D v := by rw [hΩeq]

theorem ncp_azuma_exponents {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) (hkD : (k : ℝ) ≤ 2 * D)
    (hdeg : ∀ x : V, G.degree x ≤ D) (v : V)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((nonAdjPairs G v).card : ℝ) / 2)
    (hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ)) :
    (2 * Real.exp (-(2 * ((1 / 3) * ((1 / 6) * ncpOmega G k D v)) ^ 2)
        / ((D : ℝ) * (2 * occWsum ncpJ) ^ 2))
        ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2))
    ∧ (2 * Real.exp (-(2 * ((1 / 3) * ((1 / 6) * ncpOmega G k D v)) ^ 2) / ((7200000 : ℝ) * (D : ℝ)))
        ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2)) := by
  have hL44 : 44 ≤ Real.log ((D:ℝ)+2) := by
    have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    have hδ2le : δ^2 ≤ 1 := by nlinarith [hδ0, hδ1]
    have hbig' : (10:ℝ)^6 * (Real.log ((D:ℝ)+2))^8 ≤ (D:ℝ) := by
      calc (10:ℝ)^6 * (Real.log ((D:ℝ)+2))^8 ≤ δ^2 * (D:ℝ) := hbig
        _ ≤ 1 * (D:ℝ) := mul_le_mul_of_nonneg_right hδ2le (by linarith)
        _ = (D:ℝ) := one_mul _
    exact log_large_of_growth hD1 hbig'
  have hΩ : δ * (D:ℝ) ≤ 2048 * ncpOmega G k D v :=
    ncpOmega_ge G hk hD hDk hkD v hδ0 hδ1 hsp hbig
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  constructor
  · exact azuma_exp_aux (δ := δ) (Ω := ncpOmega G k D v) (L := Real.log ((D:ℝ)+2))
      (D := (D:ℝ)) (C := (2 * occWsum ncpJ)^2) hδ0 hDpos (by rw [occWsum_ncpJ]; norm_num)
      (by rw [occWsum_ncpJ]; norm_num) hL44 hbig hΩ
  · have h := azuma_exp_aux (δ := δ) (Ω := ncpOmega G k D v) (L := Real.log ((D:ℝ)+2))
      (D := (D:ℝ)) (C := 7200000) hδ0 hDpos (by norm_num) (le_refl _) hL44 hbig hΩ
    rw [show ((7200000:ℝ) * (D:ℝ)) = (D:ℝ) * 7200000 by ring]
    exact h

end Work.Deep.Sparse
