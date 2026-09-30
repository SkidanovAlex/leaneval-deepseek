import Mathlib
import Submission.Work.BW.rdnDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## Helper estimates for `rdnNumB`

The main inequality is proved by taking logarithms of both sides.  All the
quantities involved are positive, and writing `A = log 2`, `B = log r`,
`C = log d`, `log u = A + B + C` (with `u = rdnU r d = 2 r d`) the target turns
into a *linear* inequality in `A, B, C` whose coefficients are all negative.
-/

/-- The cap `rdnCap r = 26.8 r/(r−0.536)` satisfies `cap·ρ ≤ 26.8ρ + 14.4`. -/
lemma rdnCap_mul_le {r ρ : ℕ} (hr : 2 ≤ r) (hρr : ρ < r) :
    rdnCap r * (ρ : ℝ) ≤ 26.8 * (ρ : ℝ) + 14.4 := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hpos : 0 < (r:ℝ) - 0.536 := by linarith
  have hρr' : (ρ:ℝ) + 1 ≤ (r:ℝ) := by
    have h : ρ + 1 ≤ r := by omega
    exact_mod_cast h
  unfold rdnCap
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [hr2, hρr']

/-- `log (rdnU r d) = log 2 + log r + log d`. -/
lemma log_rdnU {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) :
    Real.log (rdnU r d) = Real.log 2 + Real.log r + Real.log d := by
  have hr' : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  rw [rdnU, Real.log_mul (by positivity) hd'.ne', Real.log_mul (by norm_num) hr'.ne']

/-- Upper bound for `log (constB r ρ)`. -/
lemma log_constB_le {r ρ : ℕ} (hr : 2 ≤ r) (hρ1 : 1 ≤ ρ) (hρr : ρ < r) :
    Real.log (constB r ρ) ≤
      (1 - (ρ:ℝ)) * Real.log 2 + 3*(ρ:ℝ)*Real.log r + ((ρ:ℝ)+1)*(Real.log 2 + Real.log r) := by
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hρpos : (0:ℝ) < (ρ:ℝ) := by exact_mod_cast (by omega : 0 < ρ)
  have hfactpos : (0:ℝ) < (ρ.factorial : ℝ) := by exact_mod_cast ρ.factorial_pos
  have hdfpos : (0:ℝ) < ((r+1).descFactorial (ρ+1) : ℝ) := by
    have : 0 < (r+1).descFactorial (ρ+1) := Nat.descFactorial_pos.mpr (by omega)
    exact_mod_cast this
  have hlog : Real.log (constB r ρ) =
      (1 - (ρ:ℝ)) * Real.log 2 + 2 * Real.log (ρ.factorial:ℝ) + (ρ:ℝ) * Real.log r
        + Real.log ((r+1).descFactorial (ρ+1) : ℝ) := by
    unfold constB
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_zpow]
    push_cast
    ring
  rw [hlog]
  have h1 : Real.log (ρ.factorial:ℝ) ≤ (ρ:ℝ)*Real.log r := by
    have hfe : ((ρ.factorial:ℝ)) ≤ ((r:ℝ)^ρ) := by
      have h1' : (ρ.factorial:ℝ) ≤ (ρ:ℝ)^ρ := by exact_mod_cast Nat.factorial_le_pow ρ
      have h2' : (ρ:ℝ)^ρ ≤ (r:ℝ)^ρ :=
        pow_le_pow_left₀ (le_of_lt hρpos) (by exact_mod_cast (le_of_lt hρr)) _
      linarith
    calc Real.log (ρ.factorial:ℝ) ≤ Real.log ((r:ℝ)^ρ) := Real.log_le_log hfactpos hfe
      _ = (ρ:ℝ) * Real.log r := by rw [Real.log_pow]
  have h2 : Real.log ((r+1).descFactorial (ρ+1) : ℝ) ≤ ((ρ:ℝ)+1)*(Real.log 2 + Real.log r) := by
    have hdle : ((r+1).descFactorial (ρ+1) : ℝ) ≤ ((r+1:ℝ))^(ρ+1) := by
      exact_mod_cast Nat.descFactorial_le_pow (r+1) (ρ+1)
    have h2r : ((r+1:ℝ)) ≤ 2 * (r:ℝ) := by linarith
    have hpow : ((r+1:ℝ))^(ρ+1) ≤ (2*(r:ℝ))^(ρ+1) := pow_le_pow_left₀ (by positivity) h2r _
    calc Real.log ((r+1).descFactorial (ρ+1) : ℝ) ≤ Real.log (((r+1:ℝ))^(ρ+1)) :=
          Real.log_le_log hdfpos hdle
      _ ≤ Real.log ((2*(r:ℝ))^(ρ+1)) := Real.log_le_log (by positivity) hpow
      _ = ((ρ:ℝ)+1) * (Real.log 2 + Real.log r) := by
            rw [Real.log_pow, Real.log_mul (by norm_num) hrpos.ne']
            push_cast; ring
  linarith

/-- Upper bound for `log (rdnGam r d)`. -/
lemma log_rdnGam_le {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    Real.log (rdnGam r d) ≤ 2 * Real.log 2 - 35.65 * Real.log (rdnU r d) := by
  have hr1 : 1 ≤ r := by omega
  have hu : 0 < rdnU r d := rdnU_pos hr1 hd
  have hu1 : 1 ≤ rdnU r d := rdnU_one_le hr1 hd
  have hupos : (0:ℝ) < (rdnU r d) ^ (50 * Real.log 2) := Real.rpow_pos_of_pos hu _
  have hlogu : 0 ≤ Real.log (rdnU r d) := Real.log_nonneg hu1
  have hl2 : (34.65:ℝ) ≤ 50 * Real.log 2 := by
    have h := Real.log_two_gt_d9; nlinarith
  have hexp : Real.log (rdnGam r d) =
      2 * Real.log 2 - (1 + 50 * Real.log 2) * Real.log (rdnU r d) := by
    unfold rdnGam
    rw [Real.log_div (by norm_num) (by positivity),
        Real.log_mul hu.ne' hupos.ne', Real.log_rpow hu]
    rw [show Real.log 4 = 2 * Real.log 2 from by
      rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow]; norm_num]
    ring
  rw [hexp]
  have : 35.65 * Real.log (rdnU r d) ≤ (1 + 50 * Real.log 2) * Real.log (rdnU r d) :=
    mul_le_mul_of_nonneg_right (by linarith) hlogu
  linarith

/-- `log (rdnPC r d) = 26.8 log (rdnU r d)`. -/
lemma log_rdnPC {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) :
    Real.log (rdnPC r d) = 26.8 * Real.log (rdnU r d) := by
  unfold rdnPC
  rw [Real.log_rpow (rdnU_pos hr hd)]

/-- Lower bound for `ρ · log (rdnDel r d)`. -/
lemma rho_logRdnDel_ge {r ρ d : ℕ} (hr : 2 ≤ r) (hρ1 : 1 ≤ ρ) (hρr : ρ < r) (hd : 1 ≤ d) :
    -((26.8 * (ρ:ℝ) + 14.4) * Real.log (rdnU r d)) ≤ (ρ:ℝ) * Real.log (rdnDel r d) := by
  have hr1 : 1 ≤ r := by omega
  have hu : 0 < rdnU r d := rdnU_pos hr1 hd
  have hupos : (0:ℝ) < (rdnU r d) ^ (rdnCap r) := Real.rpow_pos_of_pos hu _
  have hlogu : 0 ≤ Real.log (rdnU r d) := Real.log_nonneg (rdnU_one_le hr1 hd)
  have hρpos : (0:ℝ) < (ρ:ℝ) := by exact_mod_cast (by omega : 0 < ρ)
  have hdel : Real.log (rdnDel r d) =
      Real.log (11.75/8) - rdnCap r * Real.log (rdnU r d) := by
    unfold rdnDel rdnPowD
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) hupos.ne',
        Real.log_rpow hu]
    rw [Real.log_div (by norm_num : (11.75:ℝ) ≠ 0) (by norm_num : (8:ℝ) ≠ 0)]
    ring
  rw [hdel]
  have h11 : 0 ≤ Real.log (11.75/8) := Real.log_nonneg (by norm_num)
  have hcap : rdnCap r * (ρ:ℝ) ≤ 26.8 * (ρ:ℝ) + 14.4 := rdnCap_mul_le hr hρr
  nlinarith [h11, hcap, hlogu, mul_nonneg hlogu hρpos.le]

/-- **BW §21 check (30), case `0 × H'`** (`rdnNumB`). Let `u = rdnU r d`, `cap = rdnCap r`
(so `u = 2rd`, `cap = 26.8 r/(r-0.536)`). Route: first prove the "reduced" inequality
`2 * ρ^(2ρ) * ρ! * (r+1)^(ρ+1) * r^(ρ+1) * 32^(r+1) ≤ 64^(r-ρ) * 4 * u^(26.8+34.65ρ - cap*ρ)`
using `ρ^(2ρ) ≤ r^(2ρ)`, `(r+1)^(ρ+1) ≤ (2r)^(ρ+1)`, `u ≥ 2r`, `cap*ρ ≤ 26.8ρ+14.4`, `ρ < r`;
then derive this statement from it with `Nat.factorial_le_pow`, `Nat.descFactorial_le_pow`,
`50*Real.log 2 ≥ 34.65` (`Real.log_two_gt_d9`), `u ≥ 2r ≥ 1`, and `Real.rpow_add`. -/
theorem rdnNumB {r ρ : ℕ} (hr : 2 ≤ r) (hρ1 : 1 ≤ ρ) (hρr : ρ < r) (d : ℕ) (hd : 1 ≤ d) :
    constB r ρ * ((r : ℝ) ^ (r + 1) * ((32 : ℝ) * (d : ℝ)) ^ (r + 1)) * (rdnGam r d) ^ ρ *
        (ρ.factorial : ℝ) ≤
      (64 * (r : ℝ) * (d : ℝ)) ^ (r - ρ) * 4 * (d : ℝ) * rdnPC r d * (rdnDel r d) ^ ρ := by
  have hr1 : 1 ≤ r := by omega
  have hd2 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hrp : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hdp : (0:ℝ) < (d:ℝ) := by linarith
  have hρnn : (0:ℝ) ≤ (ρ:ℝ) := by exact_mod_cast (by omega : 0 ≤ ρ)
  have hu : 0 < rdnU r d := rdnU_pos hr1 hd
  have hcb : 0 < constB r ρ := by
    have hfactpos : (0:ℝ) < (ρ.factorial : ℝ) := by exact_mod_cast ρ.factorial_pos
    have hdfpos : (0:ℝ) < ((r+1).descFactorial (ρ+1) : ℝ) := by
      have : 0 < (r+1).descFactorial (ρ+1) := Nat.descFactorial_pos.mpr (by omega)
      exact_mod_cast this
    unfold constB
    exact mul_pos (mul_pos (mul_pos (zpow_pos (by norm_num) _) (pow_pos hfactpos 2))
      (pow_pos hrp ρ)) hdfpos
  have hgam : 0 < rdnGam r d := by unfold rdnGam; positivity
  have hdel : 0 < rdnDel r d := by unfold rdnDel rdnPowD; positivity
  have hpc : 0 < rdnPC r d := by unfold rdnPC; positivity
  have hF : 0 < (ρ.factorial : ℝ) := by exact_mod_cast ρ.factorial_pos
  have hA : 0 < (r : ℝ) ^ (r + 1) * ((32 : ℝ) * (d : ℝ)) ^ (r + 1) := by positivity
  have hLpos : 0 < constB r ρ * ((r : ℝ) ^ (r + 1) * ((32 : ℝ) * (d : ℝ)) ^ (r + 1)) *
      (rdnGam r d) ^ ρ * (ρ.factorial : ℝ) := by positivity
  have hRpos : 0 < (64 * (r : ℝ) * (d : ℝ)) ^ (r - ρ) * 4 * (d : ℝ) * rdnPC r d *
      (rdnDel r d) ^ ρ := by positivity
  rw [← Real.log_le_log_iff hLpos hRpos]
  -- log of the left-hand side
  have hlogL : Real.log (constB r ρ * ((r : ℝ) ^ (r + 1) * ((32 : ℝ) * (d : ℝ)) ^ (r + 1)) *
        (rdnGam r d) ^ ρ * (ρ.factorial : ℝ))
      = Real.log (constB r ρ) + Real.log ((r:ℝ)^(r+1)) + Real.log (((32:ℝ)*(d:ℝ))^(r+1))
        + (ρ:ℝ) * Real.log (rdnGam r d) + Real.log (ρ.factorial:ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow (rdnGam r d) ρ]
    ring
  -- log of the right-hand side
  have hlogR : Real.log ((64 * (r : ℝ) * (d : ℝ)) ^ (r - ρ) * 4 * (d : ℝ) * rdnPC r d *
        (rdnDel r d) ^ ρ)
      = ((r:ℝ) - (ρ:ℝ)) * (6 * Real.log 2 + Real.log r + Real.log d) + 2 * Real.log 2
        + Real.log d + 26.8 * Real.log (rdnU r d) + (ρ:ℝ) * Real.log (rdnDel r d) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow (rdnDel r d) ρ]
    rw [Real.log_pow (64 * (r:ℝ) * (d:ℝ)) (r - ρ)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by norm_num) hrp.ne']
    rw [log_rdnPC hr1 hd]
    have h64 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64:ℝ) = 2^6 from by norm_num, Real.log_pow]; norm_num
    have h4log : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow]; norm_num
    have hsub : ((r - ρ : ℕ) : ℝ) = (r:ℝ) - (ρ:ℝ) := Nat.cast_sub (le_of_lt hρr)
    rw [h64, h4log, hsub]
  rw [log_rdnU hr1 hd] at hlogR
  rw [hlogL, hlogR]
  -- the linear comparison
  have h1 : Real.log (constB r ρ) ≤ (1 - (ρ:ℝ)) * Real.log 2 + 3*(ρ:ℝ)*Real.log r
      + ((ρ:ℝ)+1)*(Real.log 2 + Real.log r) := log_constB_le hr hρ1 hρr
  have h2 : Real.log ((r:ℝ)^(r+1)) = ((r:ℝ)+1)*Real.log r := by rw [Real.log_pow]; push_cast; ring
  have h3 : Real.log (((32:ℝ)*(d:ℝ))^(r+1)) = ((r:ℝ)+1)*(5*Real.log 2 + Real.log d) := by
    rw [Real.log_pow, Real.log_mul (by norm_num) hdp.ne']
    have h32 : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32:ℝ) = 2^5 from by norm_num, Real.log_pow]; norm_num
    rw [h32]; push_cast; ring
  have h4 : Real.log (rdnGam r d) ≤ 2 * Real.log 2
      - 35.65 * (Real.log 2 + Real.log r + Real.log d) := by
    have h := log_rdnGam_le hr hd
    rwa [log_rdnU hr1 hd] at h
  have h4' : (ρ:ℝ) * Real.log (rdnGam r d) ≤ (ρ:ℝ) * (2 * Real.log 2
      - 35.65 * (Real.log 2 + Real.log r + Real.log d)) := mul_le_mul_of_nonneg_left h4 hρnn
  have h5 : Real.log (ρ.factorial:ℝ) ≤ (ρ:ℝ)*Real.log r := by
    have hfe : ((ρ.factorial:ℝ)) ≤ ((r:ℝ)^ρ) := by
      have h1' : (ρ.factorial:ℝ) ≤ (ρ:ℝ)^ρ := by exact_mod_cast Nat.factorial_le_pow ρ
      have h2' : (ρ:ℝ)^ρ ≤ (r:ℝ)^ρ :=
        pow_le_pow_left₀ hρnn (by exact_mod_cast (le_of_lt hρr)) _
      linarith
    calc Real.log (ρ.factorial:ℝ) ≤ Real.log ((r:ℝ)^ρ) :=
          Real.log_le_log (by exact_mod_cast ρ.factorial_pos) hfe
      _ = (ρ:ℝ) * Real.log r := by rw [Real.log_pow]
  have h6 := rho_logRdnDel_ge hr hρ1 hρr hd
  rw [log_rdnU hr1 hd] at h6
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hρ2 : (1:ℝ) ≤ (ρ:ℝ) := by exact_mod_cast hρ1
  have hG2 : (0:ℝ) ≤ Real.log 2 := by
    exact le_of_lt (Real.log_pos (by norm_num))
  have hGr : (0:ℝ) ≤ Real.log r := Real.log_nonneg (by linarith)
  have hGd : (0:ℝ) ≤ Real.log d := Real.log_nonneg hd2
  nlinarith [h1, h2, h3, h4', h5, h6, hG2, hGr, hGd, hr2, hρ2,
    mul_nonneg hG2 (le_of_lt hrp), mul_nonneg hGr (le_of_lt hrp), mul_nonneg hGd (le_of_lt hrp),
    mul_nonneg hG2 hρnn, mul_nonneg hGr hρnn, mul_nonneg hGd hρnn,
    mul_nonneg hG2 (mul_nonneg hρnn (le_of_lt hrp)), mul_nonneg hGr (mul_nonneg hρnn (le_of_lt hrp)),
    mul_nonneg hGd (mul_nonneg hρnn (le_of_lt hrp))]

end Work.BW
