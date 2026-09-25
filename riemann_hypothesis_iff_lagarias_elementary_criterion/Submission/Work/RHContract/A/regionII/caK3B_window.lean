import Mathlib
import Submission.Work.RHContract.A.regionII.caK3B_defs

namespace Work.RHContract.A.regionII

/-- `kcc ξ > 0` for `ξ ≥ 10^5`. -/
lemma kcc_pos {ξ : ℝ} (hξ : 100000 ≤ ξ) : 0 < kcc ξ := by
  rw [kcc]
  have hξ0 : 0 < ξ := by linarith
  have hrp : (0 : ℝ) ≤ ξ ^ (3/4 : ℝ) := Real.rpow_nonneg hξ0.le _
  have h45 : (0 : ℝ) ≤ 0.45 * ξ ^ (3/4 : ℝ) := mul_nonneg (by norm_num) hrp
  refine div_pos ?_ ?_
  · rw [sub_pos, div_lt_one (Real.sqrt_pos.mpr hξ0)]
    have hsnn : (0 : ℝ) ≤ Real.sqrt ξ := Real.sqrt_nonneg ξ
    have hsq : Real.sqrt ξ ^ 2 = ξ := Real.sq_sqrt hξ0.le
    nlinarith [hsnn, hsq, hξ]
  · refine mul_pos ?_ ?_
    · linarith
    · apply Real.log_pos; linarith

/-- Strict form of `le_rpow_div_of_pow_le`: `c^k < x` gives `c < x^{1/k}`. -/
lemma lt_rpow_div_of_pow_lt {x c : ℝ} (k : ℕ) (hc : 0 ≤ c) (hx : 0 ≤ x) (hk : 0 < k)
    (h : c ^ k < x) : c < x ^ (1/(k:ℝ)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : (c ^ k : ℝ) ^ (1/(k:ℝ)) < x ^ (1/(k:ℝ)) :=
    Real.rpow_lt_rpow (pow_nonneg hc k) h (one_div_pos.mpr hk0)
  have h2 : (c ^ k : ℝ) ^ (1/(k:ℝ)) = c := by
    rw [← Real.rpow_natCast c k, ← Real.rpow_mul hc]
    have : (k : ℝ) * (1/(k:ℝ)) = 1 := by field_simp
    rw [this, Real.rpow_one]
  linarith

/-- Algebraic rearrangement: multiplying the RHS of the window hypothesis by
`(e+1)(p-1)^{e+1}` gives `((p-1)/p)^e`. -/
lemma caK3B_rpow_ident {p : ℝ} (hp : 1 < p) (e : ℕ) :
    p ^ (-((e:ℝ)+1)) / (((e:ℝ)+1) * (1 - 1/p)) * (((e:ℝ)+1) * (p-1)^(e+1))
      = ((p-1)/p)^e := by
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  have h1 : p ^ (-((e:ℝ)+1)) = (p ^ (e+1))⁻¹ := by
    rw [Real.rpow_neg hp0.le,
      show ((e:ℝ)+1) = ((e+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [h1]
  have h2 : (1 - 1/p) = (p-1)/p := by field_simp [ne_of_gt hp0] <;> ring
  rw [h2]
  rw [div_pow]
  rw [pow_succ' (p-1) e, pow_succ' p e]
  field_simp [ne_of_gt hp0, ne_of_gt hpm1, (by positivity : ((e:ℝ)+1) ≠ 0)] <;> ring

theorem caK3B_window {ξ : ℝ} {p e : ℕ} (hξ : 100000 ≤ ξ) (hp : 2 ≤ p)
    (hloglt : Real.log ξ < ((e : ℝ) + 1) * Real.log (p : ℝ))
    (hY : Work.RHContract.A.regionII.kcc ξ * Real.log (p : ℝ) <
      (p : ℝ) ^ (-((e : ℝ) + 1)) / (((e : ℝ) + 1) * (1 - 1 / (p : ℝ)))) :
    (p : ℝ) < 1 + (ξ / Work.RHContract.A.regionII.kB ξ) ^ (1 / ((e + 1 : ℕ) : ℝ)) := by
  have hξ0 : 0 < ξ := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hpm1 : 0 < (p : ℝ) - 1 := by linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hlogξ : 0 < Real.log ξ := Real.log_pos (by linarith : (1 : ℝ) < ξ)
  have hkcc : 0 < kcc ξ := kcc_pos hξ
  have hEpos : 0 < ((e : ℝ) + 1) := by positivity
  -- multiply the hypothesis by the positive factor `(e+1)(p-1)^{e+1}`
  have hmult : 0 < ((e:ℝ)+1) * ((p:ℝ)-1)^(e+1) :=
    mul_pos hEpos (pow_pos hpm1 (e+1))
  have hY2 := mul_lt_mul_of_pos_right hY hmult
  have hRHS : (p:ℝ) ^ (-((e:ℝ)+1)) / (((e:ℝ)+1) * (1 - 1/(p:ℝ)))
        * (((e:ℝ)+1) * ((p:ℝ)-1)^(e+1)) = (((p:ℝ)-1)/(p:ℝ))^e :=
    caK3B_rpow_ident hp1 e
  rw [hRHS] at hY2
  -- insert `log ξ < (e+1) log p`
  have hstep1 : kcc ξ * Real.log ξ * ((p:ℝ)-1)^(e+1)
      < kcc ξ * Real.log (p:ℝ) * (((e:ℝ)+1) * ((p:ℝ)-1)^(e+1)) := by
    have h := mul_lt_mul_of_pos_left hloglt (mul_pos hkcc (pow_pos hpm1 (e+1)))
    have e1 : (kcc ξ * ((p:ℝ)-1)^(e+1)) * Real.log ξ
        = kcc ξ * Real.log ξ * ((p:ℝ)-1)^(e+1) := by ring
    have e2 : (kcc ξ * ((p:ℝ)-1)^(e+1)) * (((e:ℝ)+1) * Real.log (p:ℝ))
        = kcc ξ * Real.log (p:ℝ) * (((e:ℝ)+1) * ((p:ℝ)-1)^(e+1)) := by ring
    rwa [e1, e2] at h
  -- the ratio `((p-1)/p)^e` is at most one
  have hratio0 : 0 ≤ ((p:ℝ)-1)/(p:ℝ) := by positivity
  have hratio : ((p:ℝ)-1)/(p:ℝ) ≤ 1 := by
    rw [div_le_one hp0]; linarith
  have hbound : (((p:ℝ)-1)/(p:ℝ))^e ≤ 1 := pow_le_one₀ hratio0 hratio
  have hkey : kcc ξ * Real.log ξ * ((p:ℝ)-1)^(e+1) < 1 :=
    lt_of_lt_of_le (lt_trans hstep1 hY2) hbound
  -- multiply by ξ and rewrite the product as `kB ξ`
  have hkey2 : ξ * (kcc ξ * Real.log ξ * ((p:ℝ)-1)^(e+1)) < ξ := by
    have := mul_lt_mul_of_pos_left hkey hξ0
    rwa [mul_one] at this
  have hkBlt : kB ξ * ((p:ℝ)-1)^(e+1) < ξ := by
    have e : ξ * (kcc ξ * Real.log ξ * ((p:ℝ)-1)^(e+1))
        = kB ξ * ((p:ℝ)-1)^(e+1) := by rw [kB]; ring
    rwa [e] at hkey2
  have hkBpos : 0 < kB ξ := by
    rw [kB]
    exact mul_pos (mul_pos hξ0 hkcc) hlogξ
  have hdiv : ((p:ℝ)-1)^(e+1) < ξ / kB ξ := by
    rw [lt_div_iff₀ hkBpos, mul_comm]
    exact hkBlt
  have hxnn : 0 ≤ ξ / kB ξ := le_of_lt (div_pos hξ0 hkBpos)
  have hfin : (p:ℝ) - 1 < (ξ / kB ξ) ^ (1 / ((e + 1 : ℕ) : ℝ)) :=
    lt_rpow_div_of_pow_lt (e+1) (by linarith : (0:ℝ) ≤ (p:ℝ)-1) hxnn (by omega) hdiv
  linarith

end Work.RHContract.A.regionII
