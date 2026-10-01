import Mathlib
import Submission.Work.LinnikAreas.Density4.exp_neg_mul_log_pow_le

namespace Work.LinnikAreas.Density4

/-- For `β ≥ 0` the iterated logarithm `(log log q)^β` is eventually bounded by a
constant multiple of `log q`. -/
lemma exists_rpow_loglog_le_log_mul (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (Real.log (Real.log (q:ℝ))) ^ β ≤ C * Real.log (q:ℝ) := by
  set δ : ℝ := 1/(β+1) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδβ : δ * β ≤ 1 := by
    rw [hδdef, one_div, inv_mul_eq_div, div_le_one (by linarith : (0:ℝ) < β+1)]
    linarith
  refine ⟨δ ^ (-β), Real.rpow_pos_of_pos hδpos _, 3, fun q hq => ?_⟩
  have hq3R : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hlogq1 : (1:ℝ) < Real.log (q:ℝ) := by
    have h : Real.log (Real.exp 1) < Real.log (q:ℝ) :=
      Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le Real.exp_one_lt_three hq3R)
    rwa [Real.log_exp] at h
  have hlogq_nonneg : 0 ≤ Real.log (q:ℝ) := by linarith
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (q:ℝ)) := Real.log_nonneg (le_of_lt hlogq1)
  have hle1 : Real.log (Real.log (q:ℝ)) ≤ (Real.log (q:ℝ)) ^ δ / δ :=
    Real.log_le_rpow_div hlogq_nonneg hδpos
  have hmono : (Real.log (Real.log (q:ℝ))) ^ β ≤ ((Real.log (q:ℝ)) ^ δ / δ) ^ β :=
    Real.rpow_le_rpow hloglog_nonneg hle1 hβ
  have hsimp : ((Real.log (q:ℝ)) ^ δ / δ) ^ β
      = (Real.log (q:ℝ)) ^ (δ * β) * δ ^ (-β) := by
    rw [Real.div_rpow (Real.rpow_nonneg hlogq_nonneg δ) hδpos.le β,
        ← Real.rpow_mul hlogq_nonneg δ β, div_eq_mul_inv, ← Real.rpow_neg hδpos.le β]
  have hlogpow_le : (Real.log (q:ℝ)) ^ (δ * β) ≤ Real.log (q:ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt hlogq1) hδβ
    simpa [Real.rpow_one] using h
  calc (Real.log (Real.log (q:ℝ))) ^ β
      ≤ ((Real.log (q:ℝ)) ^ δ / δ) ^ β := hmono
    _ = (Real.log (q:ℝ)) ^ (δ * β) * δ ^ (-β) := hsimp
    _ ≤ Real.log (q:ℝ) * δ ^ (-β) :=
          mul_le_mul_of_nonneg_right hlogpow_le (Real.rpow_pos_of_pos hδpos _).le
    _ = δ ^ (-β) * Real.log (q:ℝ) := by ring

theorem main_arith (v w x : ℝ) (hw : 0 < w) (hv : 0 < v) (hvx : v < x) (hx : v + w + 1/3 < x)
    (k : ℕ) (hk : 3 ≤ k) (e : ℝ) (he : 0 < e)
    (hek : e + 1/(3*((k:ℝ))^2) < (x - v - w - 1/3)/(k:ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      Real.log (q:ℝ) * (Real.log (Real.log (q:ℝ))) ^ (x/3) * (1 + (v+w) * Real.log (q:ℝ))^3
        * (q:ℝ) ^ (1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ))
      ≤ K / Real.log (q:ℝ) := by
  have hkR : (0:ℝ) < (k:ℝ) := by
    have h3 : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkR
  have hxpos : 0 < x := lt_trans hv hvx
  set s : ℝ := 1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ) with hs
  have hsneg : s < 0 := by
    have hstep : (x - v - w - 1/3)/(k:ℝ) = (x - v - w)/(k:ℝ) - 1/(3*(k:ℝ)) := by
      rw [sub_div, show (1:ℝ)/3/(k:ℝ) = 1/(3*(k:ℝ)) by rw [div_div]]
    have hE : e + 1/(3*(k:ℝ)^2) < (x - v - w)/(k:ℝ) - 1/(3*(k:ℝ)) := by
      rw [← hstep]; exact hek
    rw [hs]; linarith
  set t : ℝ := -s with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have hst : s = -t := by rw [ht]; ring
  obtain ⟨C', hC'pos, q₀', hq₀'⟩ := exists_rpow_loglog_le_log_mul (x/3) (by linarith)
  obtain ⟨q₀'', hq₀''⟩ := exp_neg_mul_log_pow_le t 6 htpos (by norm_num)
  refine ⟨C' * (1+v+w)^3, mul_pos hC'pos (pow_pos (by linarith : (0:ℝ) < 1+v+w) 3),
    max (max q₀' q₀'') 3, ?_⟩
  intro q hq
  have hq' : q₀' ≤ q := le_trans (le_trans (le_max_left q₀' q₀'') (le_max_left _ 3)) hq
  have hq'' : q₀'' ≤ q := le_trans (le_trans (le_max_right q₀' q₀'') (le_max_left _ 3)) hq
  have hq3 : 3 ≤ q := le_trans (le_max_right (max q₀' q₀'') 3) hq
  have hq3R : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hlogq1 : (1:ℝ) < Real.log (q:ℝ) := by
    have h : Real.log (Real.exp 1) < Real.log (q:ℝ) :=
      Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le Real.exp_one_lt_three hq3R)
    rwa [Real.log_exp] at h
  have hLpos : (0:ℝ) < Real.log (q:ℝ) := lt_trans zero_lt_one hlogq1
  have hlogLnonneg : 0 ≤ Real.log (Real.log (q:ℝ)) := Real.log_nonneg (le_of_lt hlogq1)
  have hb : (Real.log (Real.log (q:ℝ))) ^ (x/3) ≤ C' * Real.log (q:ℝ) := hq₀' q hq'
  have hc : 1 + (v+w) * Real.log (q:ℝ) ≤ (1+v+w) * Real.log (q:ℝ) := by linarith
  have hCnonneg : (0:ℝ) ≤ 1 + (v+w) * Real.log (q:ℝ) := by
    have hp : 0 < (v+w) * Real.log (q:ℝ) := mul_pos (by linarith) hLpos
    linarith
  have hc3 : (1 + (v+w) * Real.log (q:ℝ))^3 ≤ ((1+v+w) * Real.log (q:ℝ))^3 :=
    pow_le_pow_left₀ hCnonneg hc 3
  have hBC : (Real.log (Real.log (q:ℝ))) ^ (x/3) * (1 + (v+w) * Real.log (q:ℝ))^3
      ≤ (C' * Real.log (q:ℝ)) * ((1+v+w) * Real.log (q:ℝ))^3 :=
    mul_le_mul hb hc3 (pow_nonneg hCnonneg 3) (mul_nonneg hC'pos.le hLpos.le)
  have hpoly : (Real.log (q:ℝ))^2 * (Real.log (Real.log (q:ℝ))) ^ (x/3)
        * (1 + (v+w) * Real.log (q:ℝ))^3
      ≤ (Real.log (q:ℝ))^2 * (C' * Real.log (q:ℝ)) * ((1+v+w) * Real.log (q:ℝ))^3 := by
    calc (Real.log (q:ℝ))^2 * (Real.log (Real.log (q:ℝ))) ^ (x/3)
          * (1 + (v+w) * Real.log (q:ℝ))^3
        = (Real.log (q:ℝ))^2
            * ((Real.log (Real.log (q:ℝ))) ^ (x/3) * (1 + (v+w) * Real.log (q:ℝ))^3) := by ring
      _ ≤ (Real.log (q:ℝ))^2 * ((C' * Real.log (q:ℝ)) * ((1+v+w) * Real.log (q:ℝ))^3) :=
            mul_le_mul_of_nonneg_left hBC (sq_nonneg _)
      _ = (Real.log (q:ℝ))^2 * (C' * Real.log (q:ℝ)) * ((1+v+w) * Real.log (q:ℝ))^3 := by ring
  have hdecay : (q:ℝ)^(-t) * (Real.log (q:ℝ))^6 ≤ 1 := by
    have h := hq₀'' q hq''
    simpa using h
  have hDnonneg : (0:ℝ) ≤ (q:ℝ)^(-t) := Real.rpow_nonneg (le_of_lt hqpos) _
  rw [hst, le_div_iff₀ hLpos]
  calc Real.log (q:ℝ) * (Real.log (Real.log (q:ℝ))) ^ (x/3)
        * (1 + (v+w) * Real.log (q:ℝ))^3 * (q:ℝ)^(-t) * Real.log (q:ℝ)
      = (Real.log (q:ℝ))^2 * (Real.log (Real.log (q:ℝ))) ^ (x/3)
          * (1 + (v+w) * Real.log (q:ℝ))^3 * (q:ℝ)^(-t) := by ring
    _ ≤ (Real.log (q:ℝ))^2 * (C' * Real.log (q:ℝ)) * ((1+v+w) * Real.log (q:ℝ))^3
          * (q:ℝ)^(-t) := mul_le_mul_of_nonneg_right hpoly hDnonneg
    _ = C' * (1+v+w)^3 * ((q:ℝ)^(-t) * (Real.log (q:ℝ))^6) := by ring
    _ ≤ C' * (1+v+w)^3 * 1 :=
          mul_le_mul_of_nonneg_left hdecay
            (mul_nonneg hC'pos.le (pow_nonneg (by linarith : (0:ℝ) ≤ 1+v+w) 3))
    _ = C' * (1+v+w)^3 := by ring

end Work.LinnikAreas.Density4
