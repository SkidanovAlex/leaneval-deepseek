import Mathlib
import Submission.Work.TMC16Core.Assembly.NrParamsDefs

/-!
# The numerical parameter inequalities, `s ≥ 2`

This is the `s ≥ 2` version of `Work.Assembly.nr_params` (which assumes `s ≥ 3`).
The only place `s ≥ 3` entered that proof was the bound `6 Q ≤ K + 1` (used to control
`log (4(K+1))`); with `s ≥ 2` we only get `4 Q ≤ K + 1`, which yields the slightly
weaker log-bound constant `5 (K+1) L / 5924` in place of `5 (K+1) L / 8886`.  All the
other estimates are unchanged, so the same assembly goes through.
-/

namespace Work.Assembly

open Work.TMC16Core.Assembly

set_option maxHeartbeats 1000000

/-- `log (4(K+1)) · Q ≤ 5 (K+1) (log Q + 1) / 4` for `4Q ≤ K+1`, `Q ≥ 1`, `K ≥ 40`. -/
private theorem log_bound_aux4 {Q : ℝ} {K : ℕ} (hQ : 1 ≤ Q) (hQK : 4 * Q ≤ (K : ℝ) + 1)
    (hK : 40 ≤ K) :
    Real.log (4 * ((K : ℝ) + 1)) * Q ≤ 5 * ((K : ℝ) + 1) * (Real.log Q + 1) / 4 := by
  have hQpos : (0:ℝ) < Q := by linarith
  have hKR : (40:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  set n : ℝ := (K:ℝ) + 1 with hn
  have hnpos : 0 < n := by rw [hn]; linarith
  set u : ℝ := Real.log (n/4) with hu
  have hn4pos : 0 < n/4 := by positivity
  have h4le : (4:ℝ) ≤ n/4 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    rw [hn]; linarith
  have hu0 : 0 ≤ u := by
    rw [hu]
    apply Real.log_nonneg
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    rw [hn]; linarith
  have hlogn : Real.log n ≤ 2 * u := by
    have hsplit : Real.log n = Real.log 4 + Real.log (n/4) := by
      rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (ne_of_gt hn4pos)]
      rw [mul_div_cancel₀ n (by norm_num : (4:ℝ) ≠ 0)]
    have hle : Real.log 4 ≤ Real.log (n/4) := Real.log_le_log (by norm_num) h4le
    rw [hsplit, hu]
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [h4]; linarith
  have hlog4n : Real.log (4 * n) = Real.log 4 + Real.log n :=
    Real.log_mul (by norm_num) (ne_of_gt hnpos)
  set t : ℝ := n / (4 * Q) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ (by positivity : (0:ℝ) < 4*Q)]
    rw [hn]; linarith [hQK]
  have hut : u = Real.log Q + Real.log t := by
    rw [hu, ht, hn]
    rw [← Real.log_mul (ne_of_gt hQpos) (by positivity : (((K:ℝ)+1)/(4*Q)) ≠ 0)]
    congr 1
    field_simp
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hut2 : u + 1 ≤ t * (Real.log Q + 1) := by
    rw [hut]; nlinarith [hlogt, hlogQ0, ht1]
  have hmain : Real.log (4 * n) ≤ 5 * n * (Real.log Q + 1) / (4 * Q) := by
    calc Real.log (4 * n) = Real.log 4 + Real.log n := hlog4n
      _ ≤ 2 + 2 * u := by linarith
      _ ≤ 5 * (u + 1) := by linarith
      _ ≤ 5 * (t * (Real.log Q + 1)) := by linarith
      _ = 5 * n * (Real.log Q + 1) / (4 * Q) := by rw [ht]; field_simp
  have h := mul_le_mul_of_nonneg_right hmain (le_of_lt hQpos)
  have hfin : Real.log (4 * n) * Q ≤ 5 * n * (Real.log Q + 1) / 4 := by
    have h' := h
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt hQpos)] at h'
    exact h'
  exact hfin

/-- `1481 (log Q + 1)/Q ≤ L` from the two hypotheses on `r`. -/
private theorem L_lower_aux {L r Q : ℝ} (hQ : 1 ≤ Q)
    (hrlow : 200 * (Real.log Q + 1) / Q ≤ r) (hrup : r ≤ L / 8 + L / 100) :
    1481 * (Real.log Q + 1) / Q ≤ L := by
  have hQpos : (0:ℝ) < Q := by linarith
  have hz : 0 ≤ Real.log Q + 1 := by have := Real.log_nonneg hQ; linarith
  have hstep : 200 * (Real.log Q + 1) / Q ≤ L / 8 + L / 100 := le_trans hrlow hrup
  have hmul : 200 * (Real.log Q + 1) ≤ (L / 8 + L / 100) * Q := by
    rw [div_le_iff₀ hQpos] at hstep; exact hstep
  rw [div_le_iff₀ hQpos]
  nlinarith [hmul, hz]

/-- The arithmetic inequality for the `A` branch, `K ≥ 40` (constant `5/5924`). -/
private theorem arith_K_aux4 {K : ℕ} (hK : 40 ≤ K) :
    5 / 5924 + (1 + (135 : ℝ) / 1000 * (K : ℝ)) / ((K : ℝ) + 1) + 2 / ((K : ℝ) + 1) ^ 2
      ≤ (99 : ℝ) / 100 * ((K : ℝ) + 1) / (6 * (K : ℝ)) - 1 / 100 := by
  rcases le_or_gt K 200 with h | h
  · interval_cases K <;> norm_num
  · have h200 : 200 ≤ K := by omega
    have hK200 : (200:ℝ) ≤ (K:ℝ) := by exact_mod_cast h200
    have hKpos : (0:ℝ) < (K:ℝ) := by linarith
    have h1 : (1 + (135:ℝ)/1000*(K:ℝ))/((K:ℝ)+1) ≤ 135/1000 + 1/201 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < (K:ℝ)+1)]
      have h3 : (1:ℝ) ≤ ((K:ℝ)+1)/201 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 201)]; linarith
      nlinarith [h3]
    have h2 : 2/((K:ℝ)+1)^2 ≤ 2/201^2 := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ((K:ℝ)+1)^2)
        (by norm_num : (0:ℝ) < 201^2)]
      nlinarith
    have hRHS : (155:ℝ)/1000 ≤ (99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) - 1/100 := by
      rw [le_sub_iff_add_le]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 6*(K:ℝ))]
      have h3 : (1:ℝ) ≤ ((K:ℝ)+1)/(K:ℝ) := by rw [le_div_iff₀ hKpos]; linarith
      nlinarith [h3]
    linarith

/-- The arithmetic inequality for the `B` branch, `K ≥ 40`. -/
private theorem arith_KB_aux {K : ℕ} (hK : 40 ≤ K) :
    (99 : ℝ) / 100 * (1 / 40 + 1 / (K : ℝ)) - 1 / 100 + 1 / ((K : ℝ) + 1) ^ 2
      ≤ (99 : ℝ) / 100 * ((K : ℝ) + 1) / (6 * (K : ℝ)) - 1 / 100 := by
  have hK40 : (40:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have hKpos : (0:ℝ) < (K:ℝ) := by linarith
  have hA1 : (99:ℝ)/100 * (1/40 + 1/(K:ℝ)) ≤ (99:ℝ)/100 * (1/40 + 1/40) := by
    have h : 1/(K:ℝ) ≤ 1/40 := by
      rw [div_le_div_iff₀ hKpos (by norm_num : (0:ℝ) < 40)]; linarith
    linarith
  have hA2 : 1/((K:ℝ)+1)^2 ≤ 1/1681 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ((K:ℝ)+1)^2) (by norm_num : (0:ℝ) < 1681)]
    nlinarith
  have hRHS : (165:ℝ)/1000 ≤ (99:ℝ)/100 * ((K:ℝ)+1) / (6*(K:ℝ)) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 6*(K:ℝ))]
    have h : 1 ≤ ((K:ℝ)+1)/(K:ℝ) := by rw [le_div_iff₀ hKpos]; linarith
    nlinarith [h]
  linarith

theorem nr_params_ge2_s2 {L r Q : ℝ} {s K b' : ℕ}
    (hL : 0 < L) (hQ : 1 ≤ Q) (hs : 2 ≤ s) (hK40 : 40 ≤ K)
    (hK : (K : ℝ) = 2 * (s : ℝ) * Q - 1)
    (hb' : b' = (s + 2) / 3)
    (hrlow : 200 * (Real.log Q + 1) / Q ≤ r)
    (hrup : r ≤ L / 8 + L / 100) :
    1 / 40 ≤ Work.TMC16Core.Assembly.nrDelta L r K ∧
    Work.TMC16Core.Assembly.nrDelta L r K ≤ 1 / 2 ∧
    1 ≤ (K : ℝ) * (Work.TMC16Core.Assembly.nrDelta L r K - 1 / 40) ∧
    Work.TMC16Core.Assembly.nrEpsA L r K =
      Work.TMC16Core.Assembly.csing L * Work.TMC16Core.Assembly.nrDelta L r K -
        Work.TMC16Core.Assembly.eps2 L ∧
    r < Work.TMC16Core.Assembly.nrEpsA L r K ∧
    Work.TMC16Core.Assembly.eps2 L < Work.TMC16Core.Assembly.nrEpsA L r K ∧
    Real.log (4 * ((K : ℝ) + 1)) + L + (K : ℝ) * r <
      ((K : ℝ) + 1) * Work.TMC16Core.Assembly.nrEpsA L r K ∧
    Work.TMC16Core.Assembly.nrDelta L r K ≤ (b' : ℝ) * Q / (K : ℝ) ∧
    (L + Work.TMC16Core.Assembly.eps2 L) * ((3 : ℝ) * (K : ℝ) / 4) +
        (L / 4) * ((K : ℝ) / 4 - 1) ≤
      ((K : ℝ) + 1) * (L - Work.TMC16Core.Assembly.nrEpsA L r K) := by
  have hQpos : (0:ℝ) < Q := by linarith
  have hK40R : (40:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK40
  have hKpos : (0:ℝ) < (K:ℝ) := by linarith
  have hK1pos : (0:ℝ) < (K:ℝ) + 1 := by linarith
  have hK1nonneg : (0:ℝ) ≤ (K:ℝ) + 1 := le_of_lt hK1pos
  have hsR : (2:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hsRpos : (0:ℝ) < (s:ℝ) := by linarith
  have hsQ : 2 * (s:ℝ) * Q = (K:ℝ) + 1 := by linarith
  have hQK : 4 * Q ≤ (K:ℝ) + 1 := by
    have h1 : 4 * Q = 2 * ((K:ℝ)+1)/(s:ℝ) := by rw [← hsQ]; field_simp; ring
    rw [h1, div_le_iff₀ hsRpos]
    nlinarith [hsR, hsQ]
  have hlogQ1 : 0 < Real.log Q + 1 := by have := Real.log_nonneg hQ; linarith
  have hLlow : 1481 * (Real.log Q + 1) / Q ≤ L := L_lower_aux hQ hrlow hrup
  have hmul := log_bound_aux4 hQ hQK hK40
  have hlognum : Real.log (4 * ((K:ℝ)+1)) ≤ 5 * ((K:ℝ)+1) * L / 5924 := by
    have hLQ : 1481 * (Real.log Q + 1) ≤ L * Q := by
      rw [div_le_iff₀ hQpos] at hLlow; exact hLlow
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 5924)]
    nlinarith [hmul, hLQ, hQpos]
  have hrle : r ≤ (135:ℝ)/1000 * L := by linarith
  have hAub : (Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r)/((K:ℝ)+1) + 2*L/((K:ℝ)+1)^2
      ≤ ((99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) - 1/100)*L := by
    have hnum : Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r
        ≤ L*(5*((K:ℝ)+1)/5924 + 1 + (135:ℝ)/1000*(K:ℝ)) := by
      have h1 : (K:ℝ)*r ≤ (K:ℝ)*((135:ℝ)/1000*L) :=
        mul_le_mul_of_nonneg_left hrle (le_of_lt hKpos)
      nlinarith [hlognum, h1]
    have hdiv : (Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r)/((K:ℝ)+1)
        ≤ L*(5*((K:ℝ)+1)/5924 + 1 + (135:ℝ)/1000*(K:ℝ))/((K:ℝ)+1) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hK1pos)
    have hsplit : L*(5*((K:ℝ)+1)/5924 + 1 + (135:ℝ)/1000*(K:ℝ))/((K:ℝ)+1)
          + 2*L/((K:ℝ)+1)^2
        = L*(5/5924 + (1 + (135:ℝ)/1000*(K:ℝ))/((K:ℝ)+1) + 2/((K:ℝ)+1)^2) := by
      field_simp
      ring
    have harith := arith_K_aux4 hK40
    calc (Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r)/((K:ℝ)+1) + 2*L/((K:ℝ)+1)^2
        ≤ L*(5*((K:ℝ)+1)/5924 + 1 + (135:ℝ)/1000*(K:ℝ))/((K:ℝ)+1)
            + 2*L/((K:ℝ)+1)^2 := by linarith [hdiv]
      _ = L*(5/5924 + (1 + (135:ℝ)/1000*(K:ℝ))/((K:ℝ)+1) + 2/((K:ℝ)+1)^2) := hsplit
      _ ≤ L*((99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) - 1/100) :=
          mul_le_mul_of_nonneg_left harith (le_of_lt hL)
      _ = ((99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) - 1/100)*L := by ring
  have hBub : csing L*(1/40 + 1/(K:ℝ)) - eps2 L + L/((K:ℝ)+1)^2
      ≤ ((99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) - 1/100)*L := by
    have harith := arith_KB_aux hK40
    have hmul' := mul_le_mul_of_nonneg_left harith (le_of_lt hL)
    have hEq : csing L*(1/40 + 1/(K:ℝ)) - eps2 L + L/((K:ℝ)+1)^2
        = L*((99:ℝ)/100*(1/40 + 1/(K:ℝ)) - 1/100 + 1/((K:ℝ)+1)^2) := by
      simp only [csing, eps2]; ring
    rw [hEq]
    exact le_of_le_of_eq hmul' (mul_comm _ _)
  have hBge : csing L*(1/40 + 1/(K:ℝ)) - eps2 L + L/((K:ℝ)+1)^2 ≤ nrEpsA L r K := by
    rw [nrEpsA]; exact le_max_right _ _
  have hAlow : (Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r)/((K:ℝ)+1) + 2*L/((K:ℝ)+1)^2
      ≤ nrEpsA L r K := by rw [nrEpsA]; exact le_max_left _ _
  have hnrEpsA_le : nrEpsA L r K ≤ ((99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) - 1/100)*L := by
    rw [nrEpsA]; exact max_le hAub hBub
  have hXnn : (0:ℝ) ≤ (99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) := by positivity
  have hXLnn : (0:ℝ) ≤ (99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ))*L := by positivity
  have hnrEpsA_le' : nrEpsA L r K ≤ (99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ))*L - L/100 := by
    have h := hnrEpsA_le
    rw [sub_mul] at h
    linarith
  have hcs_eq : csing L = (99:ℝ)/100*L := by simp only [csing]; ring
  have heps_eq : eps2 L = L/100 := by simp only [eps2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nrDelta, le_div_iff₀ (csing_pos hL)]
    have hp : (0:ℝ) ≤ 1/(K:ℝ) := by positivity
    have hcs : (0:ℝ) ≤ csing L := le_of_lt (csing_pos hL)
    have hp2 : (0:ℝ) ≤ L/((K:ℝ)+1)^2 := by positivity
    nlinarith [hBge, hp, hcs, hp2]
  · have h1 : ((K:ℝ)+1)/(6*(K:ℝ)) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 6*(K:ℝ))]
      nlinarith [hKpos]
    have hkey : ((K:ℝ)+1)/(6*(K:ℝ)) * ((99:ℝ)/100*L) = (99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ))*L := by
      ring
    have h2 : nrDelta L r K ≤ ((K:ℝ)+1)/(6*(K:ℝ)) := by
      rw [nrDelta, div_le_iff₀ (csing_pos hL)]
      rw [hcs_eq, heps_eq, hkey]
      linarith [hnrEpsA_le']
    linarith
  · have hdx : (1:ℝ)/40 + 1/(K:ℝ) ≤ nrDelta L r K := by
      rw [nrDelta, le_div_iff₀ (csing_pos hL)]
      have hp2 : (0:ℝ) < L/((K:ℝ)+1)^2 := by positivity
      nlinarith [hBge, hp2]
    have hKinv : (K:ℝ) * (1/(K:ℝ)) = 1 := by
      rw [mul_one_div, div_self (ne_of_gt hKpos)]
    nlinarith [hdx, hKpos, hKinv]
  · exact (nrDelta_spec hL K).symm
  · have hsplit : (Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r)/((K:ℝ)+1) + 2*L/((K:ℝ)+1)^2
        = (Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r + 2*L/((K:ℝ)+1))/((K:ℝ)+1) := by
      field_simp
    have hlt : r < (Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r + 2*L/((K:ℝ)+1))/((K:ℝ)+1) := by
      rw [lt_div_iff₀ hK1pos]
      have hlog0 : 0 ≤ Real.log (4*((K:ℝ)+1)) := Real.log_nonneg (by linarith)
      have h2L : 0 < 2*L/((K:ℝ)+1) := by positivity
      nlinarith [hrle, hL, hlog0, hKpos, h2L]
    rw [← hsplit] at hlt
    exact lt_of_lt_of_le hlt hAlow
  · have hp : (0:ℝ) ≤ 1/(K:ℝ) := by positivity
    have hp2 : (0:ℝ) < L/((K:ℝ)+1)^2 := by positivity
    have hBge' := hBge
    rw [hcs_eq, heps_eq] at hBge'
    rw [heps_eq]
    nlinarith [hBge', hp, hp2, hL]
  · have hmul2 := mul_le_mul_of_nonneg_left hAlow hK1nonneg
    have heq : ((K:ℝ)+1)*((Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r)/((K:ℝ)+1)
          + 2*L/((K:ℝ)+1)^2)
        = Real.log (4*((K:ℝ)+1)) + L + (K:ℝ)*r + 2*L/((K:ℝ)+1) := by
      field_simp
    rw [heq] at hmul2
    have h2L : 0 < 2*L/((K:ℝ)+1) := by positivity
    linarith
  · have hsb : s ≤ 3*b' := by omega
    have hsbR : (s:ℝ) ≤ 3*(b':ℝ) := by exact_mod_cast hsb
    have hbQ : ((K:ℝ)+1)/6 ≤ (b':ℝ)*Q := by nlinarith [hsbR, hsQ, hQpos]
    have hfrac : ((K:ℝ)+1)/(6*(K:ℝ)) ≤ (b':ℝ)*Q/(K:ℝ) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 6*(K:ℝ)) hKpos]
      nlinarith [hbQ, hKpos]
    have hkey : ((K:ℝ)+1)/(6*(K:ℝ)) * ((99:ℝ)/100*L) = (99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ))*L := by
      ring
    have hdelta : nrDelta L r K ≤ ((K:ℝ)+1)/(6*(K:ℝ)) := by
      rw [nrDelta, div_le_iff₀ (csing_pos hL)]
      rw [hcs_eq, heps_eq, hkey]
      linarith [hnrEpsA_le']
    exact le_trans hdelta hfrac
  · have hpsi1 : (84:ℝ)/100 ≤ 1 - ((99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) - 1/100) := by
      have h : (99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) ≤ 17/100 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 6*(K:ℝ))]
        nlinarith [hKpos, hK40R]
      linarith
    have hLnr : (1 - ((99:ℝ)/100*((K:ℝ)+1)/(6*(K:ℝ)) - 1/100))*L ≤ L - nrEpsA L r K := by
      nlinarith [hnrEpsA_le, hL]
    have hlhs : (L + eps2 L)*(3*(K:ℝ)/4) + (L/4)*((K:ℝ)/4 - 1)
        ≤ (84:ℝ)/100*L*((K:ℝ)+1) := by
      rw [heps_eq]
      nlinarith [hL, hKpos]
    have hfin : (84:ℝ)/100*L*((K:ℝ)+1) ≤ ((K:ℝ)+1)*(L - nrEpsA L r K) := by
      have h1 : (84:ℝ)/100*L ≤ L - nrEpsA L r K := by nlinarith [hLnr, hpsi1, hL]
      have h2 : (84:ℝ)/100*L*((K:ℝ)+1) ≤ (L - nrEpsA L r K)*((K:ℝ)+1) :=
        mul_le_mul_of_nonneg_right h1 hK1nonneg
      exact le_of_le_of_eq h2 (by ring)
    linarith

end Work.Assembly
