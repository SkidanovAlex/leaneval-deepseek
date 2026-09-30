import Mathlib
import Submission.Work.BMF.liouville.vmvt_stechkin_defs
import Submission.Work.BMF.liouville.stechF_step_core
import Submission.Work.BMF.vmvt_setup
import Submission.Work.BMF.vmvt_M_bounds
import Submission.Work.BMF.vmvt_step_ineq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp step of the Vinogradov–Linnik iteration

This is `Work.BMF.vmvt_step_ineq` with the constant `Ac C₀ k r` replaced by the sharp
`stechF k r = exp (stechK·k·r·(k+r)·(1+log k))`; the per-step arithmetic is `stechF_step_core`
together with the growth identity `stechF_growth`.
-/

open scoped BigOperators

namespace Work.BMF.liouville

open Work.BMF

set_option maxHeartbeats 2000000

/-- `2·(4k⁴)^{k(r+1)} ≤ stechF k (r+1)`, hence `(4k⁴)^{k(r+1)} ≤ (1/2)·stechF k (r+1)`,
for `k ≥ 2`, `r ≥ 1`. -/
lemma stechF_term_one (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    (4*(k:ℝ)^4)^(k*(r+1)) ≤ (1/2) * stechF k (r+1) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hlogk0 : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have hlogk2 : Real.log 2 ≤ Real.log (k:ℝ) := Real.log_le_log (by norm_num) hk2
  have hlog4 : Real.log 4 ≤ 2 * Real.log (k:ℝ) := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    linarith only [hlogk2]
  have hlogbig : Real.log (4*(k:ℝ)^4) ≤ 6 * Real.log (k:ℝ) := by
    rw [Real.log_mul (by norm_num) (show (k:ℝ)^4 ≠ 0 by positivity), Real.log_pow]
    norm_num
    linarith only [hlog4]
  have hR : (((r+1:ℕ)):ℝ) = (r:ℝ) + 1 := by push_cast; ring
  have hkr1 : (1:ℝ) ≤ ((k*(r+1) : ℕ) : ℝ) := by
    have h1 : (1:ℕ) ≤ k*(r+1) := by nlinarith only [hk1, hr]
    exact_mod_cast h1
  have hkr0 : (0:ℝ) ≤ ((k*(r+1) : ℕ) : ℝ) := le_trans zero_le_one hkr1
  have hkR4 : (4:ℝ) ≤ (k:ℝ) + (((r+1:ℕ)):ℝ) := by rw [hR]; linarith only [hk2, hr1]
  have hK : 8 ≤ stechK := eight_le_stechK
  have hexp : Real.log 2 + ((k*(r+1) : ℕ) : ℝ) * Real.log (4*(k:ℝ)^4)
      ≤ stechK * (k:ℝ) * (((r+1:ℕ)):ℝ) * ((k:ℝ) + (((r+1:ℕ)):ℝ)) * (1 + Real.log (k:ℝ)) := by
    have hA : Real.log 2 + ((k*(r+1) : ℕ) : ℝ) * Real.log (4*(k:ℝ)^4)
        ≤ (1 + 6 * ((k*(r+1) : ℕ) : ℝ)) * Real.log (k:ℝ) := by
      have h1 : ((k*(r+1) : ℕ) : ℝ) * Real.log (4*(k:ℝ)^4)
          ≤ ((k*(r+1) : ℕ) : ℝ) * (6 * Real.log (k:ℝ)) :=
        mul_le_mul_of_nonneg_left hlogbig hkr0
      linarith only [h1, hlogk2, hlogk0]
    have hB : (1 + 6 * ((k*(r+1) : ℕ) : ℝ)) ≤ 7 * ((k*(r+1) : ℕ) : ℝ) := by
      linarith only [hkr1]
    have hB' : (1 + 6 * ((k*(r+1) : ℕ) : ℝ)) * Real.log (k:ℝ)
        ≤ 7 * ((k*(r+1) : ℕ) : ℝ) * Real.log (k:ℝ) :=
      mul_le_mul_of_nonneg_right hB hlogk0
    have h7 : (7:ℝ) ≤ stechK * ((k:ℝ) + (((r+1:ℕ)):ℝ)) := by nlinarith only [hK, hkR4]
    have hC1 : 7 * ((k*(r+1) : ℕ) : ℝ)
        ≤ (stechK * ((k:ℝ) + (((r+1:ℕ)):ℝ))) * ((k*(r+1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right h7 hkr0
    have hC2 : 7 * ((k*(r+1) : ℕ) : ℝ) * Real.log (k:ℝ)
        ≤ (stechK * ((k:ℝ) + (((r+1:ℕ)):ℝ))) * ((k*(r+1) : ℕ) : ℝ) * Real.log (k:ℝ) :=
      mul_le_mul_of_nonneg_right hC1 hlogk0
    have hz2 : (0:ℝ) ≤ (stechK * ((k:ℝ) + (((r+1:ℕ)):ℝ))) * ((k*(r+1) : ℕ) : ℝ) := by
      have h1 : (0:ℝ) < (k:ℝ) + (((r+1:ℕ)):ℝ) := by linarith only [hkR4]
      have h2 : (0:ℝ) < stechK := lt_of_lt_of_le (by norm_num) hK
      positivity
    have hC3 : (stechK * ((k:ℝ) + (((r+1:ℕ)):ℝ))) * ((k*(r+1) : ℕ) : ℝ) * Real.log (k:ℝ)
        ≤ stechK * (k:ℝ) * (((r+1:ℕ)):ℝ) * ((k:ℝ) + (((r+1:ℕ)):ℝ)) * (1 + Real.log (k:ℝ)) := by
      have hkeq : (stechK * ((k:ℝ) + (((r+1:ℕ)):ℝ))) * ((k*(r+1) : ℕ) : ℝ)
          = stechK * (k:ℝ) * (((r+1:ℕ)):ℝ) * ((k:ℝ) + (((r+1:ℕ)):ℝ)) := by
        push_cast
        ring
      rw [hkeq]
      have hz3 : (0:ℝ) ≤ stechK * (k:ℝ) * (((r+1:ℕ)):ℝ) * ((k:ℝ) + (((r+1:ℕ)):ℝ)) := by
        have h2 : (0:ℝ) < stechK := lt_of_lt_of_le (by norm_num) hK
        have h3 : (0:ℝ) < (k:ℝ) := by linarith only [hk2]
        have h4 : (0:ℝ) < (((r+1:ℕ)):ℝ) := by positivity
        have h5 : (0:ℝ) < (k:ℝ) + (((r+1:ℕ)):ℝ) := by linarith only [hkR4]
        positivity
      nlinarith only [hz3, hlogk0]
    linarith only [hA, hB', hC2, hC3]
  have key : 2 * (4*(k:ℝ)^4)^(k*(r+1)) ≤ stechF k (r+1) := by
    have h2 : (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    have h4 : (4*(k:ℝ)^4)^(k*(r+1))
        = Real.exp (((k*(r+1) : ℕ) : ℝ) * Real.log (4*(k:ℝ)^4)) := by
      rw [← Real.exp_log (show (0:ℝ) < (4*(k:ℝ)^4)^(k*(r+1)) by positivity), Real.log_pow]
    rw [h2, h4, stechF, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp
  linarith only [key]

theorem vmvt_step_ineq_sharp (k r Q : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) (hQ : 1 ≤ Q) :
    (4*(k:ℝ)^4)^(k*(r+1)) + 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
      * (((max (2*(max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊+1))) ⌈pC*(k:ℝ)^3*Real.log k⌉₊ : ℕ)) : ℝ)^(2*k*r+k*(k-1)/2)
      * (Q:ℝ)^k * (stechF k r * (1 + (Q:ℝ)/((max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊+1) : ℕ) : ℝ))^(th k r))
    ≤ stechF k (r+1) * (Q:ℝ)^(th k (r+1)) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  have hkRne : (k:ℝ) ≠ 0 := ne_of_gt hkR
  have hpC : 0 < pC := pC_pos
  set s : ℝ := (Q:ℝ) with hsdef
  set R : ℝ := s^(1/(k:ℝ)) with hRdef
  set M : ℕ := max k (⌈R⌉₊+1) with hMdef
  set Y : ℕ := max (2*M) ⌈pC*(k:ℝ)^3*Real.log k⌉₊ with hYdef
  set E : ℕ := 2*k*r+k*(k-1)/2 with hEdef
  have hs1 : (1:ℝ) ≤ s := by rw [hsdef]; exact_mod_cast hQ
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hRs : R = s^(1/(k:ℝ)) := hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact Real.rpow_pos_of_pos hs0 _
  have hR0 : 0 ≤ R := le_of_lt hRpos
  have hlogk0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hfact0 : (0:ℝ) < ((k.factorial:ℕ):ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hMb := vmvt_M_bounds k Q hk hQ
  rw [← hsdef, ← hRdef, ← hMdef] at hMb
  obtain ⟨hQleM, hMQ⟩ := hMb
  have hYb := Y_bound_aux k Q hk hQ
  rw [← hsdef, ← hRdef, ← hMdef, ← hYdef] at hYb
  have hMk : (k:ℝ) ≤ (M:ℝ) := by
    rw [hMdef, Nat.cast_max]
    exact le_max_left _ _
  have hMpos : (0:ℝ) < (M:ℝ) := lt_of_lt_of_le hkR hMk
  have hsM0 : 0 ≤ s/(M:ℝ) := div_nonneg (le_of_lt hs0) (le_of_lt hMpos)
  have h1sM : 0 ≤ 1 + s/(M:ℝ) := by linarith
  have hAexp0 : 0 ≤ pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7 := by
    have h1 : 0 ≤ pC*(k:ℝ)^3*Real.log k :=
      mul_nonneg (mul_nonneg (le_of_lt hpC) (by positivity)) hlogk0
    linarith
  have hexp : (E:ℝ)/(k:ℝ) + (k:ℝ) + (1-1/(k:ℝ))*(th k r) = th k (r+1) := by
    have h1 := Estep_div_k_aux k r hk1
    rw [← hEdef] at h1
    have h2 := th_key k r hk1
    nlinarith only [h1, h2]
  -- the zero-th order term
  have hT1 : (4*(k:ℝ)^4)^(k*(r+1)) ≤ (1/2) * (stechF k (r+1) * s^(th k (r+1))) := by
    have h1 := stechF_term_one k r hk hr
    have h2 : 1 ≤ s^(th k (r+1)) :=
      Real.one_le_rpow hs1 (le_of_lt (th_pos_aux k (r+1) hk (by omega)))
    have h3 : 0 < stechF k (r+1) := stechF_pos k (r+1)
    nlinarith only [h1, h2, h3]
  -- the coefficient
  have hcore := stechF_step_core k r hk hr
  have hcoef : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
        * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
        * (2:ℝ)^(th k r) * stechF k r ≤ (1/2) * stechF k (r+1) := by
    have hAr : 0 ≤ stechF k r := stechF_nonneg k r
    have hA0 : 0 < pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7 := by
      have h2 : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
      have h3 : 0 ≤ pC*(k:ℝ)^3*Real.log (k:ℝ) := by positivity
      linarith
    have hprod0 : 0 < 8 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6
        * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E * (2:ℝ)^(th k r) := by
      have h1 : (0:ℝ) < ((k.factorial:ℕ):ℝ) := by exact_mod_cast Nat.factorial_pos k
      have h2 : (0:ℝ) < (k:ℝ)^6 := by positivity
      have h3 : (0:ℝ) < (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E := pow_pos hA0 E
      have h4 : (0:ℝ) < (2:ℝ)^(th k r) := Real.rpow_pos_of_pos (by norm_num) _
      have h5 : (0:ℝ) < 8 := by norm_num
      positivity
    have h8bound : 8 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6
        * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E * (2:ℝ)^(th k r)
        ≤ Real.exp (stechK * (k:ℝ) * (2*(r:ℝ) + (k:ℝ) + 1) * (1 + Real.log (k:ℝ))) := by
      rw [← Real.exp_log hprod0]
      exact Real.exp_le_exp.mpr hcore
    have h1 := mul_le_mul_of_nonneg_right h8bound hAr
    rw [stechF_growth k r]
    nlinarith only [h1, hAr]
  -- the main term
  have hYpow : ((Y:ℕ):ℝ)^E
      ≤ (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) :=
    pow_le_pow_left₀ (by positivity) hYb E
  have hthr0 : 0 ≤ th k r := le_of_lt (th_pos_aux k r hk hr)
  have hbasestep : (1 + s/(M:ℝ))^(th k r) ≤ (2*s^(1-1/(k:ℝ)))^(th k r) :=
    Real.rpow_le_rpow h1sM hMQ hthr0
  have hAcr0 : 0 ≤ stechF k r := stechF_nonneg k r
  have h4k0 : 0 ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 := by positivity
  have hsp0 : 0 ≤ s^k := pow_nonneg (le_of_lt hs0) k
  have h1s0 : 0 ≤ (1 + s/(M:ℝ))^(th k r) := Real.rpow_nonneg h1sM _
  have h2s0 : 0 ≤ 2*s^(1-1/(k:ℝ)) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hs0) _)
  have h2sp0 : 0 ≤ (2*s^(1-1/(k:ℝ)))^(th k r) := Real.rpow_nonneg h2s0 _
  have hAR0 : 0 ≤ (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R := mul_nonneg hAexp0 hR0
  have hARp0 : 0 ≤ ((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E := pow_nonneg hAR0 E
  have hYT0 : 0 ≤ ((Y:ℕ):ℝ)^E := pow_nonneg (by positivity) E
  have hstepA : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * ((Y:ℕ):ℝ)^E * s^k
        * (stechF k r * (1 + s/(M:ℝ))^(th k r))
      ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
        * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k
        * (stechF k r * (2*s^(1-1/(k:ℝ)))^(th k r)) := by
    refine mul_le_mul ?_ ?_ (mul_nonneg hAcr0 h1s0) ?_
    · have hx : ((Y:ℕ):ℝ)^E * s^k
          ≤ (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k :=
        mul_le_mul_of_nonneg_right hYpow hsp0
      have hx2 : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * (((Y:ℕ):ℝ)^E * s^k)
          ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
            * ((((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k) :=
        mul_le_mul_of_nonneg_left hx h4k0
      calc 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * ((Y:ℕ):ℝ)^E * s^k
          = 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * (((Y:ℕ):ℝ)^E * s^k) := by ring
        _ ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
            * ((((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k) := hx2
        _ = 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
            * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k := by ring
    · exact mul_le_mul_of_nonneg_left hbasestep hAcr0
    · have hX : (0:ℝ) ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 := h4k0
      have hY0 : (0:ℝ) ≤ ((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E := hARp0
      have hZ0 : (0:ℝ) ≤ s^k := hsp0
      have h1' : (0:ℝ) ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) := mul_nonneg hX hY0
      have h2' : (0:ℝ) ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k := mul_nonneg h1' hZ0
      simpa only [mul_assoc] using h2'
  have hRE : R^E = s^((E:ℝ)/(k:ℝ)) := by
    rw [hRs, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hs0)]
    congr 1
    field_simp
    try ring
  have hmulpow : (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E)
      = (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E * s^((E:ℝ)/(k:ℝ)) := by
    rw [mul_pow, hRE]
  have h2E : (2*s^(1-1/(k:ℝ)))^(th k r)
      = (2:ℝ)^(th k r) * s^((1-1/(k:ℝ))*(th k r)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (le_of_lt hs0) _),
        ← Real.rpow_mul (le_of_lt hs0)]
  have hsk : s^k = s^((k:ℝ)) := (Real.rpow_natCast s k).symm
  have hstepB : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
        * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k
        * (stechF k r * (2*s^(1-1/(k:ℝ)))^(th k r))
      = (4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
          * (2:ℝ)^(th k r) * stechF k r)
        * (s^((E:ℝ)/(k:ℝ)) * s^((k:ℝ)) * s^((1-1/(k:ℝ))*(th k r))) := by
    rw [hmulpow, h2E, hsk]
    ring
  have hstepB' : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
        * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k
        * (stechF k r * (2*s^(1-1/(k:ℝ)))^(th k r))
      = (4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
          * (2:ℝ)^(th k r) * stechF k r) * s^(th k (r+1)) := by
    rw [hstepB, rpow_three s hs0 ((E:ℝ)/(k:ℝ)) ((k:ℝ)) ((1-1/(k:ℝ))*(th k r)), hexp]
  have hstepC : (4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
          * (2:ℝ)^(th k r) * stechF k r) * s^(th k (r+1))
      ≤ (1/2) * stechF k (r+1) * s^(th k (r+1)) :=
    mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (le_of_lt hs0) _)
  have hT2 : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * ((Y:ℕ):ℝ)^E * s^k
        * (stechF k r * (1 + s/(M:ℝ))^(th k r))
      ≤ (1/2) * stechF k (r+1) * s^(th k (r+1)) := by
    calc 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * ((Y:ℕ):ℝ)^E * s^k
          * (stechF k r * (1 + s/(M:ℝ))^(th k r))
        ≤ _ := hstepA
      _ = _ := hstepB'
      _ ≤ _ := hstepC
  have hsum := add_le_add hT1 hT2
  linarith only [hsum]


end Work.BMF.liouville
