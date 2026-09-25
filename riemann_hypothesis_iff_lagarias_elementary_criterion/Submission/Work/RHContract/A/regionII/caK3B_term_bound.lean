import Mathlib
import Submission.Work.RHContract.A.regionII.caK3B_defs
import Submission.Work.RHContract.A.ca_margin_lower

namespace Work.RHContract.A.regionII

/-- Local helper: for `p ≥ 2` and `e = ⌊log_p ξ⌋` the tail term obeys the "geometric-tail"
bound `p^{-(e+1)}/((e+1)(1-1/p)) ≤ (1/ξ)·(1/(e+1))·(1+1/(p-1))`. -/
lemma caYterm_le_inv_xi (ξ : ℝ) (hξ0 : 0 < ξ) {p e : ℕ} (hp1 : 1 < (p:ℝ))
    (hpowR : ξ < (p:ℝ) ^ (((e:ℝ) + 1))) :
    (p:ℝ) ^ (-(((e:ℝ) + 1))) / (((e:ℝ) + 1) * (1 - 1/(p:ℝ)))
      ≤ (1/ξ) * (1/((e:ℝ) + 1)) * (1 + 1/((p:ℝ)-1)) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hkR : 0 < ((e:ℝ) + 1) := by positivity
  have hinv : (p:ℝ) ^ (-(((e:ℝ) + 1))) ≤ 1/ξ := by
    rw [Real.rpow_neg (le_of_lt hp0), inv_eq_one_div]
    exact le_of_lt (one_div_lt_one_div_of_lt hξ0 hpowR)
  have hden : 0 < (((e:ℝ) + 1) * (1 - 1/(p:ℝ))) := by
    refine mul_pos hkR ?_
    rw [sub_pos, div_lt_one hp0]; linarith
  have hstep := div_le_div_of_nonneg_right hinv hden.le
  refine le_trans hstep ?_
  have heq : (1/ξ)/(((e:ℝ) + 1) * (1 - 1/(p:ℝ)))
      = (1/ξ) * (1/((e:ℝ) + 1)) * (1 + 1/((p:ℝ)-1)) := by
    have hpne : (p:ℝ) - 1 ≠ 0 := by linarith
    have hkne : ((e:ℝ) + 1) ≠ 0 := ne_of_gt hkR
    field_simp
    ring
  rw [heq]

theorem caK3B_term_bound (ε : ℝ) (hε : 0 < ε) (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hcaC : kcc (Work.RHPlan.caXi ε : ℝ) ≤ Work.RHContract.Margin.caC ε)
    {p : ℕ} (hp : p ∈ (Nat.primesLE ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊).filter
        (fun q => Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊)) :
    Work.RHContract.A.caK3term ε p ≤ (1/(Work.RHPlan.caXi ε : ℝ)) *
      (1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ))) *
      (1 - kB (Work.RHPlan.caXi ε : ℝ) + 1/((p:ℝ)-1)) := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ : (Work.RHPlan.caXi ε : ℝ) = ξ := hξdef.symm
  have hξ1e5 : 100000 ≤ ξ := by rw [← hξ]; exact hlo
  have hξ1 : 1 < ξ := by linarith
  have hξ0 : 0 < ξ := by linarith
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξ1
  have hp_mem1 : p ∈ Nat.primesLE ⌊Real.sqrt ξ⌋₊ := (Finset.mem_filter.mp hp).1
  have hprime : Nat.Prime p := (Nat.mem_primesLE.mp hp_mem1).2
  have hp2 : 2 ≤ p := hprime.two_le
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hprime.one_lt
  have hlogp : 0 < Real.log (p:ℝ) := Real.log_pos hp1
  have hcaC' : kcc ξ ≤ Work.RHContract.Margin.caC ε := hcaC
  have he : Work.RHContract.Margin.caExpFloor ε p = Nat.log p (Work.RHPlan.caXi ε) :=
    Work.RHContract.A.caExpFloor_eq_log ε p
  have hkR : 0 < ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) := by positivity
  have hpowN : Work.RHPlan.caXi ε < p ^ (Work.RHContract.Margin.caExpFloor ε p + 1) := by
    rw [he]
    exact Nat.lt_pow_succ_log_self hprime.one_lt (Work.RHPlan.caXi ε)
  have hpow : ξ < (p:ℝ) ^ (Work.RHContract.Margin.caExpFloor ε p + 1) := by
    have h2 : ((p ^ (Work.RHContract.Margin.caExpFloor ε p + 1) : ℕ) : ℝ)
        = (p:ℝ) ^ (Work.RHContract.Margin.caExpFloor ε p + 1) := by push_cast; ring
    have h3 : ((Work.RHPlan.caXi ε : ℕ) : ℝ)
        < (p:ℝ) ^ (Work.RHContract.Margin.caExpFloor ε p + 1) := by
      rw [← h2]; exact_mod_cast hpowN
    rw [← hξ]
    exact h3
  have hpowR : ξ < (p:ℝ) ^ (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)) := by
    have hc2 : (p:ℝ) ^ (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
        = (p:ℝ) ^ (Work.RHContract.Margin.caExpFloor ε p + 1) := by
      rw [show (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
          = ((Work.RHContract.Margin.caExpFloor ε p + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [hc2]; exact hpow
  have hloglt : Real.log ξ
      < ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * Real.log (p:ℝ) := by
    have h1 : Real.log ξ
        < Real.log ((p:ℝ) ^ (Work.RHContract.Margin.caExpFloor ε p + 1)) :=
      Real.log_lt_log hξ0 hpow
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogdiv : Real.log ξ / ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)
      < Real.log (p:ℝ) := by
    rw [div_lt_iff₀ hkR]; linarith
  have hA := caYterm_le_inv_xi ξ hξ0 hp1 hpowR
  have hkcc0 : 0 ≤ kcc ξ := by
    rw [kcc]
    refine div_nonneg ?_ ?_
    · rw [sub_nonneg, div_le_one (Real.sqrt_pos.mpr hξ0)]
      have h3 : (3:ℝ) ≤ Real.sqrt ξ := by
        rw [Real.le_sqrt (by norm_num) (le_of_lt hξ0)]; linarith
      linarith
    · have h2 : 0 ≤ ξ ^ (3/4:ℝ) := Real.rpow_nonneg hξ0.le _
      have h4 : 1 ≤ ξ + 0.45*ξ^(3/4:ℝ) + 2 := by linarith
      have h5 : 0 < ξ + 0.45*ξ^(3/4:ℝ) + 2 := by linarith
      exact mul_nonneg (le_of_lt h5) (Real.log_nonneg h4)
  have hgain : kB ξ / (ξ * ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
      ≤ Work.RHContract.Margin.caC ε * Real.log (p:ℝ) := by
    have h1 : kB ξ / (ξ * ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
        = kcc ξ * (Real.log ξ / ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)) := by
      rw [kB]
      field_simp
    rw [h1]
    calc kcc ξ * (Real.log ξ / ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
        ≤ kcc ξ * Real.log (p:ℝ) := mul_le_mul_of_nonneg_left hlogdiv.le hkcc0
      _ ≤ Work.RHContract.Margin.caC ε * Real.log (p:ℝ) :=
          mul_le_mul_of_nonneg_right hcaC' hlogp.le
  have hmul : (1/ξ) * (1/((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
        * (1 + 1/((p:ℝ)-1))
      - kB ξ / (ξ * ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
      = (1/ξ) * (1/((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
        * (1 - kB ξ + 1/((p:ℝ)-1)) := by
    have hpne : (p:ℝ) - 1 ≠ 0 := by linarith
    have hkne : ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) ≠ 0 := ne_of_gt hkR
    field_simp
    ring
  have hT : caYterm ε p - caXterm ε p ≤
      (1/ξ) * (1/((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
        * (1 - kB ξ + 1/((p:ℝ)-1)) := by
    rw [caYterm, caXterm]
    linarith [hA, hgain, hmul]
  have hRHSnn : 0 ≤ (1/ξ) * (1/((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
      * (1 - kB ξ + 1/((p:ℝ)-1)) := by
    have hkB1 : kB ξ ≤ 1 := kB_le_one ξ hξ1e5
    have h3 : 0 ≤ 1 - kB ξ + 1/((p:ℝ)-1) := by
      have h4 : 0 ≤ 1/((p:ℝ)-1) := by
        have : 0 < (p:ℝ)-1 := by linarith
        positivity
      linarith
    have h2 : 0 ≤ (1/ξ) * (1/((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)) := by
      positivity
    exact mul_nonneg h2 h3
  have hK3 : caK3term ε p ≤ (1/ξ) * (1/((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
      * (1 - kB ξ + 1/((p:ℝ)-1)) := by
    rw [caK3term]
    exact max_le hRHSnn hT
  have hkp : ((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ)
      = ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) := by
    rw [← he]
    push_cast
    ring
  calc caK3term ε p
      ≤ (1/ξ) * (1/((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))
          * (1 - kB ξ + 1/((p:ℝ)-1)) := hK3
    _ = (1/(Work.RHPlan.caXi ε : ℝ))
          * (1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ)))
          * (1 - kB (Work.RHPlan.caXi ε : ℝ) + 1/((p:ℝ)-1)) := by
        rw [hξ, hkp]

end Work.RHContract.A.regionII
