import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs
import Submission.Work.Analysis.Primes.sum_primes_le_third
import Submission.Work.RHContract.A.regionII.netLossNumeric
import Submission.Work.RHContract.A.regionII.netLossSumBound
import Submission.Work.RHContract.A.regionII.netLossLogPf
import Submission.Work.RHContract.A.regionII.netLossCBounds

/-!
# `Work.RHContract.A.regionII.netLossBound`

The boundary loss of the `k = 2` level of Region II is controlled.  For
`ξ = ξ(ε) = caXi ε ∈ [10^5, 10^8)`, `s = √ξ`, `L = log ξ`, `m = ⌊s⌋₊`, `Pf = ⌊(115/100)s⌋₊`
and `c = caC ε` we show

`Σ_{√ξ < p ≤ Pf} (c log p - 1/(2p(p-1))) ≥ - netY L / (s-4)`,

the lower bound for the *negative* part of `Net₂`.  The argument:

* per prime `p > m` the summand equals `log p · (c - h p)` with `h p = 1/(2p(p-1)log p)`, so
  it is at worst `- log(Pf)·max (B/(p(p-1)) - c) 0` where `B = 1/(2 log(m+1))`;
* the sum over primes `m < p ≤ Pf` is at most a third of the sum over all integers in
  `[m-2, Pf]` (`sum_primes_le_third`), using that primes `> 3` occupy two of every six
  residue classes mod 6;
* the integer sum of the positive parts is at most `(√(B/(m-3)) - √(c(m-3)))²`
  (`netLossSumBound`, a discrete telescoping/AM-GM estimate);
* that square is at most `0.0045/(L(s-4))` (`netLossNumeric`, with the bounds
  `0.9015/(L+0.0941) ≤ cξ ≤ 1/(0.9(L-0.105361))` of `netLossCBounds` and the two bounds on
  `B` coming from `log s ≤ log(m+1) ≤ log s + 1/s`);
* finally `log(Pf) ≤ L/2 + 0.15` (`netLossLogPf`) turns `(1/3)log(Pf)·0.0045/(L(s-4))` into
  `netY L/(s-4)`.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.RHContract.A.regionII

noncomputable section

private lemma sqrt_bridge (B c M : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c) (hM : 0 < M) :
    (Real.sqrt (B/M) - Real.sqrt (c*M))^2 = (Real.sqrt B - M*Real.sqrt c)^2 / M := by
  have hsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt (le_of_lt hM)
  rw [Real.sqrt_div hB, Real.sqrt_mul hc, sub_sq, sub_sq, div_pow, hsq]
  rw [mul_pow, hsq, Real.sq_sqrt hB, Real.sq_sqrt hc]
  field_simp
  rw [Real.sq_sqrt hc]

private lemma netF_ge_neg (m Pf p : ℕ) (B c : ℝ)
    (hB : 1/(2*Real.log ((m:ℝ)+1)) ≤ B) (hm1 : 1 ≤ m)
    (hp : Nat.Prime p) (hmp : m < p) (hpPf : p ≤ Pf) (hPf1 : 1 ≤ Pf) :
    -(Real.log (Pf:ℝ)) * max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0 ≤ netF c p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 < p := hp.one_lt
  have hp1r : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp1
  have hlogp : 0 < Real.log (p:ℝ) := Real.log_pos hp1r
  have hlogpnn : 0 ≤ Real.log (p:ℝ) := le_of_lt hlogp
  have hlogPfnn : 0 ≤ Real.log (Pf:ℝ) := Real.log_nonneg (by exact_mod_cast hPf1)
  have hmp' : (m:ℝ) + 1 ≤ (p:ℝ) := by exact_mod_cast (by omega : m + 1 ≤ p)
  have hlogle : Real.log ((m:ℝ) + 1) ≤ Real.log (p:ℝ) :=
    Real.log_le_log (by positivity) hmp'
  have hpPf' : (p:ℝ) ≤ (Pf:ℝ) := by exact_mod_cast hpPf
  have hlogpPf : Real.log (p:ℝ) ≤ Real.log (Pf:ℝ) := Real.log_le_log (by linarith) hpPf'
  set h : ℝ := 1/(2*(p:ℝ)*((p:ℝ)-1)*Real.log (p:ℝ)) with hhdef
  have hnetF : netF c p = Real.log (p:ℝ) * (c - h) := by
    rw [netF, hhdef]
    have hlp : Real.log (p:ℝ) ≠ 0 := ne_of_gt hlogp
    field_simp
  have hden_pos : 0 < (p:ℝ) * ((p:ℝ) - 1) := by
    have : (1:ℝ) ≤ (p:ℝ) := by linarith
    nlinarith
  have hle : h ≤ B / ((p:ℝ) * ((p:ℝ) - 1)) := by
    have hm1r : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    have hmlogpos : 0 < Real.log ((m:ℝ)+1) := Real.log_pos (by linarith)
    have hstep : (1:ℝ)/(2*Real.log (p:ℝ)) ≤ B := by
      have h2 : 0 < 2*Real.log (p:ℝ) := by linarith
      have h3 : 0 < 2*Real.log ((m:ℝ)+1) := by linarith
      calc (1:ℝ)/(2*Real.log (p:ℝ)) ≤ 1/(2*Real.log ((m:ℝ)+1)) :=
            one_div_le_one_div_of_le h3 (by linarith)
        _ ≤ B := hB
    calc h = ((1:ℝ)/(2*Real.log (p:ℝ))) / ((p:ℝ) * ((p:ℝ) - 1)) := by
            rw [hhdef]; field_simp
      _ ≤ B / ((p:ℝ) * ((p:ℝ) - 1)) := div_le_div_of_nonneg_right hstep (le_of_lt hden_pos)
  have hmax : max (h - c) 0 ≤ max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0 :=
    max_le_max (by linarith) le_rfl
  have hkey : Real.log (p:ℝ) * (h - c) ≤ Real.log (Pf:ℝ) * max (h - c) 0 := by
    have h1 : Real.log (p:ℝ) * (h - c) ≤ Real.log (p:ℝ) * max (h - c) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hlogpnn
    have h2 : Real.log (p:ℝ) * max (h - c) 0 ≤ Real.log (Pf:ℝ) * max (h - c) 0 :=
      mul_le_mul_of_nonneg_right hlogpPf (le_max_right _ _)
    linarith
  have hkey2 : Real.log (Pf:ℝ) * max (h - c) 0 ≤ Real.log (Pf:ℝ) * max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0 :=
    mul_le_mul_of_nonneg_left hmax hlogPfnn
  rw [hnetF]
  have : Real.log (p:ℝ) * (c - h) = -(Real.log (p:ℝ) * (h - c)) := by ring
  rw [this]
  linarith

theorem netLossBound (ε : ℝ) (hε : 0 < ε) (hlo : (100000 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ))
    (hhi : (Work.RHPlan.caXi ε : ℝ) < (10 : ℝ) ^ 8) :
    -(netY (Real.log (Work.RHPlan.caXi ε : ℝ)) / (Real.sqrt (Work.RHPlan.caXi ε : ℝ) - 4))
      ≤ ∑ p ∈ (netS ε).filter (fun q => q ≤ netPf (Work.RHPlan.caXi ε : ℝ)),
          netF (Work.RHContract.Margin.caC ε) p := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  set s : ℝ := Real.sqrt ξ with hsdef
  set L : ℝ := Real.log ξ with hLdef
  set c : ℝ := Work.RHContract.Margin.caC ε with hcdef
  set m : ℕ := netM ξ with hmdef
  set Pf : ℕ := netPf ξ with hPfdef
  set B : ℝ := 1 / (2 * Real.log ((m : ℝ) + 1)) with hBdef
  set γ : ℝ := c * ξ with hγdef
  set M : ℝ := (m : ℝ) - 3 with hMdef
  set A : Finset ℕ := (netS ε).filter (fun q => q ≤ Pf) with hAdef
  have hξ0 : 0 < ξ := by rw [hξdef]; linarith
  have hξ1e5 : (100000 : ℝ) ≤ ξ := by rw [hξdef]; exact hlo
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hξ0
  have hs2 : s ^ 2 = ξ := by rw [hsdef]; exact Real.sq_sqrt hξ0.le
  have hs3162 : (316.2 : ℝ) ≤ s := by
    rw [hsdef]
    have h1 : (316.2 : ℝ) ≤ Real.sqrt 100000 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    exact le_trans h1 (Real.sqrt_le_sqrt hξ1e5)
  have hs316 : (316 : ℝ) ≤ s := by linarith
  have hs4 : 0 < s - 4 := by linarith
  have hL115 : (115 / 10 : ℝ) ≤ L := by
    rw [hLdef]
    have h1 : Real.log (100000 : ℝ) ≤ Real.log ξ := Real.log_le_log (by norm_num) hξ1e5
    have h2 : Real.log (100000 : ℝ) = 5 * Real.log 10 := by
      rw [show (100000 : ℝ) = 10 ^ 5 by norm_num, Real.log_pow]; norm_num
    have h3 : (2.3025850926 : ℝ) ≤ Real.log 10 := by
      have hm : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
        rw [show (10:ℝ) = 2*5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    linarith
  have hL0 : 0 < L := by linarith
  have hLs : L = 2 * Real.log s := by
    rw [hLdef, ← hs2, Real.log_pow]; norm_num
  have hm_hi : (m : ℝ) ≤ s := by rw [hmdef, hsdef]; exact Nat.floor_le (Real.sqrt_nonneg ξ)
  have hm_lo : s - 1 ≤ (m : ℝ) := by
    have h : s < (m : ℝ) + 1 := by
      rw [hmdef, hsdef]
      exact Nat.lt_floor_add_one (Real.sqrt ξ)
    linarith
  have hm316 : 316 ≤ m := by
    rw [hmdef]
    exact Nat.le_floor (le_trans (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (Real.sqrt_le_sqrt hξ1e5))
  have hm4 : 4 ≤ m := by omega
  have hm6 : 6 ≤ m := by omega
  have hPf_ge : m - 2 ≤ Pf := by
    rw [hPfdef]
    apply Nat.le_floor
    have hcast : ((m - 2 : ℕ) : ℝ) = (m:ℝ) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ m by omega)]; norm_num
    rw [hcast]
    nlinarith [hm_hi, hs316]
  have hPf1 : 1 ≤ Pf := by omega
  have hlogPfnn : 0 ≤ Real.log (Pf:ℝ) := Real.log_nonneg (by exact_mod_cast hPf1)
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hBpos : 0 < B := by
    rw [hBdef]
    have : 0 < Real.log ((m:ℝ) + 1) := Real.log_pos (by linarith)
    positivity
  have hγlo : (9015 : ℝ)/10000/(L + 941/10000) ≤ γ := by
    have h := (netLossCBounds ε hε hlo).1
    simpa only [hγdef, hcdef, hLdef, hξdef] using h
  have hγhi : γ ≤ 1/((9/10 : ℝ)*(L - 105361/1000000)) := by
    have h := (netLossCBounds ε hε hlo).2
    simpa only [hγdef, hcdef, hLdef, hξdef] using h
  have hγpos : 0 < γ := lt_of_lt_of_le (by apply div_pos (by norm_num); linarith) hγlo
  have hc0 : 0 < c := by
    have h : 0 < c * ξ := by rw [← hγdef]; exact hγpos
    exact pos_of_mul_pos_left h hξ0.le
  have hm1pos : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hlogm1pos : 0 < Real.log ((m:ℝ) + 1) := Real.log_pos (by linarith)
  have hBhi : B ≤ 1/L := by
    have hs_le_m1 : s ≤ (m:ℝ) + 1 := by
      rw [hmdef]
      have h := Nat.lt_floor_add_one s
      linarith
    have hlogle : Real.log s ≤ Real.log ((m:ℝ)+1) := Real.log_le_log hs0 hs_le_m1
    have h2 : 0 < 2 * Real.log s := by linarith
    calc B = 1/(2 * Real.log ((m:ℝ)+1)) := hBdef
      _ ≤ 1/(2 * Real.log s) := one_div_le_one_div_of_le h2 (by linarith)
      _ = 1/L := by rw [hLs]
  have hBlo : 1/(L + 6329/1000000) ≤ B := by
    have hm1_le : (m:ℝ)+1 ≤ s + 1 := by linarith
    have hlog1 : Real.log ((m:ℝ)+1) ≤ Real.log s + 1/s := by
      have hspos : 0 < s + 1 := by linarith
      calc Real.log ((m:ℝ)+1) ≤ Real.log (s+1) := Real.log_le_log (by linarith) hm1_le
        _ = Real.log s + Real.log (1 + 1/s) := by
              rw [show s + 1 = s * (1 + 1/s) by field_simp]
              rw [Real.log_mul (ne_of_gt hs0) (by positivity)]
        _ ≤ Real.log s + 1/s := by
              have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/s by positivity)
              linarith
    have h2s : 2 * (1/s) ≤ 6329/1000000 := by
      rw [show (2:ℝ) * (1/s) = 2/s by ring]
      rw [div_le_iff₀ hs0]; nlinarith [hs3162]
    have hkey : 2 * Real.log ((m:ℝ)+1) ≤ L + 6329/1000000 := by
      have ha : 2 * Real.log ((m:ℝ)+1) ≤ 2 * (Real.log s + 1/s) := by linarith [hlog1]
      have hb : 2 * (Real.log s + 1/s) ≤ 2 * Real.log s + 6329/1000000 := by linarith [h2s]
      rw [hLs]; linarith
    calc 1/(L + 6329/1000000) ≤ 1/(2 * Real.log ((m:ℝ)+1)) :=
          one_div_le_one_div_of_le (by linarith) hkey
      _ = B := hBdef.symm
  have hMlo : s - 4 ≤ M := by rw [hMdef]; linarith
  have hMhi : M ≤ s - 3 := by rw [hMdef]; linarith
  have hMpos : 0 < M := by
    rw [hMdef]
    have : (3:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 3 < m)
    linarith
  -- pointwise and sum chain
  have h1 : -(Real.log (Pf:ℝ)) * (∑ p ∈ A, max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0)
      ≤ ∑ p ∈ A, netF c p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpS : p ∈ netS ε := (Finset.mem_filter.mp hp).1
    have hpPf : p ≤ Pf := (Finset.mem_filter.mp hp).2
    have hp' : p ∈ (Nat.primesLE (Work.RHContract.Margin.caXi2 ε)).filter (fun q => netM ξ < q) := hpS
    have hprime : Nat.Prime p := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp').1).2
    have hm_lt : m < p := by rw [hmdef]; exact (Finset.mem_filter.mp hp').2
    exact netF_ge_neg m Pf p B c (le_of_eq hBdef.symm) (by omega : 1 ≤ m) hprime hm_lt hpPf hPf1
  have hAsub : A ⊆ (Finset.Icc (m + 1) Pf).filter Nat.Prime := by
    intro p hp
    have hpS : p ∈ netS ε := (Finset.mem_filter.mp hp).1
    have hpPf : p ≤ Pf := (Finset.mem_filter.mp hp).2
    have hp' : p ∈ (Nat.primesLE (Work.RHContract.Margin.caXi2 ε)).filter (fun q => netM ξ < q) := hpS
    have hprime : Nat.Prime p := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp').1).2
    have hm_lt : m < p := by rw [hmdef]; exact (Finset.mem_filter.mp hp').2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hpPf⟩, hprime⟩
  have h2 : ∑ p ∈ A, max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0
      ≤ ∑ p ∈ (Finset.Icc (m + 1) Pf).filter Nat.Prime,
          max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun x _ _ => le_max_right _ _)
  have hgm : ∀ a b : ℕ, m - 2 ≤ a → a ≤ b → b ≤ Pf →
      max (B / ((b:ℝ) * ((b:ℝ) - 1)) - c) 0 ≤ max (B / ((a:ℝ) * ((a:ℝ) - 1)) - c) 0 := by
    intro a b ha hab hbPf
    apply max_le_max _ le_rfl
    have ha4 : 4 ≤ a := by omega
    have ha4r : (4:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha4
    have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
    have hden_a : 0 < (a:ℝ) * ((a:ℝ) - 1) := by nlinarith
    have hprod : (a:ℝ) * ((a:ℝ) - 1) ≤ (b:ℝ) * ((b:ℝ) - 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hab') (by linarith : (0:ℝ) ≤ (a:ℝ) + (b:ℝ) - 1)]
    have hinv : ((b:ℝ) * ((b:ℝ) - 1))⁻¹ ≤ ((a:ℝ) * ((a:ℝ) - 1))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hden_a hprod
    have hstep : B / ((b:ℝ) * ((b:ℝ) - 1)) ≤ B / ((a:ℝ) * ((a:ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hinv (le_of_lt hBpos)
    linarith
  have h3 : ∑ p ∈ (Finset.Icc (m + 1) Pf).filter Nat.Prime,
        max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0
      ≤ (1/3) * ∑ n ∈ Finset.Icc (m - 2) Pf, max (B / ((n:ℝ) * ((n:ℝ) - 1)) - c) 0 :=
    Work.Analysis.Primes.sum_primes_le_third m Pf hm6
      (fun n => max (B / ((n:ℝ) * ((n:ℝ) - 1)) - c) 0)
      (fun n => le_max_right _ _) hgm
  have h4 : ∑ n ∈ Finset.Icc (m - 2) Pf, max (B / ((n:ℝ) * ((n:ℝ) - 1)) - c) 0
      ≤ (Real.sqrt (B / ((m:ℝ) - 3)) - Real.sqrt (c * ((m:ℝ) - 3))) ^ 2 :=
    netLossSumBound m Pf B c hBpos (le_of_lt hc0) hm4 hPf_ge
  have hnum := netLossNumeric s L B γ M hs3162 hL115 hMlo hMhi hBlo hBhi hγlo hγhi
  have hMeq : M = (m:ℝ) - 3 := hMdef
  have hγs : Real.sqrt γ = Real.sqrt c * s := by
    rw [hγdef, hsdef, Real.sqrt_mul (le_of_lt hc0)]
  have hbridge : (Real.sqrt (B / ((m:ℝ) - 3)) - Real.sqrt (c * ((m:ℝ) - 3))) ^ 2
      = (Real.sqrt B - M / s * Real.sqrt γ) ^ 2 / M := by
    rw [← hMeq, hγs]
    have hsne : s ≠ 0 := ne_of_gt hs0
    have hsimp : M / s * (Real.sqrt c * s) = M * Real.sqrt c := by field_simp
    rw [hsimp]
    exact sqrt_bridge B c M (le_of_lt hBpos) (le_of_lt hc0) hMpos
  have hZA : ∑ p ∈ A, max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0
      ≤ (1/3) * (45/10000/(L*(s-4))) := by
    calc ∑ p ∈ A, max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0
        ≤ ∑ p ∈ (Finset.Icc (m + 1) Pf).filter Nat.Prime, max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0 := h2
      _ ≤ (1/3) * ∑ n ∈ Finset.Icc (m - 2) Pf, max (B / ((n:ℝ) * ((n:ℝ) - 1)) - c) 0 := h3
      _ ≤ (1/3) * (Real.sqrt (B / ((m:ℝ) - 3)) - Real.sqrt (c * ((m:ℝ) - 3))) ^ 2 :=
            mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = (1/3) * ((Real.sqrt B - M / s * Real.sqrt γ) ^ 2 / M) := by rw [hbridge]
      _ ≤ (1/3) * ((45/10000/L) / M) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact div_le_div_of_nonneg_right hnum (le_of_lt hMpos)
      _ ≤ (1/3) * (45/10000/(L*(s-4))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            rw [div_le_div_iff₀ hMpos (by positivity)]
            have hLne : L ≠ 0 := ne_of_gt hL0
            have : (45/10000/L) * (L*(s-4)) = 45/10000*(s-4) := by field_simp
            rw [this]
            nlinarith [hMlo]
  have hZ : (0:ℝ) ≤ (1/3) * (45/10000/(L*(s-4))) := by positivity
  have hlogPf_le : Real.log (Pf:ℝ) ≤ L/2 + 15/100 := by
    have h := netLossLogPf ξ hξ0 hξ1e5
    simpa only [hPfdef, hLdef] using h
  have hZnn : (0:ℝ) ≤ (1/3) * (45/10000/(L*(s-4))) := hZ
  have hlast : -((1/3) * (L/2 + 15/100) * ((45/10000)/L) / (s-4))
      = -((L/2 + 15/100) * ((1/3) * (45/10000/(L*(s-4))))) := by
    congr 1
    have hLne : L ≠ 0 := ne_of_gt hL0
    have hs4ne : s - 4 ≠ 0 := ne_of_gt hs4
    field_simp
  calc -(netY L / (s - 4))
      = -((1/3) * (L/2 + 15/100) * ((45/10000)/L) / (s-4)) := by rw [netY]
    _ = -((L/2 + 15/100) * ((1/3) * (45/10000/(L*(s-4))))) := hlast
    _ ≤ -(Real.log (Pf:ℝ)) * ((1/3) * (45/10000/(L*(s-4)))) := by
          have h1' : -(L/2 + 15/100) ≤ -(Real.log (Pf:ℝ)) := by linarith
          simpa only [neg_mul] using mul_le_mul_of_nonneg_right h1' hZ
    _ ≤ -(Real.log (Pf:ℝ)) * (∑ p ∈ A, max (B / ((p:ℝ) * ((p:ℝ) - 1)) - c) 0) := by
          apply mul_le_mul_of_nonpos_left hZA
          linarith
    _ ≤ ∑ p ∈ A, netF c p := h1

end

end Work.RHContract.A.regionII
