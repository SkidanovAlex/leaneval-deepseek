import Submission.ASP.S39

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- `Ã(x) ≥ 1`. -/
lemma one_le_Acount_atil (x : ℕ) (hx : 1 ≤ x) : (1 : ℝ) ≤ Acount (atil FIa) (x : ℝ) := by
  rw [Acount, Nat.floor_natCast]
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hx⟩
  have h := Finset.single_le_sum (f := fun n => atil FIa n)
    (fun i _ => atil_nonneg FIa_nonneg i) hmem
  have h1 : (1 : ℝ) ≤ atil FIa 1 := by
    rw [atil]
    have h2 : ((ArithmeticFunction.moebius 1 : ℝ)) ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_apply_one]; norm_num
    rw [h2, one_mul]
    show (1 : ℝ) ≤ (Submission.an 1 : ℝ)
    exact_mod_cast an_one_pos'
  linarith

/-- The pure algebra of the §9 Hölder step: the accumulated constant `c₁^{3/4}c₂^{1/4}` is beaten
by the spare power `L^{1/4}` of the logarithm. -/
lemma holder_algebra {b lam L c1 c2 At : ℝ} (hAt : 0 < At) (hL : 0 < L)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hKey : c1 ^ ((3 : ℝ) / 4) * c2 ^ ((1 : ℝ) / 4)
      * L ^ (b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ)) ≤ 1) :
    (c1 * At * L ^ b) ^ ((3 : ℝ) / 4) * (c2 * At * L ^ (-lam)) ^ ((1 : ℝ) / 4)
      ≤ At * L ^ (-(3 : ℝ)) := by
  have hLnn : (0 : ℝ) ≤ L := le_of_lt hL
  have hAtnn : (0 : ℝ) ≤ At := le_of_lt hAt
  have hLp1 : (0 : ℝ) ≤ L ^ b := Real.rpow_nonneg hLnn _
  have hLp2 : (0 : ℝ) ≤ L ^ (-lam) := Real.rpow_nonneg hLnn _
  have hF1 : (c1 * At * L ^ b) ^ ((3 : ℝ) / 4)
      = c1 ^ ((3 : ℝ) / 4) * At ^ ((3 : ℝ) / 4) * L ^ (b * ((3 : ℝ) / 4)) := by
    have hX : (0 : ℝ) ≤ At * L ^ b := mul_nonneg hAtnn hLp1
    calc (c1 * At * L ^ b) ^ ((3 : ℝ) / 4) = (c1 * (At * L ^ b)) ^ ((3 : ℝ) / 4) := by
          congr 1; ring
      _ = c1 ^ ((3 : ℝ) / 4) * (At * L ^ b) ^ ((3 : ℝ) / 4) := Real.mul_rpow hc1 hX
      _ = c1 ^ ((3 : ℝ) / 4) * (At ^ ((3 : ℝ) / 4) * (L ^ b) ^ ((3 : ℝ) / 4)) := by
          rw [Real.mul_rpow hAtnn hLp1]
      _ = c1 ^ ((3 : ℝ) / 4) * At ^ ((3 : ℝ) / 4) * L ^ (b * ((3 : ℝ) / 4)) := by
          rw [← Real.rpow_mul hLnn]; ring
  have hF2 : (c2 * At * L ^ (-lam)) ^ ((1 : ℝ) / 4)
      = c2 ^ ((1 : ℝ) / 4) * At ^ ((1 : ℝ) / 4) * L ^ ((-lam) * ((1 : ℝ) / 4)) := by
    have hX : (0 : ℝ) ≤ At * L ^ (-lam) := mul_nonneg hAtnn hLp2
    calc (c2 * At * L ^ (-lam)) ^ ((1 : ℝ) / 4) = (c2 * (At * L ^ (-lam))) ^ ((1 : ℝ) / 4) := by
          congr 1; ring
      _ = c2 ^ ((1 : ℝ) / 4) * (At * L ^ (-lam)) ^ ((1 : ℝ) / 4) := Real.mul_rpow hc2 hX
      _ = c2 ^ ((1 : ℝ) / 4) * (At ^ ((1 : ℝ) / 4) * (L ^ (-lam)) ^ ((1 : ℝ) / 4)) := by
          rw [Real.mul_rpow hAtnn hLp2]
      _ = c2 ^ ((1 : ℝ) / 4) * At ^ ((1 : ℝ) / 4) * L ^ ((-lam) * ((1 : ℝ) / 4)) := by
          rw [← Real.rpow_mul hLnn]; ring
  have hAt12 : At ^ ((3 : ℝ) / 4) * At ^ ((1 : ℝ) / 4) = At := by
    rw [← Real.rpow_add hAt,
      show ((3 : ℝ) / 4) + ((1 : ℝ) / 4) = (1 : ℝ) by norm_num, Real.rpow_one]
  have hC : c1 ^ ((3 : ℝ) / 4) * c2 ^ ((1 : ℝ) / 4)
      ≤ L ^ (-(b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ))) := by
    have hpos : (0 : ℝ) < L ^ (b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ)) :=
      Real.rpow_pos_of_pos hL _
    have h := (le_div_iff₀ hpos).mpr hKey
    have h2 : 1 / L ^ (b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ))
        = L ^ (-(b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ))) := by
      rw [one_div, Real.rpow_neg hLnn]
    linarith [h, h2]
  rw [hF1, hF2]
  calc c1 ^ ((3 : ℝ) / 4) * At ^ ((3 : ℝ) / 4) * L ^ (b * ((3 : ℝ) / 4))
        * (c2 ^ ((1 : ℝ) / 4) * At ^ ((1 : ℝ) / 4) * L ^ ((-lam) * ((1 : ℝ) / 4)))
      = (c1 ^ ((3 : ℝ) / 4) * c2 ^ ((1 : ℝ) / 4)) * (At ^ ((3 : ℝ) / 4) * At ^ ((1 : ℝ) / 4))
        * (L ^ (b * ((3 : ℝ) / 4)) * L ^ ((-lam) * ((1 : ℝ) / 4))) := by ring
    _ ≤ L ^ (-(b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ))) * At
        * L ^ (b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4)) := by
        rw [hAt12, ← Real.rpow_add hL]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hAtnn)
          (Real.rpow_nonneg hLnn _)
    _ = At * (L ^ (-(b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ)))
        * L ^ (b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4))) := by ring
    _ ≤ At * L ^ (-(3 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hAtnn
        rw [← Real.rpow_add hL]
        congr 1; ring

/-- The base reduction + absorb of the §9 Hölder step. -/
lemma holder_absorb {b lam Cc C23 CR As At L : ℝ}
    (hC23 : 0 < C23) (hCR : 0 < CR) (hCc : 0 < Cc)
    (hL : 0 < L) (hAt : 0 < At) (hAs : 0 ≤ As) (hAsle : As ≤ Cc * At)
    (hKey : (C23 * (Cc + 1)) ^ ((3 : ℝ) / 4) * (CR * Cc) ^ ((1 : ℝ) / 4)
      * L ^ (b * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ)) ≤ 1) :
    (C23 * (As + At) * L ^ b) ^ ((3 : ℝ) / 4)
      * (CR * As * L ^ (-lam)) ^ ((1 : ℝ) / 4) ≤ At * L ^ (-(3 : ℝ)) := by
  have hLnn : (0 : ℝ) ≤ L := le_of_lt hL
  have hsum : As + At ≤ (Cc + 1) * At := by
    have : Cc * At + At = (Cc + 1) * At := by ring
    linarith
  have hP : C23 * (As + At) * L ^ b ≤ (C23 * (Cc + 1)) * At * L ^ b := by
    calc C23 * (As + At) * L ^ b = C23 * ((As + At) * L ^ b) := by ring
      _ ≤ C23 * (((Cc + 1) * At) * L ^ b) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hLnn _)) hC23.le
      _ = (C23 * (Cc + 1)) * At * L ^ b := by ring
  have hQ : CR * As * L ^ (-lam) ≤ (CR * Cc) * At * L ^ (-lam) := by
    calc CR * As * L ^ (-lam) = CR * (As * L ^ (-lam)) := by ring
      _ ≤ CR * ((Cc * At) * L ^ (-lam)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hAsle (Real.rpow_nonneg hLnn _)) hCR.le
      _ = (CR * Cc) * At * L ^ (-lam) := by ring
  have hPnn : (0 : ℝ) ≤ C23 * (As + At) * L ^ b :=
    mul_nonneg (mul_nonneg hC23.le (by linarith)) (Real.rpow_nonneg hLnn _)
  have hQnn : (0 : ℝ) ≤ CR * As * L ^ (-lam) :=
    mul_nonneg (mul_nonneg hCR.le hAs) (Real.rpow_nonneg hLnn _)
  have hPnn' : (0 : ℝ) ≤ (C23 * (Cc + 1)) * At * L ^ b :=
    mul_nonneg (mul_nonneg (mul_nonneg hC23.le (by linarith)) (le_of_lt hAt))
      (Real.rpow_nonneg hLnn _)
  refine le_trans (mul_le_mul (Real.rpow_le_rpow hPnn hP (by norm_num))
    (Real.rpow_le_rpow hQnn hQ (by norm_num))
    (Real.rpow_nonneg hQnn _) (Real.rpow_nonneg hPnn' _)) ?_
  have hc1nn : (0 : ℝ) ≤ C23 * (Cc + 1) := mul_nonneg hC23.le (by linarith)
  have hc2nn : (0 : ℝ) ≤ CR * Cc := mul_nonneg hCR.le hCc.le
  exact holder_algebra hAt hL hc1nn hc2nn hKey

/-- **(R′) for `ã`** (for `m ≥ Rcut x`). -/
theorem FI_RemainderSum_atil_le :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ, Submission.Rcut x ≤ m → m ≤ x →
      RemainderSum (rtildeFull FIr FIg FIgtil FIa) (Submission.Rcut x) m
        ≤ Acount (atil FIa) (x : ℝ) * (Real.log x) ^ (-(3 : ℝ)) := by
  obtain ⟨C23, B23, X23r, hC23, h23⟩ := Atil_tau_pow_remainder_le
  set lam : ℝ := 3 * B23 + 13 with hlamdef
  obtain ⟨Xr, CR, hCR, hR⟩ := FI_rtildeFull_sum_le lam
  obtain ⟨Xab, hab⟩ := FI_Aseq_le_const_mul_Atil
  set Cc : ℝ := 2 / Gprod FIg + 1 with hCcdef
  have hCcpos : 0 < Cc := by
    rw [hCcdef]
    have h := Gprod_FIg_pos
    positivity
  set K : ℝ := (C23 * (Cc + 1)) ^ ((3 : ℝ) / 4) * (CR * Cc) ^ ((1 : ℝ) / 4) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨Xl, hXl⟩ : ∃ X : ℕ, Real.exp (K ^ 4) ≤ (X : ℝ) :=
    ⟨⌈Real.exp (K ^ 4)⌉₊, Nat.le_ceil _⟩
  refine ⟨max (max (max ⌈X23r⌉₊ Xr) (max Xab Xl)) 64, fun x hx m hmD hmx => ?_⟩
  have hx23 : X23r ≤ (x : ℝ) :=
    le_trans (Nat.le_ceil X23r) (by exact_mod_cast (by omega : ⌈X23r⌉₊ ≤ x))
  have hxr : Xr ≤ x := by omega
  have hxab : Xab ≤ x := by omega
  have hxl : Xl ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
  have hlog1 : (1 : ℝ) ≤ Real.log x :=
    le_trans one_le_log_three (Real.log_le_log (by norm_num) hx3)
  have hlog0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hD2 : 2 ≤ Submission.Rcut x := le_trans (by norm_num : 2 ≤ 4) (four_le_Rcut hx64)
  have hm2 : 2 ≤ m := le_trans hD2 hmD
  -- the counting function and the two Hölder inputs
  have hAt1 : (1 : ℝ) ≤ Acount (atil FIa) (x : ℝ) := one_le_Acount_atil x hx1
  have hAt0 : (0 : ℝ) < Acount (atil FIa) (x : ℝ) := lt_of_lt_of_le zero_lt_one hAt1
  have hAsnn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    have h0 : (0 : ℝ) ≤ Acount FIa (x : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
    rw [FI_Acount_eq] at h0; linarith
  have hAsle : (Submission.Aseq x : ℝ) ≤ Cc * Acount (atil FIa) (x : ℝ) := by
    have h1 := hab x hxab
    rw [FI_Acount_eq] at h1
    have h3 : (2 / Gprod FIg) * Acount (atil FIa) (x : ℝ) + 1
        ≤ (2 / Gprod FIg) * Acount (atil FIa) (x : ℝ) + Acount (atil FIa) (x : ℝ) := by linarith
    have h4 : (2 / Gprod FIg) * Acount (atil FIa) (x : ℝ) + Acount (atil FIa) (x : ℝ)
        = Cc * Acount (atil FIa) (x : ℝ) := by rw [hCcdef]; ring
    linarith
  have hR' : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        |rtildeFull FIr FIg FIgtil FIa d m|)
      ≤ CR * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := hR x hxr m hmD hmx
  have h23' : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * |rtildeFull FIr FIg FIgtil FIa d m|)
      ≤ C23 * ((Submission.Aseq x : ℝ) + Acount (atil FIa) (x : ℝ)) * (Real.log x) ^ B23 :=
    h23 x hx23 m hm2 hmx (Submission.Rcut x) hmD
  -- the Hölder step
  have hholder := Commons.Analysis.MeanInequalities.sum_rpow_holder
    (F := fun d : ℕ => ((d.divisors.card : ℝ)))
    (R := fun d : ℕ => if Squarefree d then |rtildeFull FIr FIg FIgtil FIa d m| else 0)
    (fun d => by positivity) (fun d => by positivity) (Submission.Rcut x)
  have hE5 : (∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
        ((d.divisors.card : ℝ)) ^ 5
          * (if Squarefree d then |rtildeFull FIr FIg FIgtil FIa d m| else 0))
      = RemainderSum (rtildeFull FIr FIg FIgtil FIa) (Submission.Rcut x) m := by
    rw [RemainderSum, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun d _ => by by_cases h : Squarefree d <;> simp [h])
  have hE23 : (∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
          * (if Squarefree d then |rtildeFull FIr FIg FIgtil FIa d m| else 0))
      = (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * |rtildeFull FIr FIg FIgtil FIa d m|) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun d _ => by by_cases h : Squarefree d <;> simp [h])
  have hE0 : (∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
        (if Squarefree d then |rtildeFull FIr FIg FIgtil FIa d m| else 0))
      = (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
          |rtildeFull FIr FIg FIgtil FIa d m|) := by
    rw [Finset.sum_filter]
  set P : ℝ := C23 * ((Submission.Aseq x : ℝ) + Acount (atil FIa) (x : ℝ))
    * (Real.log x) ^ B23 with hPdef
  set Q : ℝ := CR * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) with hQdef
  have hPnn : (0 : ℝ) ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hC23.le (by linarith)) (Real.rpow_nonneg hlog0.le _)
  have hQnn : (0 : ℝ) ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg hCR.le hAsnn) (Real.rpow_nonneg hlog0.le _)
  have h23P : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * |rtildeFull FIr FIg FIgtil FIa d m|) ≤ P := by
    rw [hPdef]; exact h23'
  have hRQ : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        |rtildeFull FIr FIg FIgtil FIa d m|) ≤ Q := by
    rw [hQdef]; exact hR'
  have hH : RemainderSum (rtildeFull FIr FIg FIgtil FIa) (Submission.Rcut x) m
      ≤ P ^ ((3 : ℝ) / 4) * Q ^ ((1 : ℝ) / 4) := by
    rw [← hE5]
    refine le_trans hholder ?_
    have hbase1 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
          * (if Squarefree d then |rtildeFull FIr FIg FIgtil FIa d m| else 0) := by
      rw [hE23]
      exact Finset.sum_nonneg (fun d _ => mul_nonneg (by positivity) (abs_nonneg _))
    have hbase2 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
        (if Squarefree d then |rtildeFull FIr FIg FIgtil FIa d m| else 0) := by
      rw [hE0]
      exact Finset.sum_nonneg (fun d _ => abs_nonneg _)
    have hc1 : (∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
            * (if Squarefree d then |rtildeFull FIr FIg FIgtil FIa d m| else 0)) ^ ((3 : ℝ) / 4)
        ≤ P ^ ((3 : ℝ) / 4) := by
      refine Real.rpow_le_rpow hbase1 ?_ (by norm_num)
      rw [hE23]
      exact h23P
    have hc2 : (∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
          (if Squarefree d then |rtildeFull FIr FIg FIgtil FIa d m| else 0)) ^ ((1 : ℝ) / 4)
        ≤ Q ^ ((1 : ℝ) / 4) := by
      refine Real.rpow_le_rpow hbase2 ?_ (by norm_num)
      rw [hE0]
      exact hRQ
    exact mul_le_mul hc1 hc2 (Real.rpow_nonneg hbase2 _) (Real.rpow_nonneg hPnn _)
  -- the constant bookkeeping
  have hKey : (C23 * (Cc + 1)) ^ ((3 : ℝ) / 4) * (CR * Cc) ^ ((1 : ℝ) / 4)
      * (Real.log x) ^ (B23 * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ)) ≤ 1 := by
    have hKle : K ≤ (Real.log x) ^ ((1 : ℝ) / 4) := by
      have hh1 : K ^ 4 ≤ Real.log x := by
        have hh2 : Real.exp (K ^ 4) ≤ (x : ℝ) := le_trans hXl (by exact_mod_cast hxl)
        have hh3 := Real.log_le_log (Real.exp_pos _) hh2
        rwa [Real.log_exp] at hh3
      have hh4 : K = (K ^ 4) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hKpos)]
        norm_num
      rw [hh4]
      exact Real.rpow_le_rpow (by positivity) hh1 (by norm_num)
    have hexp : B23 * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ) = -((1 : ℝ) / 4) := by
      rw [hlamdef]; ring
    have h1 : (C23 * (Cc + 1)) ^ ((3 : ℝ) / 4) * (CR * Cc) ^ ((1 : ℝ) / 4) = K := hKdef.symm
    rw [h1, hexp]
    refine le_trans (mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hlog0.le _))
      (le_of_eq ?_)
    rw [← Real.rpow_add hlog0]
    norm_num
  refine le_trans hH ?_
  rw [hPdef, hQdef]
  exact holder_absorb hC23 hCR hCcpos hlog0 hAt0 hAsnn hAsle hKey

end

end Submission.ASP
