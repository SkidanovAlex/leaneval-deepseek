import Mathlib
import Submission.Work.ChenPlan.H1.Defs
import Submission.Work.ChenPlan.H1.Tools
import Submission.Work.NumberTheory.Chen.ChainDeficit.Port.VsieveLogRatioSharp

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Work.ChenPlan.H1

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight
open Commons.NumberTheory.Sieve (oddProd oddFac oddSqProd oddSqFac primeProd)

lemma primeFactors_oddPrimLt (M : ℕ) : (oddPrimLt M).primeFactors = oddLt M := by
  rw [oddPrimLt_eq_prod_oddLt]
  exact Nat.primeFactors_prod (fun p hp => (Submission.mem_oddLt.mp hp).1)

lemma oddProd_pred_eq_VsieveOdd (M : ℕ) (hM : 1 ≤ M) :
    oddProd (M - 1) = VsieveOdd M := by
  conv_rhs => rw [← Nat.sub_add_cancel hM]
  rw [VsieveOdd_primesLE]
  simp only [oddProd, oddFac]

lemma oddLt_subset {k M : ℕ} (h : k ≤ M) : oddLt k ⊆ oddLt M := by
  intro p hp
  rw [Submission.mem_oddLt] at hp ⊢
  exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 h⟩

lemma filter_oddLt_eq_sdiff (M k : ℕ) :
    (oddLt M).filter (fun p => k ≤ p) = oddLt M \ oddLt k := by
  ext p
  rw [Finset.mem_filter, Finset.mem_sdiff, Submission.mem_oddLt, Submission.mem_oddLt]
  constructor
  · rintro ⟨hp, hkp⟩
    exact ⟨hp, fun h => (not_lt.mpr hkp) h.2.2⟩
  · rintro ⟨hp, hpk⟩
    refine ⟨hp, ?_⟩
    by_contra hlt
    exact hpk ⟨hp.1, hp.2.1, not_le.mp hlt⟩

lemma VsieveOdd_pos (M : ℕ) : 0 < VsieveOdd M := by
  rw [VsieveOdd]
  refine Finset.prod_pos (fun p hp => ?_)
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by
    have := (Submission.mem_oddLt.mp hp).2.1
    exact_mod_cast this
  have h1 : (1:ℝ) < (p:ℝ) - 1 := by linarith
  have h2 : 1/((p:ℝ)-1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

lemma sieveProd_eq_VsieveOdd_div (M k : ℕ) (hk : 2 ≤ k) (hkM : k ≤ M) :
    ∏ p ∈ (oddLt M).filter (fun p => k ≤ p), (1 - 1/((p:ℝ)-1))⁻¹
      = VsieveOdd k / VsieveOdd M := by
  have hsub : oddLt k ⊆ oddLt M := oddLt_subset hkM
  have hsd := Finset.prod_sdiff hsub (f := fun p : ℕ => (1 - 1/((p:ℝ)-1)))
  have hVk : VsieveOdd k ≠ 0 := ne_of_gt (VsieveOdd_pos k)
  rw [filter_oddLt_eq_sdiff, Finset.prod_inv_distrib]
  have hP : (∏ x ∈ oddLt M \ oddLt k, (1 - 1/((x:ℝ)-1))) = VsieveOdd M / VsieveOdd k := by
    rw [eq_div_iff hVk]
    have hsd' := hsd
    rw [show (∏ x ∈ oddLt k, (1 - 1/((x:ℝ)-1))) = VsieveOdd k from rfl,
        show (∏ x ∈ oddLt M, (1 - 1/((x:ℝ)-1))) = VsieveOdd M from rfl] at hsd'
    exact hsd'
  rw [hP, inv_div]

lemma oddProd_pos (n : ℕ) : 0 < oddProd n := by
  have h := oddProd_pred_eq_VsieveOdd (n+1) (by omega)
  rw [Nat.add_sub_cancel] at h
  rw [h]; exact VsieveOdd_pos (n+1)

lemma log5_ge : (1.386:ℝ) ≤ Real.log 5 := by
  have h4 : Real.log (4:ℝ) ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
  have hlog4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_gt_d9, h4, hlog4]

lemma log2049_le : Real.log (2049:ℝ) ≤ 7.63 := by
  have hmul : (2049:ℝ) = (2048:ℝ) * (2049/2048) := by norm_num
  rw [hmul, Real.log_mul (by norm_num) (by norm_num)]
  have h2 : Real.log ((2049:ℝ)/2048) ≤ (2049:ℝ)/2048 - 1 :=
    le_of_lt (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num))
  rw [show (2049:ℝ)/2048 - 1 = 1/2048 by norm_num] at h2
  have hlog2048 : Real.log ((2048:ℝ)) = 11 * Real.log 2 := by
    rw [show (2048:ℝ) = 2^11 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9, h2, hlog2048]

lemma oddProd_ratio_small (Z₀ : ℕ)
    (hZ₀ : ∀ z : ℕ, Z₀ ≤ z → ∀ p : ℕ, Nat.Prime p → 5 ≤ p → p ≤ z →
      oddProd (p - 1) ≤ (6/5) * (Real.log (z:ℝ) / Real.log (p:ℝ)) * oddProd z)
    (M k : ℕ) (hZ : Z₀ ≤ M) (hM5 : 5 ≤ M) (hk : 2 ≤ k) (hk2049 : k ≤ 2049) (hkM : k ≤ M) :
    oddProd (k-1)/oddProd (M-1) ≤ (Real.log (M:ℝ) / Real.log (k:ℝ)) * (1 + 100/Real.log (k:ℝ)) := by
  have hM1 : 1 ≤ M := by omega
  have hlogM : 0 < Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogk : 0 < Real.log (k:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hP4 : oddProd 4 = 1/2 := by
    rw [oddProd]
    rw [show (Nat.primesLE 4).filter (fun q : ℕ => q ≠ 2) = {3} from by decide]
    simp [oddFac]; norm_num
  have h5 : (1/2 : ℝ) ≤ (6/5) * (Real.log (M:ℝ)/Real.log (5:ℝ)) * oddProd M := by
    have h := hZ₀ M hZ 5 (by norm_num) (le_refl 5) hM5
    rwa [hP4] at h
  have hlow : (5/12) * (Real.log 5 / Real.log (M:ℝ)) ≤ oddProd M := by
    have hlog5pos : 0 < Real.log (5:ℝ) := Real.log_pos (by norm_num)
    have key : (1/2:ℝ) * Real.log 5 ≤ (6/5) * Real.log (M:ℝ) * oddProd M := by
      rw [show (6/5:ℝ) * (Real.log (M:ℝ)/Real.log (5:ℝ)) * oddProd M
            = (6/5) * Real.log (M:ℝ) * oddProd M / Real.log (5:ℝ) from by ring] at h5
      rwa [le_div_iff₀ hlog5pos] at h5
    rw [show (5/12:ℝ) * (Real.log 5 / Real.log (M:ℝ))
          = (5/12) * Real.log 5 / Real.log (M:ℝ) from by ring, div_le_iff₀ hlogM]
    nlinarith [key, hlogM]
  have h1M : 1/oddProd M ≤ (12/5)*(Real.log (M:ℝ)/Real.log (5:ℝ)) := by
    rw [div_le_iff₀ (oddProd_pos M)]
    have hlog5pos : 0 < Real.log (5:ℝ) := Real.log_pos (by norm_num)
    nlinarith [hlow, hlogM, hlog5pos]
  have hR : oddProd (k-1)/oddProd (M-1) ≤ (12/5)*(Real.log (M:ℝ)/Real.log (5:ℝ)) := by
    have hMM : oddProd M ≤ oddProd (M-1) := Commons.NumberTheory.Sieve.oddProd_anti (by omega)
    have hk1 : oddProd (k-1) ≤ 1 := Commons.NumberTheory.Sieve.oddProd_le_one (k-1)
    calc oddProd (k-1)/oddProd (M-1) ≤ 1/oddProd (M-1) :=
          div_le_div_of_nonneg_right hk1 (le_of_lt (oddProd_pos _))
      _ ≤ 1/oddProd M := div_le_div_of_nonneg_left (by norm_num) (oddProd_pos M) hMM
      _ ≤ (12/5)*(Real.log (M:ℝ)/Real.log (5:ℝ)) := h1M
  have hcomp : (12/5)/Real.log 5 ≤ (1/Real.log (k:ℝ)) * (1 + 100/Real.log (k:ℝ)) := by
    have hlog5pos : 0 < Real.log (5:ℝ) := Real.log_pos (by norm_num)
    have hklog : Real.log (k:ℝ) ≤ 7.63 :=
      le_trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk2049)) log2049_le
    have hA : (12/5)/Real.log 5 ≤ (12/5)/1.386 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) log5_ge
    have hB : (12/5 : ℝ)/1.386 ≤ (1+100/7.63)/7.63 := by norm_num
    have hC : (1+100/7.63)/7.63 ≤ (1+100/Real.log (k:ℝ))/Real.log (k:ℝ) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 7.63) hlogk]
      have h1 : 100*Real.log (k:ℝ)/7.63 ≤ 100 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 7.63)]; nlinarith [hklog]
      have h2 : 100 ≤ 7.63*100/Real.log (k:ℝ) := by
        rw [le_div_iff₀ hlogk]; nlinarith [hklog]
      have e1 : (1+100/7.63) * Real.log (k:ℝ) = Real.log (k:ℝ) + 100*Real.log (k:ℝ)/7.63 := by
        field_simp
      have e2 : (1+100/Real.log (k:ℝ)) * 7.63 = 7.63 + 7.63*100/Real.log (k:ℝ) := by
        field_simp
      rw [e1, e2]; linarith
    calc (12/5)/Real.log 5 ≤ (12/5)/1.386 := hA
      _ ≤ (1+100/7.63)/7.63 := hB
      _ ≤ (1+100/Real.log (k:ℝ))/Real.log (k:ℝ) := hC
      _ = (1/Real.log (k:ℝ)) * (1 + 100/Real.log (k:ℝ)) := by ring
  calc oddProd (k-1)/oddProd (M-1) ≤ (12/5)*(Real.log (M:ℝ)/Real.log (5:ℝ)) := hR
    _ = Real.log (M:ℝ) * ((12/5)/Real.log 5) := by ring
    _ ≤ Real.log (M:ℝ) * ((1/Real.log (k:ℝ)) * (1 + 100/Real.log (k:ℝ))) :=
        mul_le_mul_of_nonneg_left hcomp (le_of_lt hlogM)
    _ = (Real.log (M:ℝ) / Real.log (k:ℝ)) * (1 + 100/Real.log (k:ℝ)) := by ring

lemma TP_eq_oddSqProd (n : ℕ) : Work.NumberTheory.Chen.TP n = oddSqProd n := by
  simp only [Work.NumberTheory.Chen.TP, oddSqProd, oddSqFac, one_div]

lemma oddSqProd_pos (n : ℕ) : 0 < oddSqProd n := by
  rw [oddSqProd]
  refine Finset.prod_pos (fun q hq => ?_)
  have hq2 : q ≠ 2 := (Finset.mem_filter.mp hq).2
  have hp : Nat.Prime q := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
  have h3 : 3 ≤ q := by have := hp.two_le; omega
  have h3' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast h3
  have hpos : (0:ℝ) < (q:ℝ) - 1 := by linarith
  have h1 : (1:ℝ) < ((q:ℝ)-1)^2 := by nlinarith
  rw [oddSqFac]
  have h2 : 1/((q:ℝ)-1)^2 < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  linarith
lemma log_comparison (k : ℕ) (hk : 2049 ≤ k) :
    2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)
      + 1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)) + 2/((k:ℝ)-2)
      ≤ Real.log (1 + 100/Real.log (k:ℝ)) := by
  have hkm1 : 2048 ≤ k - 1 := by omega
  have hkR : (2049:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hk1 : (1:ℝ) < (k:ℝ) := by linarith
  have hLpos : 0 < Real.log (k:ℝ) := Real.log_pos hk1
  have hkm1R : (2048:ℝ) ≤ ((k-1:ℕ):ℝ) := by exact_mod_cast hkm1
  have hkm1pos : (0:ℝ) < ((k-1:ℕ):ℝ) := by linarith
  have hLkpos : 0 < Real.log ((k-1:ℕ):ℝ) := Real.log_pos (by linarith)
  have hcast : ((k-1:ℕ):ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  have hk2pos : (0:ℝ) < (k:ℝ) - 2 := by linarith
  have hLk_ge : (7.62:ℝ) ≤ Real.log ((k-1:ℕ):ℝ) := by
    have h : Real.log (2048:ℝ) ≤ Real.log ((k-1:ℕ):ℝ) :=
      Real.log_le_log (by norm_num) hkm1R
    have hlog2048 : Real.log (2048:ℝ) = 11 * Real.log 2 := by
      rw [show (2048:ℝ) = 2^11 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9, h, hlog2048]
  have hlog1p : 100/(Real.log (k:ℝ)+50) ≤ Real.log (1 + 100/Real.log (k:ℝ)) := by
    have h := Real.le_log_one_add_of_nonneg (x := 100/Real.log (k:ℝ)) (by positivity)
    have he : 2*(100/Real.log (k:ℝ))/((100/Real.log (k:ℝ))+2) = 100/(Real.log (k:ℝ)+50) := by
      field_simp
      ring
    linarith [h, he.symm.le]
  by_cases hcase : Real.log (k:ℝ) ≤ 152
  · have h1 : 2.96/Real.log ((k-1:ℕ):ℝ) ≤ 2.96/7.62 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLk_ge
    have h2 : 8/((k-1:ℕ):ℝ) ≤ 8/2048 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkm1R
    have h3 : 1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)) ≤ 1/(2048*7.62) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hm := mul_le_mul hkm1R hLk_ge (by norm_num) (le_of_lt hkm1pos)
      linarith [hm]
    have h4 : 2/((k:ℝ)-2) ≤ 2/2047 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith [hkR]
    have hsum : 2.96/7.62 + 8/2048 + 1/(2048*7.62) + 2/2047 ≤ 100/(Real.log (k:ℝ)+50) := by
      have hc : (2.96/7.62 + 8/2048 + 1/(2048*7.62) + 2/2047 : ℝ) ≤ 0.3935 := by norm_num
      have hd : (0.3935:ℝ) ≤ 100/(Real.log (k:ℝ)+50) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [hcase]
      linarith
    linarith [h1, h2, h3, h4, hsum, hlog1p]
  · have hL : (152:ℝ) ≤ Real.log (k:ℝ) := le_of_lt (not_le.mp hcase)
    have hk_eq : Real.exp (Real.log (k:ℝ)) = (k:ℝ) := Real.exp_log (by linarith)
    have hLk_half : Real.log (k:ℝ)/2 ≤ Real.log ((k-1:ℕ):ℝ) := by
      have hsplit : Real.log (k:ℝ) = Real.log ((k-1:ℕ):ℝ) + Real.log ((k:ℝ)/((k-1:ℕ):ℝ)) := by
        rw [← Real.log_mul (ne_of_gt hkm1pos) (by positivity)]
        congr 1; field_simp
      have hpos : (0:ℝ) < (k:ℝ)/((k-1:ℕ):ℝ) := by positivity
      have hne : (k:ℝ)/((k-1:ℕ):ℝ) ≠ 1 := by
        intro h; rw [div_eq_one_iff_eq (ne_of_gt hkm1pos)] at h
        rw [hcast] at h; linarith
      have hle := le_of_lt (Real.log_lt_sub_one_of_pos hpos hne)
      have hdiff : (k:ℝ)/((k-1:ℕ):ℝ) - 1 = 1/((k-1:ℕ):ℝ) := by
        rw [div_sub_one (ne_of_gt hkm1pos)]
        congr 1
        rw [hcast]; ring
      rw [hdiff] at hle
      have hinv : 1/((k-1:ℕ):ℝ) ≤ Real.log (k:ℝ)/2 := by
        have h1 : 1/((k-1:ℕ):ℝ) ≤ 1/2048 :=
          one_div_le_one_div_of_le (by norm_num) hkm1R
        linarith [h1, hL]
      linarith [hsplit, hle, hinv]
    have hk_sub : Real.log (k:ℝ) ≤ (k:ℝ) - 1 := by
      have := Real.add_one_le_exp (Real.log (k:ℝ))
      rw [hk_eq] at this; linarith
    have h1 : 2.96/Real.log ((k-1:ℕ):ℝ) ≤ 5.92/Real.log (k:ℝ) := by
      rw [div_le_div_iff₀ hLkpos hLpos]
      nlinarith [hLk_half]
    have h2 : 8/((k-1:ℕ):ℝ) ≤ 8/Real.log (k:ℝ) := by
      rw [div_le_div_iff₀ hkm1pos hLpos]
      nlinarith [hk_sub]
    have h3 : 1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)) ≤ 2/(Real.log (k:ℝ))^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hLk_half, hk_sub, hLpos, hkm1pos, hLkpos]
    have h4 : 2/((k:ℝ)-2) ≤ 4/Real.log (k:ℝ) := by
      rw [div_le_div_iff₀ (by linarith) hLpos]
      nlinarith [hk_sub, hL]
    have hsum : 5.92/Real.log (k:ℝ) + 8/Real.log (k:ℝ) + 2/(Real.log (k:ℝ))^2 + 4/Real.log (k:ℝ)
        ≤ 100/(Real.log (k:ℝ)+50) := by
      have hL0 : 0 < Real.log (k:ℝ) := hLpos
      have hL50 : 0 < Real.log (k:ℝ) + 50 := by linarith
      have hkey : 898*Real.log (k:ℝ) + 100 ≤ 82.08 * (Real.log (k:ℝ))^2 := by nlinarith [hL]
      rw [show 5.92/Real.log (k:ℝ) + 8/Real.log (k:ℝ) + 2/(Real.log (k:ℝ))^2 + 4/Real.log (k:ℝ)
            = 17.92/Real.log (k:ℝ) + 2/(Real.log (k:ℝ))^2 from by ring]
      rw [div_add_div _ _ (ne_of_gt hL0) (by positivity)]
      rw [div_le_div_iff₀ (by positivity) hL50]
      nlinarith [hkey, hL0]
    linarith [h1, h2, h3, h4, hsum, hlog1p]
lemma oddProd_ratio_large (M k : ℕ) (hk : 2049 ≤ k) (hkM : k ≤ M) :
    oddProd (k-1)/oddProd (M-1) ≤ (Real.log (M:ℝ) / Real.log (k:ℝ)) * (1 + 100/Real.log (k:ℝ)) := by
  have hk2 : 2 ≤ k := by omega
  have hkm1 : 2 ≤ k-1 := by omega
  have hkm1' : 2048 ≤ k-1 := by omega
  have hMm1 : 2 ≤ M-1 := by omega
  have hM100 : 100 ≤ M-1 := by omega
  have hMm1le : k-1 ≤ M-1 := by omega
  have hkR : (2049:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkm1pos : 0 < ((k-1:ℕ):ℝ) := by positivity
  have hMm1pos : 0 < ((M-1:ℕ):ℝ) := by positivity
  have hkm1posR : (0:ℝ) < ((k-1:ℕ):ℝ) := hkm1pos
  have hLkpos : 0 < Real.log ((k-1:ℕ):ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k-1))
  have hLmpos : 0 < Real.log ((M-1:ℕ):ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M-1))
  have hLpos : 0 < Real.log (k:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hlogMpos : 0 < Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hLk_le_Lm : Real.log ((k-1:ℕ):ℝ) ≤ Real.log ((M-1:ℕ):ℝ) :=
    Real.log_le_log hkm1pos (by exact_mod_cast hMm1le)
  have hcast : ((k-1:ℕ):ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  have hk2pos : (0:ℝ) < (k:ℝ) - 2 := by linarith
  -- Q bound
  have hPu : primeProd (k-1) * Real.log ((k-1:ℕ):ℝ)
      ≤ Real.exp (-Real.eulerMascheroniConstant)
        * Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)) := by
    have h := Commons.NumberTheory.Sieve.Aux.my_logRatioSum_ge ((k-1:ℕ):ℝ) (by exact_mod_cast (by omega : 100 ≤ k-1))
    rw [Commons.NumberTheory.Sieve.primeProd_eq_exp]
    have h2 : Real.exp (-Commons.NumberTheory.Mertens.logRatioSum ((k-1:ℕ):ℝ))
        ≤ Real.exp (-Real.log (Real.log ((k-1:ℕ):ℝ)) - Real.eulerMascheroniConstant
            + ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))) :=
      Real.exp_le_exp.mpr (by linarith [h])
    calc Real.exp (-Commons.NumberTheory.Mertens.logRatioSum ((k-1:ℕ):ℝ)) * Real.log ((k-1:ℕ):ℝ)
        ≤ Real.exp (-Real.log (Real.log ((k-1:ℕ):ℝ)) - Real.eulerMascheroniConstant
            + ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))) * Real.log ((k-1:ℕ):ℝ) :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hLkpos)
      _ = Real.exp (-Real.eulerMascheroniConstant)
            * Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)) := by
          rw [show -Real.log (Real.log ((k-1:ℕ):ℝ)) - Real.eulerMascheroniConstant
                + ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
              = (-Real.log (Real.log ((k-1:ℕ):ℝ))) + (-Real.eulerMascheroniConstant
                + ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))) from by ring]
          rw [Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hLkpos]
          field_simp
  have hPlm : Real.exp (-Real.eulerMascheroniConstant)
      * (Real.exp (3/(2*Real.log ((M-1:ℕ):ℝ))))⁻¹ / Real.log ((M-1:ℕ):ℝ) ≤ primeProd (M-1) := by
    have h := Commons.NumberTheory.Sieve.primeProd_ge (M-1) hM100
    have heq : Real.exp (-(3/2)/Real.log ((M-1:ℕ):ℝ))
        = (Real.exp (3/(2*Real.log ((M-1:ℕ):ℝ))))⁻¹ := by
      rw [show -(3/2)/Real.log ((M-1:ℕ):ℝ)
            = -(3/(2*Real.log ((M-1:ℕ):ℝ))) from by ring, Real.exp_neg]
    rwa [heq] at h
  have hQ : primeProd (k-1)/primeProd (M-1)
      ≤ Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
        * Real.exp (3/(2*Real.log ((M-1:ℕ):ℝ)))
        * (Real.log ((M-1:ℕ):ℝ)/Real.log ((k-1:ℕ):ℝ)) := by
    have hnum : primeProd (k-1) ≤ Real.exp (-Real.eulerMascheroniConstant)
        * Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)) / Real.log ((k-1:ℕ):ℝ) := by
      rw [le_div_iff₀ hLkpos]; linarith [hPu]
    calc primeProd (k-1)/primeProd (M-1)
        ≤ (Real.exp (-Real.eulerMascheroniConstant)
            * Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)) / Real.log ((k-1:ℕ):ℝ))
          / primeProd (M-1) := div_le_div_of_nonneg_right hnum (le_of_lt (Commons.NumberTheory.Sieve.primeProd_pos _))
      _ ≤ (Real.exp (-Real.eulerMascheroniConstant)
            * Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)) / Real.log ((k-1:ℕ):ℝ))
          / (Real.exp (-Real.eulerMascheroniConstant)
            * (Real.exp (3/(2*Real.log ((M-1:ℕ):ℝ))))⁻¹ / Real.log ((M-1:ℕ):ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hPlm
      _ = Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
            * Real.exp (3/(2*Real.log ((M-1:ℕ):ℝ)))
            * (Real.log ((M-1:ℕ):ℝ)/Real.log ((k-1:ℕ):ℝ)) := by
            field_simp
  -- TS bound
  have hTS : oddSqProd (k-1)/oddSqProd (M-1) ≤ 1 + 2/((k:ℝ)-2) := by
    have hpos : 0 < oddSqProd (M-1) := oddSqProd_pos (M-1)
    have hge : (1/2:ℝ) ≤ oddSqProd (M-1) := le_trans (by norm_num) (Commons.NumberTheory.Sieve.oddSqProd_ge (M-1))
    have hd : oddSqProd (k-1) - oddSqProd (M-1) ≤ ((k:ℝ)-2)⁻¹ := by
      have h := Work.NumberTheory.Chen.ChainDeficit.Port.TP_tail_le (n := k-1) (m := M-1) (by omega : 2 ≤ k-1) hMm1le
      rw [TP_eq_oddSqProd, TP_eq_oddSqProd] at h
      have hcast2 : (((k-1:ℕ):ℝ) - 1) = (k:ℝ) - 2 := by rw [Nat.cast_sub (by omega : 1 ≤ k)]; ring
      rw [hcast2, one_div] at h
      exact h
    have h1 : oddSqProd (k-1) ≤ oddSqProd (M-1) + ((k:ℝ)-2)⁻¹ := by linarith [hd]
    calc oddSqProd (k-1)/oddSqProd (M-1)
        ≤ (oddSqProd (M-1) + ((k:ℝ)-2)⁻¹)/oddSqProd (M-1) :=
          div_le_div_of_nonneg_right h1 (le_of_lt hpos)
      _ = 1 + ((k:ℝ)-2)⁻¹/oddSqProd (M-1) := by field_simp
      _ ≤ 1 + 2/((k:ℝ)-2) := by
          have hle : ((k:ℝ)-2)⁻¹/oddSqProd (M-1) ≤ 2/((k:ℝ)-2) := by
            rw [div_le_div_iff₀ hpos hk2pos]
            rw [inv_mul_cancel₀ (ne_of_gt hk2pos)]
            linarith [hge]
          linarith [hle]
  -- log ratio
  have hL_div : Real.log (k:ℝ)/Real.log ((k-1:ℕ):ℝ)
      ≤ 1 + 1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)) := by
    have hsplit : Real.log (k:ℝ) = Real.log ((k-1:ℕ):ℝ) + Real.log ((k:ℝ)/((k-1:ℕ):ℝ)) := by
      rw [← Real.log_mul (ne_of_gt hkm1posR) (by positivity)]
      congr 1; field_simp
    have hlogle : Real.log ((k:ℝ)/((k-1:ℕ):ℝ)) ≤ 1/((k-1:ℕ):ℝ) := by
      have hpos : (0:ℝ) < (k:ℝ)/((k-1:ℕ):ℝ) := by positivity
      have hne : (k:ℝ)/((k-1:ℕ):ℝ) ≠ 1 := by
        intro h; rw [div_eq_one_iff_eq (ne_of_gt hkm1posR)] at h
        rw [hcast] at h; linarith
      have hh := le_of_lt (Real.log_lt_sub_one_of_pos hpos hne)
      have hdiff : (k:ℝ)/((k-1:ℕ):ℝ) - 1 = 1/((k-1:ℕ):ℝ) := by
        rw [div_sub_one (ne_of_gt hkm1posR)]; congr 1; rw [hcast]; ring
      rwa [hdiff] at hh
    have he : (1/((k-1:ℕ):ℝ))/Real.log ((k-1:ℕ):ℝ)
        = 1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)) := by ring
    rw [hsplit, add_div, div_self (ne_of_gt hLkpos)]
    have := div_le_div_of_nonneg_right hlogle hLkpos.le
    linarith [this, he]
  -- assembly
  have hexp1 : Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
      * Real.exp (3/(2*Real.log ((M-1:ℕ):ℝ))) ≤ Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h2 : 3/(2*Real.log ((M-1:ℕ):ℝ)) ≤ (3/2)/Real.log ((k-1:ℕ):ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hLkpos]
      nlinarith [hLk_le_Lm]
    have h3 : (73/50)/Real.log ((k-1:ℕ):ℝ) + (3/2)/Real.log ((k-1:ℕ):ℝ)
        = 2.96/Real.log ((k-1:ℕ):ℝ) := by ring
    linarith [h2, h3]
  have hf3 : Real.log (k:ℝ)/Real.log ((k-1:ℕ):ℝ)
      ≤ Real.exp (1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ))) := by
    have hh := Real.add_one_le_exp (1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)))
    linarith [hL_div, hh]
  have hRdec : oddProd (k-1)/oddProd (M-1)
      = (primeProd (k-1)/primeProd (M-1)) * (oddSqProd (k-1)/oddSqProd (M-1)) := by
    rw [Commons.NumberTheory.Sieve.oddProd_decomp hkm1, Commons.NumberTheory.Sieve.oddProd_decomp hMm1]
    field_simp
  have hQ' : primeProd (k-1)/primeProd (M-1)
      ≤ Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
        * (Real.log ((M-1:ℕ):ℝ)/Real.log ((k-1:ℕ):ℝ)) := by
    calc primeProd (k-1)/primeProd (M-1)
        ≤ Real.exp ((73/50)/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
            * Real.exp (3/(2*Real.log ((M-1:ℕ):ℝ)))
            * (Real.log ((M-1:ℕ):ℝ)/Real.log ((k-1:ℕ):ℝ)) := hQ
      _ ≤ Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
            * (Real.log ((M-1:ℕ):ℝ)/Real.log ((k-1:ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_right hexp1 (div_nonneg hLmpos.le hLkpos.le)
  have hf2 : Real.log ((M-1:ℕ):ℝ) / Real.log (M:ℝ) ≤ 1 := by
    rw [div_le_one hlogMpos]
    exact Real.log_le_log hMm1pos (by exact_mod_cast (by omega : M-1 ≤ M))
  have hf4 : 1 + 2/((k:ℝ)-2) ≤ Real.exp (2/((k:ℝ)-2)) := by
    rw [add_comm]; exact Real.add_one_le_exp _
  have hbig : oddProd (k-1)/oddProd (M-1) * (Real.log (k:ℝ)/Real.log (M:ℝ))
      ≤ Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
        * (Real.log ((M-1:ℕ):ℝ)/Real.log (M:ℝ))
        * (Real.log (k:ℝ)/Real.log ((k-1:ℕ):ℝ)) * (1 + 2/((k:ℝ)-2)) := by
    have hTSnn : 0 ≤ oddSqProd (k-1)/oddSqProd (M-1) :=
      le_of_lt (div_pos (oddSqProd_pos _) (oddSqProd_pos _))
    have hXnn : 0 ≤ Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
        * (Real.log ((M-1:ℕ):ℝ)/Real.log ((k-1:ℕ):ℝ)) :=
      mul_nonneg (Real.exp_pos _).le (div_nonneg hLmpos.le hLkpos.le)
    rw [hRdec]
    calc (primeProd (k-1)/primeProd (M-1)) * (oddSqProd (k-1)/oddSqProd (M-1))
          * (Real.log (k:ℝ)/Real.log (M:ℝ))
        ≤ (Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
            * (Real.log ((M-1:ℕ):ℝ)/Real.log ((k-1:ℕ):ℝ)) * (1 + 2/((k:ℝ)-2)))
          * (Real.log (k:ℝ)/Real.log (M:ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hQ' hTS hTSnn hXnn) (div_nonneg hLpos.le hlogMpos.le)
      _ = Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
            * (Real.log ((M-1:ℕ):ℝ)/Real.log (M:ℝ))
            * (Real.log (k:ℝ)/Real.log ((k-1:ℕ):ℝ)) * (1 + 2/((k:ℝ)-2)) := by ring
  have hexpA : Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)
        + 1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)) + 2/((k:ℝ)-2))
      ≤ 1 + 100/Real.log (k:ℝ) := by
    rw [← Real.exp_log (by positivity : (0:ℝ) < 1 + 100/Real.log (k:ℝ))]
    exact Real.exp_le_exp.mpr (log_comparison k hk)
  have hprod : oddProd (k-1)/oddProd (M-1) * (Real.log (k:ℝ)/Real.log (M:ℝ))
      ≤ Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)
          + 1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)) + 2/((k:ℝ)-2)) := by
    refine le_trans hbig ?_
    calc Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ))
          * (Real.log ((M-1:ℕ):ℝ)/Real.log (M:ℝ))
          * (Real.log (k:ℝ)/Real.log ((k-1:ℕ):ℝ)) * (1 + 2/((k:ℝ)-2))
        ≤ Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)) * 1
          * Real.exp (1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ))) * Real.exp (2/((k:ℝ)-2)) := by
          apply mul_le_mul
          · apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hf2 (Real.exp_pos _).le
            · exact hf3
            · exact div_nonneg hLpos.le hLkpos.le
            · positivity
          · exact hf4
          · have h4nn : (0:ℝ) ≤ 2/((k:ℝ)-2) := div_nonneg (by norm_num) hk2pos.le
            linarith
          · positivity
      _ = Real.exp (2.96/Real.log ((k-1:ℕ):ℝ) + 8/((k-1:ℕ):ℝ)
            + 1/(((k-1:ℕ):ℝ)*Real.log ((k-1:ℕ):ℝ)) + 2/((k:ℝ)-2)) := by
          rw [mul_one, ← Real.exp_add, ← Real.exp_add]
  have hfin : oddProd (k-1)/oddProd (M-1) * (Real.log (k:ℝ)/Real.log (M:ℝ)) ≤ 1 + 100/Real.log (k:ℝ) :=
    le_trans hprod hexpA
  rw [show oddProd (k-1)/oddProd (M-1) * (Real.log (k:ℝ)/Real.log (M:ℝ))
        = oddProd (k-1)/oddProd (M-1) * Real.log (k:ℝ)/Real.log (M:ℝ) from by ring] at hfin
  rw [div_le_iff₀ hlogMpos] at hfin
  rw [div_mul_eq_mul_div, le_div_iff₀ hLpos]
  linarith [hfin]

lemma pow10000_ge_five : (5:ℕ) ≤ 2^10000 := by
  calc (5:ℕ) ≤ 2^3 := by norm_num
    _ ≤ 2^10000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

lemma eventually_chenSiftLimitTenth_ge (N : ℕ) :
    ∀ᶠ x : ℕ in Filter.atTop, N ≤ Submission.chenSiftLimitTenth x := by
  rw [Filter.eventually_atTop]
  refine ⟨N^10, fun x hx => ?_⟩
  have hxR : ((N:ℝ))^10 ≤ (x:ℝ) := by
    have h2 : ((N^10 : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    push_cast at h2
    exact h2
  have hbase : ((N:ℝ)) = ((N:ℝ)^10)^((1:ℝ)/10) := by
    rw [(Real.rpow_natCast_mul (by positivity : (0:ℝ) ≤ (N:ℝ)) 10 ((1:ℝ)/10)).symm,
        show ((10:ℕ):ℝ) * ((1:ℝ)/10) = 1 by norm_num, Real.rpow_one]
  have h1 : ((N:ℝ)^10)^((1:ℝ)/10) ≤ (x:ℝ)^((1:ℝ)/10) :=
    Real.rpow_le_rpow (by positivity) hxR (by norm_num)
  have h2 : N ≤ ⌊Real.rpow (x:ℝ) (1/10)⌋₊ := Nat.le_floor (by rw [hbase]; exact h1)
  show N ≤ ⌊Real.rpow (x:ℝ) (1/10)⌋₊ + 1
  omega

theorem isLinear_chenSieve :
    ∀ᶠ x : ℕ in Filter.atTop,
      Submission.ChenPlan.IsLinear (chenSieve x (Submission.chenSiftLimitTenth x))
        (Submission.chenSiftLimitTenth x : ℝ) 100 := by
  obtain ⟨Z₀, hZ₀⟩ := Commons.NumberTheory.Sieve.oddEulerProduct_ratio_le_log_p5
  filter_upwards [eventually_chenSiftLimitTenth_ge (max Z₀ (2^10000))] with x hx
  set M : ℕ := Submission.chenSiftLimitTenth x
  have hMZ : Z₀ ≤ M := le_trans (le_max_left _ _) hx
  have hMbig : 2^10000 ≤ M := le_trans (le_max_right _ _) hx
  have hM5 : 5 ≤ M := le_trans pow10000_ge_five hMbig
  have hM1 : 1 ≤ M := by omega
  have hnu : ∀ p ∈ oddLt M, (chenSieve x M).nu p = 1/((p:ℝ)-1) := by
    intro p hp
    have hpp : Nat.Prime p := (Submission.mem_oddLt.mp hp).1
    have hp1 : 1 ≤ p := hpp.one_le
    rw [show (chenSieve x M).nu = invTotient from rfl, invTotient_apply, Nat.totient_prime hpp,
        Nat.cast_sub hp1, one_div]
    norm_num
  have hLpos : 0 < Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  constructor
  · intro p hp
    rw [show (chenSieve x M).prodPrimes = oddPrimLt M from rfl, primeFactors_oddPrimLt M] at hp
    have hpM : p < M := (Submission.mem_oddLt.mp hp).2.2
    exact_mod_cast hpM
  · intro w hw2 hwM
    rw [show (chenSieve x M).prodPrimes = oddPrimLt M from rfl, primeFactors_oddPrimLt M]
    set k : ℕ := Nat.ceil w
    have hkw : w ≤ (k:ℝ) := Nat.le_ceil w
    have hk2 : 2 ≤ k := by
      have : (2:ℝ) ≤ (k:ℝ) := le_trans hw2 hkw
      exact_mod_cast this
    have hkM : k ≤ M := by rw [Nat.ceil_le]; exact le_of_lt hwM
    have hkpos : 0 < Real.log (k:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hwpos : 0 < Real.log w := Real.log_pos (by linarith)
    have hlogwk : Real.log w ≤ Real.log (k:ℝ) := Real.log_le_log (by linarith) hkw
    have hfilt : (oddLt M).filter (fun p : ℕ => w ≤ (p:ℝ))
        = (oddLt M).filter (fun p : ℕ => k ≤ p) := by
      apply Finset.filter_congr
      intro p hp
      show w ≤ (p:ℝ) ↔ Nat.ceil w ≤ p
      rw [Nat.ceil_le]
    have hnu' : ∀ p ∈ (oddLt M).filter (fun p : ℕ => k ≤ p),
        (1 - (chenSieve x M).nu p)⁻¹ = (1 - 1/((p:ℝ)-1))⁻¹ := by
      intro p hp
      rw [hnu p (Finset.mem_filter.mp hp).1]
    have hstep1 : ∏ p ∈ (oddLt M).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - (chenSieve x M).nu p)⁻¹
        = ∏ p ∈ (oddLt M).filter (fun p : ℕ => k ≤ p), (1 - 1/((p:ℝ)-1))⁻¹ := by
      rw [hfilt]
      exact Finset.prod_congr rfl hnu'
    have hstep2 : ∏ p ∈ (oddLt M).filter (fun p : ℕ => k ≤ p), (1 - 1/((p:ℝ)-1))⁻¹
        = oddProd (k-1)/oddProd (M-1) := by
      rw [sieveProd_eq_VsieveOdd_div M k hk2 hkM, ← oddProd_pred_eq_VsieveOdd M hM1,
        ← oddProd_pred_eq_VsieveOdd k (by omega)]
    have hbnd : oddProd (k-1)/oddProd (M-1)
        ≤ (Real.log (M:ℝ) / Real.log (k:ℝ)) * (1 + 100/Real.log (k:ℝ)) := by
      by_cases hk2049 : k ≤ 2049
      · exact oddProd_ratio_small Z₀ hZ₀ M k hMZ hM5 hk2 hk2049 hkM
      · exact oddProd_ratio_large M k (by omega) hkM
    calc ∏ p ∈ (oddLt M).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - (chenSieve x M).nu p)⁻¹
        = oddProd (k-1)/oddProd (M-1) := by rw [hstep1, hstep2]
      _ ≤ (Real.log (M:ℝ) / Real.log (k:ℝ)) * (1 + 100/Real.log (k:ℝ)) := hbnd
      _ ≤ (Real.log (M:ℝ) / Real.log w) * (1 + 100/Real.log w) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_left hLpos.le hwpos hlogwk
          · have h1 : 100/Real.log (k:ℝ) ≤ 100/Real.log w :=
              div_le_div_of_nonneg_left (by norm_num) hwpos hlogwk
            linarith [h1]
          · have h3 : (0:ℝ) ≤ 100/Real.log (k:ℝ) := div_nonneg (by norm_num) hkpos.le
            linarith [h3]
          · exact div_nonneg hLpos.le hwpos.le


end

end Work.ChenPlan.H1
