import Mathlib
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.Psi
import Submission.Work.HP.IntForm
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.HP2.ClassCountPrelude
import Submission.Work.HP.HP2.grid_coset_lower
import Submission.Work.HP.HP2.grid_coset_upper
import Submission.Work.HP.HP2.moebius_sieve_lower
import Submission.Work.HP.DNC.moebius_prim_ncard
import Submission.Work.HP.HP2.PF_eventually
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.tendsto_wOf_atTop
import Submission.Work.ClassCount.classPrimSet_moebius_eq
import Submission.Work.ClassCount.mobiusCount_eq_zero_of_not_coprime
import Submission.Work.ClassCount.tube_tail_eventually
import Submission.Work.ClassCount.mobiusCount_lower_bdd
import Submission.Work.ClassCount.mobiusCount_upper_bdd
import Submission.Work.ClassCount.mobiusCount_tail_le
import Submission.Work.ClassCount.sieve_bounds
import Submission.Work.ClassCount.tail_const_le

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators Pointwise



namespace Work.HP.HP2

theorem class_count_lower_pointwise (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (m : ℕ) (κ : ℝ) (hκ1 : 1 ≤ κ)
    (ccone : ℝ) (hccone : 0 < ccone)
    (hcone : ∀ (a : Work.HP.Mon d n → ℤ) (α R : ℝ),
      Work.HP.RealSol d n a → 1 ≤ α → 1 ≤ R →
      ccone * R ^ (n + 1) / α ^ n ≤
        (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal)
    (a : Work.HP.Mon d n → ℤ) (b : Fin (n + 1) → ℤ) (W : ℕ) (α R T₀ cstar : ℝ)
    (w : ℝ)
    (hW1 : 1 ≤ W) (hα1 : 1 ≤ α) (hR1 : 1 ≤ R)
    (hw4 : 4 ≤ w) (hWdiv : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ w → p ∣ W)
    (hT0eq : T₀ = (W : ℝ) * α ^ m * κ)
    (hT0R : T₀ ≤ R) (h2T0R : 2 * T₀ ≤ R)
    (hcstar : cstar = ccone ^ (1 / (n : ℝ))
      * ((n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n)) ^ (1 / (n : ℝ)))
    (hstrong : (W : ℝ) ^ ((2 * (n : ℝ) + 1) / n) * α ^ (m + 1) * κ ≤ R * cstar)
    (ha : a ≠ 0) (hsol : Work.HP.RealSol d n a)
    (hprim : ∀ p : ℕ, p.Prime → p ∣ W → ∃ i, ¬ (p : ℤ) ∣ b i)
    (hTube : ∀ T : ℝ, 1 ≤ T → T₀ ≤ T → Work.HP.TubeOk d n a α T (W : ℝ)) :
    (1 / 8) * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
        / (W : ℝ) ^ (n + 1)
      ≤ ((Work.HP.classPrimSet d n a b W α R).ncard : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hκpos : 0 < κ := by linarith
  have hWpos : 0 < W := by omega
  have hWpos' : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  have hW1' : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW1
  have hW2 : 2 ≤ W := by
    have := Nat.le_of_dvd hWpos (hWdiv 2 Nat.prime_two (by push_cast; linarith))
    linarith
  have hαpos : 0 < α := by linarith
  have hRpos : 0 < R := by linarith
  have hT0pos : 0 < T₀ := by rw [hT0eq]; positivity
  have h1αm : (1 : ℝ) ≤ α ^ m := one_le_pow₀ hα1
  have hT01 : 1 ≤ T₀ := by
    rw [hT0eq]
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ (W : ℝ) * α ^ m * κ := by gcongr
  have hnot0 : ¬ ∀ i, (W : ℤ) ∣ b i := not_forall_dvd_of_hprim W b hW2 hprim
  have hK0le : ⌊R / T₀⌋₊ ≤ ⌊R⌋₊ := by
    apply Nat.floor_mono
    rw [div_le_iff₀ hT0pos]
    nlinarith [hT01, hRpos]
  have hK1 : 1 ≤ R / T₀ := by
    rw [le_div_iff₀ hT0pos]
    linarith
  have hmain := Work.ClassCount.classPrimSet_moebius_eq d n a b W α R (le_of_lt hRpos)
  let V : ℝ := (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal / (W : ℝ) ^ (n + 1)
  have hVdef : V = (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal / (W : ℝ) ^ (n + 1) := rfl
  have hVnn : 0 ≤ V := by rw [hVdef]; positivity
  have hsieve := Work.ClassCount.sieve_bounds n hn2 w hw4 (R / T₀) hK1 W hWdiv
  -- termwise bound on the coprime part
  have hterm : ∀ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (V / (k : ℝ) ^ (n + 1)) - (V / (k : ℝ) ^ (n + 1)) / 2
        ≤ ((ArithmeticFunction.moebius k : ℤ) : ℝ)
            * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkK⟩, hcop⟩ := hk
    have hkR : (k : ℝ) ≤ R := by
      have hle : (k : ℝ) ≤ ((⌊R / T₀⌋₊ : ℕ) : ℝ) := by exact_mod_cast hkK
      have hK0R : ((⌊R / T₀⌋₊ : ℕ) : ℝ) ≤ R := by
        calc ((⌊R / T₀⌋₊ : ℕ) : ℝ) ≤ R / T₀ := Nat.floor_le (by positivity)
          _ ≤ R := by rw [div_le_iff₀ hT0pos]; nlinarith [hT01, hRpos]
      linarith
    have hkT : (k : ℝ) * T₀ ≤ R := by
      have hle : (k : ℝ) ≤ R / T₀ := by
        calc (k : ℝ) ≤ ((⌊R / T₀⌋₊ : ℕ) : ℝ) := by exact_mod_cast hkK
          _ ≤ R / T₀ := Nat.floor_le (by positivity)
      rw [le_div_iff₀ hT0pos] at hle
      linarith
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h1Rk : 1 ≤ R / (k : ℝ) := by
      rw [le_div_iff₀ hkpos]; linarith
    have hT0Rk : T₀ ≤ R / (k : ℝ) := by
      rw [le_div_iff₀ hkpos]; linarith
    have hTube' : Work.HP.TubeOk d n a α (R / (k : ℝ)) (W : ℝ) := hTube _ h1Rk hT0Rk
    have hlow := Work.ClassCount.mobiusCount_lower_bdd d n hd hdn a b W k α R T₀
      hWpos hk1 hα1 hR1 hcop hnot0 hT01 hkT hTube'
    have hup := Work.ClassCount.mobiusCount_upper_bdd d n hd hdn a b W k α R T₀
      hWpos hk1 hα1 hR1 hcop hnot0 hT01 hkT hTube'
    rw [mul_div_assoc] at hlow hup
    rw [← hVdef] at hlow hup
    have hMnn : 0 ≤ V / (k : ℝ) ^ (n + 1) := div_nonneg hVnn (by positivity)
    have hdiff : |((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) - V / (k : ℝ) ^ (n + 1)|
        ≤ (V / (k : ℝ) ^ (n + 1)) / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have habsμ : |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
      have h' : ((|ArithmeticFunction.moebius k| : ℤ) : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      rwa [Int.cast_abs] at h'
    have hab : ((ArithmeticFunction.moebius k : ℤ) : ℝ)
          * (((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) - V / (k : ℝ) ^ (n + 1))
        ≥ -(|((ArithmeticFunction.moebius k : ℤ) : ℝ)|
            * |((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) - V / (k : ℝ) ^ (n + 1)|) := by
      have h := neg_abs_le (((ArithmeticFunction.moebius k : ℤ) : ℝ)
        * (((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) - V / (k : ℝ) ^ (n + 1)))
      rwa [abs_mul] at h
    have hb : -(|((ArithmeticFunction.moebius k : ℤ) : ℝ)|
            * |((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) - V / (k : ℝ) ^ (n + 1)|)
        ≥ -(V / (k : ℝ) ^ (n + 1)) / 2 := by
      nlinarith [habsμ, hdiff,
        abs_nonneg (((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) - V / (k : ℝ) ^ (n + 1)),
        hMnn]
    nlinarith [hab, hb]
  -- sum over the coprime part
  have hsum1 : V / 4 ≤ ∑ k ∈ Finset.Icc 1 ⌊R / T₀⌋₊,
      ((ArithmeticFunction.moebius k : ℤ) : ℝ)
        * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := by
    have hfilter : ∑ k ∈ Finset.Icc 1 ⌊R / T₀⌋₊,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ)
          * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
        = ∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
        ((ArithmeticFunction.moebius k : ℤ) : ℝ)
          * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hc : Nat.Coprime k W
      · rw [if_pos hc]
      · rw [if_neg hc]
        have hz := Work.ClassCount.mobiusCount_eq_zero_of_not_coprime d n a b W k α R hW2 hprim hc
        rw [hz]
        norm_num
    rw [hfilter]
    have hstep : ∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) * (V / (k : ℝ) ^ (n + 1))
          - (V / (k : ℝ) ^ (n + 1)) / 2)
        ≤ ∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
        ((ArithmeticFunction.moebius k : ℤ) : ℝ)
          * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun k hk => hterm k hk)
    have hMk : ∀ k : ℕ, V / (k : ℝ) ^ (n + 1) = V * (k : ℝ) ^ (-((n : ℝ) + 1)) := by
      intro k
      rw [show (k : ℝ) ^ (-((n : ℝ) + 1)) = 1 / (k : ℝ) ^ (n + 1) from rpow_neg_succ_inv k n,
        mul_one_div]
    have hsplit : ∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) * (V / (k : ℝ) ^ (n + 1))
          - (V / (k : ℝ) ^ (n + 1)) / 2)
        = V * (∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
              ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (k : ℝ) ^ (-((n : ℝ) + 1)))
          - (V / 2) * (∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
              (k : ℝ) ^ (-((n : ℝ) + 1))) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [hMk k]
        ring
      · apply Finset.sum_congr rfl
        intro k hk
        rw [hMk k]
        ring
    rw [hsplit] at hstep
    have hs1 : 1 - 1 / 10 ≤ ∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (k : ℝ) ^ (-((n : ℝ) + 1)) := by
      have h0 : ((ArithmeticFunction.moebius 0 : ℤ) : ℝ) * (((0 : ℕ) : ℝ)) ^ (-((n : ℝ) + 1)) = 0 := by
        simp
      rw [← sum_range_filter_eq_sum_Icc (K := ⌊R / T₀⌋₊) (P := fun k => Nat.Coprime k W)
        (f := fun k => ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (k : ℝ) ^ (-((n : ℝ) + 1))) h0]
      exact hsieve.1
    have hs2 : ∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
        (k : ℝ) ^ (-((n : ℝ) + 1)) ≤ 13 / 10 := by
      have h0 : (((0 : ℕ) : ℝ)) ^ (-((n : ℝ) + 1)) = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow (show (-((n : ℝ) + 1)) ≠ 0 by linarith)]
      rw [← sum_range_filter_eq_sum_Icc (K := ⌊R / T₀⌋₊) (P := fun k => Nat.Coprime k W)
        (f := fun k => (k : ℝ) ^ (-((n : ℝ) + 1))) h0]
      exact hsieve.2
    have hS1 : V * (1 - 1 / 10) ≤ V * (∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter
        (fun k => Nat.Coprime k W), ((ArithmeticFunction.moebius k : ℤ) : ℝ)
          * (k : ℝ) ^ (-((n : ℝ) + 1))) := mul_le_mul_of_nonneg_left hs1 hVnn
    have hS2 : (V / 2) * (∑ k ∈ (Finset.Icc 1 ⌊R / T₀⌋₊).filter (fun k => Nat.Coprime k W),
          (k : ℝ) ^ (-((n : ℝ) + 1))) ≤ (V / 2) * (13 / 10) :=
      mul_le_mul_of_nonneg_left hs2 (by linarith)
    nlinarith [hstep, hS1, hS2]
  -- tail
  have htail : ∑ k ∈ Finset.Icc (⌊R / T₀⌋₊ + 1) ⌊R⌋₊,
      ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
      ≤ (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n * R * T₀ ^ n / (n : ℝ) :=
    Work.ClassCount.mobiusCount_tail_le d n hn1 a b W α R T₀ (le_of_lt hRpos) hT0pos h2T0R
  have htailbound : (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n * R * T₀ ^ n / (n : ℝ) ≤ V / 8 := by
    have hconst := Work.ClassCount.tail_const_le n hn1 m (W : ℝ) α R T₀ ccone cstar κ
      hWpos' hαpos hRpos hccone hκpos hT0eq hcstar hstrong
    have hcone' := hcone a α R hsol hα1 hR1
    have hVlb : ccone * R ^ (n + 1) / (α ^ n * (W : ℝ) ^ (n + 1)) ≤ V := by
      rw [hVdef]
      calc ccone * R ^ (n + 1) / (α ^ n * (W : ℝ) ^ (n + 1))
          = (ccone * R ^ (n + 1) / α ^ n) / (W : ℝ) ^ (n + 1) := by rw [div_div]
        _ ≤ (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal / (W : ℝ) ^ (n + 1) :=
            div_le_div_of_nonneg_right hcone' (by positivity)
    have h8 : ccone * R ^ (n + 1) / (8 * α ^ n * (W : ℝ) ^ (n + 1))
        = (1 / 8) * (ccone * R ^ (n + 1) / (α ^ n * (W : ℝ) ^ (n + 1))) := by
      field_simp
    have hV8 : (1 / 8) * V = V / 8 := by ring
    have hstep : (1 / 8) * (ccone * R ^ (n + 1) / (α ^ n * (W : ℝ) ^ (n + 1))) ≤ (1 / 8) * V :=
      mul_le_mul_of_nonneg_left hVlb (by norm_num)
    linarith [hconst, h8.le, hstep, hV8]
  have hSum2 : -(V / 8) ≤ ∑ k ∈ Finset.Icc (⌊R / T₀⌋₊ + 1) ⌊R⌋₊,
      ((ArithmeticFunction.moebius k : ℤ) : ℝ)
        * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := by
    have h1 : -(∑ k ∈ Finset.Icc (⌊R / T₀⌋₊ + 1) ⌊R⌋₊,
          ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.Icc (⌊R / T₀⌋₊ + 1) ⌊R⌋₊,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ)
            * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro k hk
      have hμ : (-1 : ℝ) ≤ ((ArithmeticFunction.moebius k : ℤ) : ℝ) := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := k)
        have h2 : ((-1 : ℤ)) ≤ ArithmeticFunction.moebius k := (abs_le.mp h).1
        exact_mod_cast h2
      have hmc : (0 : ℝ) ≤ ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hμ, hmc]
    linarith [h1, htail, htailbound]
  rw [mul_div_assoc]
  rw [← hVdef]
  rw [hmain]
  have hsplit := sum_Icc_split (a := 1) (b := ⌊R⌋₊) (c := ⌊R / T₀⌋₊) (by omega) hK0le
    (fun k => ((ArithmeticFunction.moebius k : ℤ) : ℝ)
      * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ))
  rw [hsplit]
  linarith [hsum1, hSum2]

end Work.HP.HP2

namespace Work.HP.HP2

theorem class_count_lower (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (m : ℕ) (κ : ℝ) (hκ : 1 ≤ κ)
    (ccone : ℝ) (hccone : 0 < ccone)
    (hcone : ∀ (a : Work.HP.Mon d n → ℤ) (α R : ℝ),
      Work.HP.RealSol d n a → 1 ≤ α → 1 ≤ R →
      ccone * R ^ (n + 1) / α ^ n ≤
        (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal) :
    ∀ᶠ B in atTop, ∀ (a : Work.HP.Mon d n → ℤ) (b : Fin (n + 1) → ℤ),
      a ≠ 0 → Work.HP.RealSol d n a →
      (∀ i, 0 ≤ b i ∧ b i < Work.HP.bigW (Work.HP.wOf B)) →
      (∀ p : ℕ, p.Prime → p ∣ Work.HP.bigW (Work.HP.wOf B) → ∃ i, ¬ (p : ℤ) ∣ b i) →
      ((Work.HP.bigW (Work.HP.wOf B) : ℤ) ∣ Work.HP.formEval d n a b) →
      (∀ T : ℝ, 1 ≤ T →
        (Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ ≤ T →
        Work.HP.TubeOk d n a (Real.log B) T (Work.HP.bigW (Work.HP.wOf B) : ℝ)) →
      (1 / 8) * (MeasureTheory.volume (Work.HP.coneRegion d n a (Real.log B)
          (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
        / (Work.HP.bigW (Work.HP.wOf B) : ℝ) ^ (n + 1)
        ≤ ((Work.HP.classPrimSet d n a b (Work.HP.bigW (Work.HP.wOf B)) (Real.log B)
            (B ^ (1 / ((n : ℝ) + 1 - d)))).ncard : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hκpos : 0 < κ := by linarith
  have hκ2pos : 0 < 2 * κ := by linarith
  set cstar : ℝ := ccone ^ (1 / (n : ℝ))
      * ((n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n)) ^ (1 / (n : ℝ)) with hcstar
  have hcstarpos : 0 < cstar := by
    rw [hcstar]
    exact mul_pos (Real.rpow_pos_of_pos hccone _) (Real.rpow_pos_of_pos (by positivity) _)
  have hE1 := Work.HP.HP2.PF_eventually d n hdn m κ hκpos
  have hE2 := Work.HP.tendsto_wOf_atTop.eventually_ge_atTop 4
  have hE4 := Work.HP.HP2.PF_eventually d n hdn m (2 * κ) hκ2pos
  have hE5 := Work.ClassCount.tube_tail_eventually d n hdn hn1 m κ cstar hκpos hcstarpos
  filter_upwards [hE1, hE2, hE4, hE5] with B hB1 hB2 hB4 hB5
  obtain ⟨hlog1, hB1'⟩ := hB1
  intro a b ha hsol hbox hprim hf hTube
  have hW1 : 1 ≤ Work.HP.bigW (Work.HP.wOf B) := Work.HP.one_le_bigW _
  have hW1' : (1 : ℝ) ≤ (Work.HP.bigW (Work.HP.wOf B) : ℝ) := by exact_mod_cast hW1
  have hαm1 : (1 : ℝ) ≤ (Real.log B) ^ m := one_le_pow₀ hlog1
  have hT01 : (1 : ℝ) ≤ (Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ := by
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ (Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ := by gcongr
  have hR1 : 1 ≤ B ^ (1 / ((n : ℝ) + 1 - d)) := le_trans hT01 hB1'
  have h2T0R : 2 * ((Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ)
      ≤ B ^ (1 / ((n : ℝ) + 1 - d)) := by
    have hrearr : (Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * (2 * κ)
        = 2 * ((Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ) := by ring
    linarith [hrearr, hB4]
  exact class_count_lower_pointwise d n hd hdn m κ hκ ccone hccone hcone
    a b (Work.HP.bigW (Work.HP.wOf B)) (Real.log B) (B ^ (1 / ((n : ℝ) + 1 - d)))
    ((Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ) cstar (Work.HP.wOf B)
    hW1 hlog1 hR1 hB2 (fun p hp hple => Work.HP.prime_dvd_bigW hp hple)
    rfl hB1' h2T0R hcstar hB5 ha hsol hprim hTube

end Work.HP.HP2
