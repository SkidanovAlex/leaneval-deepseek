import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.averaging_bound
import Submission.Work.BMF.holder_box
import Submission.Work.BMF.VU.exp_taylor_real
import Submission.Work.BMF.VU.arcind_box
import Submission.Work.BMF.VU.nu_integrals
import Submission.Work.BMF.VU.core_sum_bound_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private lemma eC_eq' (t : ℝ) : eC t = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  unfold eC
  congr 1
  push_cast
  ring

private lemma norm_eC' (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC_eq']
  exact Complex.norm_exp_ofReal_mul_I _

set_option maxHeartbeats 1000000 in
/-- **V1a (fixed 20:30). Vinogradov's reduction with a `k`-explicit constant `exp(C₀k³)`.**
Fixes against the first version: the derivative hypotheses range over **real**
`x ∈ (0, N+1)` (before, `Set.Ioo 0 N` elaborated over `ℕ`, so the condition was imposed only at
integers and the statement was false), and the constant is the more generous `exp(C₀ k³)`. -/
theorem kth_derivative_reduction_uniform :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (k : ℕ), 2 ≤ k → ∀ (N : ℕ) (f : ℝ → ℝ) (lam A H M : ℝ) (s : ℕ),
      1 ≤ N → 0 < lam → 1 ≤ A → A * lam ≤ 1 / 4 → 0 < H →
      H = (A * lam) ^ (-(1 / (k : ℝ))) →
      1 ≤ s →
      ContDiffOn ℝ k f (Set.Ioo (0 : ℝ) ((N : ℝ) + 1)) →
      (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) →
        lam ≤ iteratedDeriv k f x ∧ iteratedDeriv k f x ≤ A * lam) →
      (∀ x : ℝ, 0 ≤ x → x ≤ H →
        (∫ α in (Set.pi Set.univ (fun _ : Fin (k - 1) => Set.Icc (0:ℝ) 1)),
            ‖∑ h ∈ Finset.Icc 1 ⌊x⌋₊,
               Complex.exp ((2 * Real.pi * (∑ j : Fin (k-1), α j * (h:ℝ) ^ ((j:ℕ)+1)) : ℝ) *
                 Complex.I)‖ ^ (2 * (s:ℝ))) ≤ M) →
      ‖∑ n ∈ Finset.Icc 1 N, Complex.exp ((↑(2 * Real.pi * f (n : ℝ)) : ℂ) * Complex.I)‖
        ≤ Real.exp (C₀ * (k : ℝ) ^ 3) * (H + (k:ℝ)^2 * (N:ℝ)^(1 - 1/(s:ℝ))
            * (((Set.ncard {mn : ℕ × ℕ | mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N ∧
                  ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 →
                    ∃ z : ℤ, |iteratedDeriv j f (mn.1 : ℝ) / (Nat.factorial j : ℝ)
                      - iteratedDeriv j f (mn.2 : ℝ) / (Nat.factorial j : ℝ) - (z : ℝ)|
                      ≤ 2 * H ^ (-(j : ℝ))} : ℕ) : ℝ) ^ (1/(2*(s:ℝ))))
            * ((H ^ (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2)) * M) ^ (1/(2*(s:ℝ)))) := by
  obtain ⟨Ccore, hCcore1, hCcore⟩ := core_sum_bound_uniform
  refine ⟨Ccore + 1, by linarith [hCcore1], ?_⟩
  intro k hk N f lam A H M s hN hlam hA hAq hHpos hHdef hs hf hfder hM
  have hEpos : 0 < Real.exp (Ccore * (k:ℝ)^3) := Real.exp_pos _
  have hE1 : (1:ℝ) ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) :=
    Real.one_le_exp (mul_nonneg (by linarith [hCcore1]) (by positivity))
  rw [show (∑ n ∈ Finset.Icc 1 N, Complex.exp ((↑(2 * Real.pi * f (n : ℝ)) : ℂ) * Complex.I))
      = ∑ n ∈ Finset.Icc 1 N, eC (f (n:ℝ)) from
        Finset.sum_congr rfl (fun n _ => (eC_eq' (f (n:ℝ))).symm)]
  change ‖∑ n ∈ Finset.Icc 1 N, eC (f (n:ℝ))‖ ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) *
    (H + (k:ℝ)^2 * (N:ℝ)^(1 - 1/(s:ℝ)) * (((Nset k N f H).ncard : ℕ) : ℝ) ^ (1/(2*(s:ℝ)))
      * ((H ^ (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2)) * M) ^ (1/(2*(s:ℝ))))
  set A2 : ℝ := (N:ℝ)^(1 - 1/(s:ℝ)) with hA2
  set B2 : ℝ := (((Nset k N f H).ncard : ℕ) : ℝ) ^ (1/(2*(s:ℝ))) with hB2
  set HE : ℝ := (H ^ (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2) * M) ^ (1/(2*(s:ℝ))) with hHE
  set A1 : ℝ := ((N - ⌊H⌋₊ : ℕ) : ℝ) ^ (1 - 1/(s:ℝ)) with hA1
  set B1 : ℝ := (((Nset k (N - ⌊H⌋₊) f H).ncard : ℕ) : ℝ) ^ (1/(2*(s:ℝ))) with hB1
  set Ha : ℝ := H ^ ((k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ))) with hHa
  set Md : ℝ := M ^ (1/(2*(s:ℝ))) with hMd
  set BB : ℝ := (k:ℝ)^2 * A2 * B2 * HE with hBB
  change ‖∑ n ∈ Finset.Icc 1 N, eC (f (n:ℝ))‖ ≤
    Real.exp ((Ccore + 1) * (k:ℝ)^3) * (H + BB)
  set A1 : ℝ := ((N - ⌊H⌋₊ : ℕ) : ℝ) ^ (1 - 1/(s:ℝ)) with hA1
  set B1 : ℝ := (((Nset k (N - ⌊H⌋₊) f H).ncard : ℕ) : ℝ) ^ (1/(2*(s:ℝ))) with hB1
  set Ha : ℝ := H ^ ((k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ))) with hHa
  set Md : ℝ := M ^ (1/(2*(s:ℝ))) with hMd
  set XX : ℝ := Real.exp (Ccore * (k:ℝ)^3) * A1 * B1 * Ha * Md with hXX
  clear_value A2 B2 HE BB A1 B1 Ha Md XX
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA
  have hAlam_pos : 0 < A * lam := mul_pos hApos hlam
  have hH1 : 1 ≤ H := by
    rw [hHdef, Real.rpow_neg (le_of_lt hAlam_pos), one_le_inv₀ (Real.rpow_pos_of_pos hAlam_pos _)]
    exact Real.rpow_le_one (le_of_lt hAlam_pos) (by linarith only [hAq]) (by positivity)
  have hAlam_eq : A * lam = H ^ (-(k:ℝ)) := by
    have h1 : H ^ (k : ℝ) = (A * lam)⁻¹ := by
      rw [hHdef, ← Real.rpow_mul (le_of_lt hAlam_pos)]
      have hmul : -(1/(k:ℝ)) * (k:ℝ) = -1 := by
        have hk0 : ((k:ℝ)) ≠ 0 := by positivity
        field_simp
      rw [hmul, Real.rpow_neg_one]
    rw [Real.rpow_neg (le_of_lt hHpos), h1, inv_inv]
  have hL1 : 1 ≤ ⌊H⌋₊ := Nat.le_floor (by exact_mod_cast hH1)
  have hLleH : ((⌊H⌋₊ : ℕ) : ℝ) ≤ H := Nat.floor_le (le_of_lt hHpos)
  have hLpos : (0:ℝ) < ((⌊H⌋₊ : ℕ) : ℝ) := by exact_mod_cast hL1
  have hHhalf : H / 2 ≤ ((⌊H⌋₊ : ℕ) : ℝ) := by
    have hlt : H < ((⌊H⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one H
    by_cases h : 2 ≤ H
    · linarith only [hlt, h]
    · have h1 : (1:ℝ) ≤ ((⌊H⌋₊ : ℕ) : ℝ) := by exact_mod_cast hL1
      linarith only [hlt, h, h1]
  have hM0 : 0 ≤ M := by
    have h0 := hM 0 (le_refl 0) (by linarith)
    have hz : (0:ℝ) ≤ (∫ α in (Set.pi Set.univ (fun _ : Fin (k-1) => Set.Icc (0:ℝ) 1)),
        ‖∑ h ∈ Finset.Icc 1 ⌊(0:ℝ)⌋₊, Complex.exp ((2 * Real.pi * (∑ j : Fin (k-1), α j * (h:ℝ) ^ ((j:ℕ)+1)) : ℝ) * Complex.I)‖ ^ (2*(s:ℝ))) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards with α
      positivity
    linarith only [hz, h0]
  have hAnn : (0:ℝ) ≤ A1 := by rw [hA1]; exact Real.rpow_nonneg (by positivity) _
  have hBnn : (0:ℝ) ≤ B1 := by rw [hB1]; exact Real.rpow_nonneg (by positivity) _
  have hA2nn : (0:ℝ) ≤ A2 := by rw [hA2]; exact Real.rpow_nonneg (by positivity) _
  have hB2nn : (0:ℝ) ≤ B2 := by rw [hB2]; exact Real.rpow_nonneg (by positivity) _
  have hHann : (0:ℝ) ≤ Ha := by rw [hHa]; exact Real.rpow_nonneg (le_of_lt hHpos) _
  have hMdn : (0:ℝ) ≤ Md := by rw [hMd]; exact Real.rpow_nonneg hM0 _
  have hHEnn : (0:ℝ) ≤ HE := by
    rw [hHE]
    have h3 : (0:ℝ) ≤ H ^ (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2) := Real.rpow_nonneg (le_of_lt hHpos) _
    exact Real.rpow_nonneg (mul_nonneg h3 hM0) _
  have hBBnn : (0:ℝ) ≤ BB := by rw [hBB]; positivity
  have hXXnn : (0:ℝ) ≤ XX := by rw [hXX]; positivity
  have hC1 : (1:ℝ) ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) := hE1
  by_cases htriv : N ≤ ⌊H⌋₊
  · have hS : ‖∑ n ∈ Finset.Icc 1 N, eC (f (n:ℝ))‖ ≤ (N:ℝ) := by
      have hcard : (Finset.Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
      have h2 : (∑ n ∈ Finset.Icc 1 N, ‖eC (f (n:ℝ))‖) = (N:ℝ) := by
        rw [show (∑ n ∈ Finset.Icc 1 N, ‖eC (f (n:ℝ))‖) = ∑ n ∈ Finset.Icc 1 N, (1:ℝ) from
              Finset.sum_congr rfl (fun n _ => norm_eC (f (n:ℝ))),
            Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
      exact (norm_sum_le (Finset.Icc 1 N) (fun n => eC (f (n:ℝ)))).trans (le_of_eq h2)
    have hNH : (N:ℝ) ≤ H := by
      have h2 : (N:ℝ) ≤ ((⌊H⌋₊ : ℕ) : ℝ) := by exact_mod_cast htriv
      linarith
    have hC1' : (0:ℝ) ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) := by linarith [hC1]
    have h2 : H ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * H := by nlinarith only [hC1, hHpos]
    have h3 : (0:ℝ) ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * BB := mul_nonneg hC1' hBBnn
    calc ‖∑ n ∈ Finset.Icc 1 N, eC (f (n:ℝ))‖ ≤ (N:ℝ) := hS
      _ ≤ H := hNH
      _ ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * (H + BB) := by
          calc H = H + 0 := by ring
            _ ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * H
                  + Real.exp ((Ccore + 1) * (k:ℝ)^3) * BB := add_le_add h2 h3
            _ = Real.exp ((Ccore + 1) * (k:ℝ)^3) * (H + BB) := by ring
  · push_neg at htriv
    have hhard : ⌊H⌋₊ < N := htriv
    have hLN : ⌊H⌋₊ ≤ N := le_of_lt hhard
    have hM' : ∀ x : ℝ, 0 ≤ x → x ≤ H →
        (∫ α in unitBox (k-1), ‖polySum (k-1) α x‖ ^ (2*(s:ℝ))) ≤ M := by
      intro x hx0 hxH
      have h := hM x hx0 hxH
      have hpe : ∀ α : Fin (k-1) → ℝ, polySum (k-1) α x
          = ∑ h ∈ Finset.Icc 1 ⌊x⌋₊, Complex.exp ((↑(2 * Real.pi * (∑ j : Fin (k-1), α j * (h:ℝ) ^ ((j:ℕ)+1)) : ℝ) : ℂ) * Complex.I) := by
        intro α
        unfold polySum phase
        exact Finset.sum_congr rfl (fun h _ => eC_eq' _)
      have hset : (∫ α in unitBox (k-1), ‖polySum (k-1) α x‖ ^ (2*(s:ℝ)))
          = ∫ α in (Set.pi Set.univ (fun _ : Fin (k-1) => Set.Icc (0:ℝ) 1)),
              ‖∑ h ∈ Finset.Icc 1 ⌊x⌋₊, Complex.exp ((↑(2 * Real.pi * (∑ j : Fin (k-1), α j * (h:ℝ) ^ ((j:ℕ)+1)) : ℝ) : ℂ) * Complex.I)‖ ^ (2*(s:ℝ)) := by
        simp only [unitBox]
        refine setIntegral_congr_fun (MeasurableSet.pi (Set.Finite.countable Set.finite_univ)
          (fun _ _ => measurableSet_Icc)) ?_
        intro α _
        change ‖polySum (k-1) α x‖ ^ (2*(s:ℝ))
          = ‖∑ h ∈ Finset.Icc 1 ⌊x⌋₊, Complex.exp ((↑(2 * Real.pi * (∑ j : Fin (k-1), α j * (h:ℝ) ^ ((j:ℕ)+1)) : ℝ) : ℂ) * Complex.I)‖ ^ (2*(s:ℝ))
        rw [hpe α]
      rw [hset]; exact h
    have hX := hCcore k hk N f H M s hhard hs hH1 hM'
    set av : ℕ → Fin (k-1) → ℝ := fun n j =>
      iteratedDeriv ((j:ℕ)+1) f (n:ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) with hav
    have hX' : ∀ y : ℝ, 0 ≤ y → y ≤ (⌊H⌋₊ : ℝ) →
        (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊), ‖polySum (k-1) (av n) y‖) ≤ XX := by
      intro y hy0 hyL
      rw [hXX, hA1, hB1, hHa, hMd]
      simpa only [hav] using hX y hy0 hyL
    have havg := averaging_bound hL1 hLN (fun n => eC (f (n:ℝ))) (fun n => (norm_eC _).le)
    have hSub : Finset.Icc 1 (N - ⌊H⌋₊ - 1) ⊆ Finset.Icc 1 (N - ⌊H⌋₊) := by
      intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
    have hLast : ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f (((N - ⌊H⌋₊)+h:ℕ):ℝ))‖ ≤ (⌊H⌋₊ : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [show (∑ h ∈ Finset.Icc 1 ⌊H⌋₊, ‖eC (f (((N - ⌊H⌋₊)+h:ℕ):ℝ))‖) = ∑ h ∈ Finset.Icc 1 ⌊H⌋₊, (1:ℝ) from
            Finset.sum_congr rfl (fun h _ => norm_eC' _),
          Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp
    have hper : ∀ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1),
        ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f ((n+h:ℕ):ℝ))‖ ≤
          ‖polySum (k-1) (av n) (⌊H⌋₊:ℝ)‖
          + 2*Real.pi*H⁻¹*∑ h ∈ Finset.range ⌊H⌋₊, ‖polySum (k-1) (av n) (h:ℝ)‖ := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hnL : n + ⌊H⌋₊ < N := by omega
      have hf' : ContDiffOn ℝ k f (Set.Ioo (0:ℝ) (((N+1 : ℕ)) : ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hf
      have hder' : ∀ y ∈ Set.Ioo (0:ℝ) (((N+1 : ℕ)) : ℝ), ‖iteratedDeriv k f y‖ ≤ A * lam := by
        intro y hy
        have hy' : y ∈ Set.Ioo (0:ℝ) ((N:ℝ) + 1) := by simpa only [Nat.cast_add, Nat.cast_one] using hy
        have h1 : lam ≤ iteratedDeriv k f y := (hfder y hy').1
        have h2 : iteratedDeriv k f y ≤ A * lam := (hfder y hy').2
        rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hlam h1)]
        exact h2
      have hnL' : n + ⌊H⌋₊ < N + 1 := by omega
      have hres := exp_sum_taylor_abel_bound_real k hk hHpos hAlam_eq.le (le_of_lt hAlam_pos)
        hf' hder' hn.1 hnL' hLleH
      simpa only [hav] using hres
    have hA1le : (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1), ‖polySum (k-1) (av n) (⌊H⌋₊:ℝ)‖) ≤ XX :=
      (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun i _ _ => norm_nonneg _)).trans
        (hX' (⌊H⌋₊:ℝ) (by positivity) le_rfl)
    have hA2le : (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1),
          ∑ h ∈ Finset.range ⌊H⌋₊, ‖polySum (k-1) (av n) (h:ℝ)‖) ≤ (⌊H⌋₊:ℝ) * XX := by
      rw [Finset.sum_comm]
      calc (∑ h ∈ Finset.range ⌊H⌋₊, ∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1),
              ‖polySum (k-1) (av n) (h:ℝ)‖)
          ≤ ∑ h ∈ Finset.range ⌊H⌋₊, XX := by
            refine Finset.sum_le_sum (fun h hh => ?_)
            rw [Finset.mem_range] at hh
            exact (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun i _ _ => norm_nonneg _)).trans
              (hX' (h:ℝ) (by positivity) (by exact_mod_cast (le_of_lt hh)))
        _ = (⌊H⌋₊:ℝ) * XX := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hRest : (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1), ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f ((n+h:ℕ):ℝ))‖)
        ≤ (1 + 2*Real.pi) * XX := by
      have hsum1 : (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1), ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f ((n+h:ℕ):ℝ))‖)
          ≤ XX + 2*Real.pi*H⁻¹*((⌊H⌋₊:ℝ) * XX) := by
        calc (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1), ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f ((n+h:ℕ):ℝ))‖)
            ≤ ∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1), (‖polySum (k-1) (av n) (⌊H⌋₊:ℝ)‖
                + 2*Real.pi*H⁻¹*∑ h ∈ Finset.range ⌊H⌋₊, ‖polySum (k-1) (av n) (h:ℝ)‖) :=
              Finset.sum_le_sum hper
          _ = (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1), ‖polySum (k-1) (av n) (⌊H⌋₊:ℝ)‖)
                + 2*Real.pi*H⁻¹*(∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1),
                    ∑ h ∈ Finset.range ⌊H⌋₊, ‖polySum (k-1) (av n) (h:ℝ)‖) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ XX + 2*Real.pi*H⁻¹*((⌊H⌋₊:ℝ) * XX) := by
              have h3 : (0:ℝ) ≤ 2 * Real.pi * H⁻¹ := by positivity
              exact add_le_add hA1le (mul_le_mul_of_nonneg_left hA2le h3)
      have h4 : H⁻¹ * (⌊H⌋₊ : ℝ) ≤ 1 := by
        rw [inv_mul_le_iff₀ hHpos]; linarith only [hLleH]
      have h5 : (0:ℝ) ≤ 2*Real.pi := by positivity
      have h7 : H⁻¹ * ((⌊H⌋₊:ℝ) * XX) ≤ XX := by
        have := mul_le_mul_of_nonneg_right h4 hXXnn
        simpa [mul_assoc] using this
      refine hsum1.trans ?_
      calc XX + 2*Real.pi*H⁻¹*((⌊H⌋₊:ℝ) * XX)
          = XX + 2*Real.pi*(H⁻¹*((⌊H⌋₊:ℝ) * XX)) := by ring
        _ ≤ XX + 2*Real.pi*XX := add_le_add_right (mul_le_mul_of_nonneg_left h7 h5) XX
        _ = (1 + 2*Real.pi) * XX := by ring
    have hsum : (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊), ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f ((n+h:ℕ):ℝ))‖)
        ≤ (1 + 2*Real.pi) * XX + (⌊H⌋₊ : ℝ) := by
      have hsplit : (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊), ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f ((n+h:ℕ):ℝ))‖)
          ≤ (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊ - 1), ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f ((n+h:ℕ):ℝ))‖)
            + ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f (((N - ⌊H⌋₊)+h:ℕ):ℝ))‖ := by
        have hunion : Finset.Icc 1 (N - ⌊H⌋₊) = Finset.Icc 1 (N - ⌊H⌋₊ - 1) ∪ {N - ⌊H⌋₊} := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
        have hdisj : Disjoint (Finset.Icc 1 (N - ⌊H⌋₊ - 1)) ({N - ⌊H⌋₊} : Finset ℕ) := by
          rw [Finset.disjoint_left]; intro x hx hxs
          simp only [Finset.mem_singleton] at hxs
          simp only [Finset.mem_Icc] at hx
          omega
        rw [hunion, Finset.sum_union hdisj, Finset.sum_singleton]
      exact hsplit.trans (add_le_add hRest hLast)
    have hHinv : ((⌊H⌋₊ : ℝ))⁻¹ ≤ 2 * H⁻¹ := by
      rw [show (2:ℝ) * H⁻¹ = (H/2)⁻¹ from by rw [inv_div]; ring]
      exact (inv_le_inv₀ hLpos (by positivity)).mpr hHhalf
    have hstep1 : A1 ≤ A2 := by
      rw [hA1, hA2]
      have hNL : (((N - ⌊H⌋₊ : ℕ) : ℝ)) ≤ (N:ℝ) := by
        have hh : (N - ⌊H⌋₊ : ℕ) ≤ N := Nat.sub_le _ _
        exact_mod_cast hh
      have he1 : (0:ℝ) ≤ 1 - 1/(s:ℝ) := by
        have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
        have hs0 : (0:ℝ) < (s:ℝ) := by positivity
        rw [sub_nonneg, div_le_one hs0]; exact hs1
      exact Real.rpow_le_rpow (by positivity) hNL he1
    have hstep2 : B1 ≤ B2 := by
      rw [hB1, hB2]
      have hfin : (Nset k N f H).Finite := by
        refine (Set.finite_Icc (1:ℕ) N).prod (Set.finite_Icc (1:ℕ) N) |>.subset ?_
        intro p hp
        simp only [Nset, Set.mem_setOf_eq, Finset.mem_Icc] at hp
        exact ⟨⟨hp.1.1, hp.1.2⟩, ⟨hp.2.1.1, hp.2.1.2⟩⟩
      have hNc : (((Nset k (N - ⌊H⌋₊) f H).ncard : ℕ) : ℝ) ≤ (((Nset k N f H).ncard : ℕ) : ℝ) := by
        have hsub : Nset k (N - ⌊H⌋₊) f H ⊆ Nset k N f H := by
          intro p hp
          simp only [Nset, Set.mem_setOf_eq] at hp ⊢
          exact ⟨Finset.Icc_subset_Icc_right (Nat.sub_le _ _) hp.1,
                 Finset.Icc_subset_Icc_right (Nat.sub_le _ _) hp.2.1, hp.2.2⟩
        exact_mod_cast Set.ncard_le_ncard hsub hfin
      exact Real.rpow_le_rpow (by positivity) hNc (by positivity)
    have hId : Ha * Md = H * HE := by
      rw [hHa, hMd, hHE]
      have hexp : 1 + (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2) * (1/(2*(s:ℝ)))
          = (k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ)) := by
        have hA2e : (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2) * (1/(2*(s:ℝ)))
            = -1 + (k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ)) := by
          field_simp
          ring
        rw [hA2e]; ring
      calc H ^ ((k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ))) * M ^ (1/(2*(s:ℝ)))
          = H ^ (1 + (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2) * (1/(2*(s:ℝ)))) * M ^ (1/(2*(s:ℝ))) := by
              rw [hexp]
        _ = (H * H ^ ((-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2) * (1/(2*(s:ℝ))))) * M ^ (1/(2*(s:ℝ))) := by
              rw [Real.rpow_add hHpos, Real.rpow_one]
        _ = H * (H ^ ((-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2) * (1/(2*(s:ℝ)))) * M ^ (1/(2*(s:ℝ)))) := by
              ring
        _ = H * ((H ^ (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2)) ^ (1/(2*(s:ℝ))) * M ^ (1/(2*(s:ℝ)))) := by
              rw [Real.rpow_mul (le_of_lt hHpos)]
        _ = H * (H ^ (-(2*(s:ℝ)) + (k:ℝ)*((k:ℝ)-1)/2) * M) ^ (1/(2*(s:ℝ))) := by
              rw [Real.mul_rpow (le_of_lt (Real.rpow_pos_of_pos hHpos _)) hM0]
    have hXXB : XX ≤ H * (Real.exp (Ccore * (k:ℝ)^3) * BB) := by
      rw [hXX, hBB]
      have hAB : A1 * B1 ≤ A2 * B2 := mul_le_mul hstep1 hstep2 hBnn hA2nn
      have hk2 : (1:ℝ) ≤ (k:ℝ)^2 := by
        have h2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        nlinarith
      have hABE : 0 ≤ A2 * B2 * HE := by positivity
      calc Real.exp (Ccore * (k:ℝ)^3) * A1 * B1 * Ha * Md
          = Real.exp (Ccore * (k:ℝ)^3) * (A1 * B1) * (Ha * Md) := by ring
        _ ≤ Real.exp (Ccore * (k:ℝ)^3) * (A2 * B2) * (H * HE) := by
              rw [hId]
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAB (by positivity)) (by positivity)
        _ = H * (Real.exp (Ccore * (k:ℝ)^3) * (A2 * B2 * HE)) := by ring
        _ ≤ H * (Real.exp (Ccore * (k:ℝ)^3) * ((k:ℝ)^2 * (A2 * B2 * HE))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hABE hk2) hEpos.le) (by positivity)
        _ = H * (Real.exp (Ccore * (k:ℝ)^3) * ((k:ℝ)^2 * A2 * B2 * HE)) := by ring
    have hkey : ((⌊H⌋₊ : ℝ))⁻¹ * ((1 + 2*Real.pi) * XX + (⌊H⌋₊ : ℝ)) + 2 * (⌊H⌋₊ : ℝ)
        ≤ 2*(1 + 2*Real.pi) * (Real.exp (Ccore * (k:ℝ)^3) * BB) + 3 * H := by
      have h1 : ((⌊H⌋₊ : ℝ))⁻¹ * ((1 + 2*Real.pi) * XX + (⌊H⌋₊ : ℝ))
          = ((⌊H⌋₊ : ℝ))⁻¹ * ((1 + 2*Real.pi) * XX) + 1 := by
        rw [mul_add, inv_mul_cancel₀ (ne_of_gt hLpos)]
      rw [h1]
      have h2 : ((⌊H⌋₊ : ℝ))⁻¹ * ((1 + 2*Real.pi) * XX) ≤ 2*H⁻¹ * ((1 + 2*Real.pi) * XX) :=
        mul_le_mul_of_nonneg_right hHinv (by positivity)
      have h3 : H⁻¹ * XX ≤ Real.exp (Ccore * (k:ℝ)^3) * BB := by
        have hb := mul_le_mul_of_nonneg_left hXXB (le_of_lt (inv_pos.mpr hHpos))
        calc H⁻¹ * XX ≤ H⁻¹ * (H * (Real.exp (Ccore * (k:ℝ)^3) * BB)) := hb
          _ = Real.exp (Ccore * (k:ℝ)^3) * BB := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hHpos), one_mul]
      have h4 : 2*H⁻¹ * ((1 + 2*Real.pi) * XX) ≤ 2*(1 + 2*Real.pi) * (Real.exp (Ccore * (k:ℝ)^3) * BB) := by
        have heq : 2*H⁻¹ * ((1 + 2*Real.pi) * XX) = 2*(1 + 2*Real.pi) * (H⁻¹ * XX) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : (1:ℝ) + 2*(⌊H⌋₊ : ℝ) ≤ 3*H := by linarith only [hLleH, hH1]
      linarith only [h2, h4, h5]
    have hfinal2 : 2*(1 + 2*Real.pi) * (Real.exp (Ccore * (k:ℝ)^3) * BB) + 3 * H
        ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * (H + BB) := by
      have hsmall : (2 * (1 + 2*Real.pi)) ≤ Real.exp ((k:ℝ)^3) := by
        have h1 : (2:ℝ) * (1 + 2 * Real.pi) ≤ 2 * (1 + 8) := by nlinarith [Real.pi_lt_four]
        have h2 : (2:ℝ) * (1 + 8) ≤ (18:ℝ) := by norm_num
        have h3 : (18:ℝ) ≤ (2:ℝ)^(k^3) := by
          calc (18:ℝ) ≤ 64 := by norm_num
            _ = 2^6 := by norm_num
            _ ≤ 2^(k^3) := by
              refine pow_le_pow_right₀ (by norm_num) ?_
              have h2 : 4 ≤ k^2 := by nlinarith
              calc 6 ≤ 2 * 4 := by norm_num
                _ ≤ 2 * k^2 := Nat.mul_le_mul_left 2 h2
                _ ≤ k * k^2 := Nat.mul_le_mul_right (k^2) hk
                _ = k^3 := by ring
        have h4 : (2:ℝ)^(k^3) ≤ Real.exp 1 ^ (k^3) :=
          pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le (k^3)
        have h5 : Real.exp 1 ^ (k^3) = Real.exp ((k:ℝ)^3) := by
          rw [← Real.exp_nat_mul, mul_one, Nat.cast_pow]
        linarith [h1, h2, h3, h4, h5.le, h5.ge]
      have hexpadd : Real.exp (Ccore * (k:ℝ)^3) * Real.exp ((k:ℝ)^3)
          = Real.exp ((Ccore + 1) * (k:ℝ)^3) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h1 : 2 * (1 + 2*Real.pi) * (Real.exp (Ccore * (k:ℝ)^3) * BB)
          ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * BB := by
        calc 2 * (1 + 2*Real.pi) * (Real.exp (Ccore * (k:ℝ)^3) * BB)
            = ((2 * (1 + 2*Real.pi)) * Real.exp (Ccore * (k:ℝ)^3)) * BB := by ring
          _ ≤ (Real.exp ((k:ℝ)^3) * Real.exp (Ccore * (k:ℝ)^3)) * BB :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le) hBBnn
          _ = Real.exp ((Ccore + 1) * (k:ℝ)^3) * BB := by
              rw [mul_comm (Real.exp ((k:ℝ)^3)), hexpadd]
      have h2 : 3*H ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * H := by
        refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hHpos)
        have hkR2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        have hk3 : (1:ℝ) ≤ (k:ℝ)^3 := by nlinarith
        have hx2 : (2:ℝ) ≤ (Ccore + 1) * (k:ℝ)^3 := by nlinarith [hCcore1, hk3]
        exact le_trans (by linarith : (3:ℝ) ≤ (Ccore + 1) * (k:ℝ)^3 + 1) (Real.add_one_le_exp _)
      calc 2*(1 + 2*Real.pi) * (Real.exp (Ccore * (k:ℝ)^3) * BB) + 3 * H
          ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * BB + Real.exp ((Ccore + 1) * (k:ℝ)^3) * H :=
            add_le_add h1 h2
        _ = Real.exp ((Ccore + 1) * (k:ℝ)^3) * (H + BB) := by ring
    calc ‖∑ n ∈ Finset.Icc 1 N, eC (f (n:ℝ))‖
        ≤ ((⌊H⌋₊ : ℝ))⁻¹ * ((1 + 2*Real.pi) * XX + (⌊H⌋₊ : ℝ)) + 2 * (⌊H⌋₊ : ℝ) := by
          have hA : ((⌊H⌋₊ : ℝ))⁻¹ * (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊), ‖∑ h ∈ Finset.Icc 1 ⌊H⌋₊, eC (f ((n+h:ℕ):ℝ))‖)
              ≤ ((⌊H⌋₊ : ℝ))⁻¹ * ((1 + 2*Real.pi) * XX + (⌊H⌋₊ : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hLpos))
          linarith only [havg, hA]
      _ ≤ Real.exp ((Ccore + 1) * (k:ℝ)^3) * (H + BB) := hkey.trans hfinal2


end Work.BMF
