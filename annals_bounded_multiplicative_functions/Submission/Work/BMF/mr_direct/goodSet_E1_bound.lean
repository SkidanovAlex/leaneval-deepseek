import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.buchstab_decomp
import Submission.Work.BMF.mv_sharp_dirichlet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary lemmas for `goodSet_E1_bound` -/

lemma norm_inv_natCast_le_one {k : ℕ} (hk : 1 ≤ k) : ‖(((k : ℕ)) : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_natCast]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)

/-- `t ↦ n^{-(1+it)}` is continuous for `n ≥ 1`. -/
lemma continuous_cpow_neg_one_sub {n : ℕ} (hn : 1 ≤ n) :
    Continuous fun t : ℝ => (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  have hfun : (fun t : ℝ => (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = fun t : ℝ => (n : ℂ)⁻¹ *
          Complex.exp (Complex.I * (((-(Real.log (n : ℝ)) : ℝ) : ℂ) * (t : ℂ))) := by
    funext t
    exact Work.BMF.cpow_neg_one_sub_I n hn t
  rw [hfun]
  fun_prop

lemma continuous_primePoly (c : ℕ → ℂ) (K : ℝ) (j : ℕ) :
    Continuous fun t : ℝ => mrDirect.primePoly c K j t := by
  unfold mrDirect.primePoly
  refine continuous_finsetSum _ fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact Continuous.mul continuous_const (continuous_cpow_neg_one_sub hp.2.one_le)

lemma continuous_remPoly (b : ℕ → ℂ) (P Q K X : ℝ) (j : ℕ) (hX : 0 < X) :
    Continuous fun t : ℝ => mrDirect.remPoly b P Q K X j t := by
  unfold mrDirect.remPoly
  refine continuous_finsetSum _ fun m hm => ?_
  have hm1 : 1 ≤ m := by
    have hmem := Finset.mem_Icc.mp hm
    have h1 : 1 ≤ ⌈X * Real.exp (-((j : ℝ) + 1) / K)⌉₊ :=
      Nat.ceil_pos.mpr (mul_pos hX (Real.exp_pos _))
    omega
  exact Continuous.mul (Continuous.mul continuous_const continuous_const)
    (continuous_cpow_neg_one_sub hm1)

/-! ### Separation of the frequencies `-log m` in a window -/

lemma log_sep_lt {A B : ℝ} (hA : 0 < A) {m n : ℕ}
    (hm : m ∈ Work.BMF.natIcc A B) (hn : n ∈ Work.BMF.natIcc A B) (hlt : m < n) :
    1 / (B + 1) ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
  rw [Work.BMF.natIcc, Finset.mem_Icc] at hm hn
  have hcA : 1 ≤ ⌈A⌉₊ := Nat.ceil_pos.mpr hA
  have hm1 : 1 ≤ m := le_trans hcA hm.1
  have hn1 : 1 ≤ n := le_trans hm1 (le_of_lt hlt)
  have hB1 : 1 ≤ B := (Nat.one_le_floor_iff B).mp (le_trans hm1 hm.2)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have h1 : Real.log (m : ℝ) - Real.log (n : ℝ) ≤ (m : ℝ) / (n : ℝ) - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) / (n : ℝ) by positivity)
    rwa [Real.log_div hmpos.ne' hnpos.ne'] at this
  have h2 : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
    have h' : ((m : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
    linarith
  have h3 : (1 : ℝ) / (n : ℝ) ≤ ((n : ℝ) - (m : ℝ)) / (n : ℝ) :=
    div_le_div_of_nonneg_right h2 hnpos.le
  have h4 : ((n : ℝ) - (m : ℝ)) / (n : ℝ) = 1 - (m : ℝ) / (n : ℝ) := by
    field_simp
  have h5 : (1 : ℝ) / (n : ℝ) ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
    rw [h4] at h3
    linarith
  have h7 : (n : ℝ) ≤ B + 1 := by
    have h8 : (n : ℝ) ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast hn.2
    have h9 : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le (by linarith : (0:ℝ) ≤ B)
    linarith
  have := one_div_le_one_div_of_le hnpos h7
  linarith

lemma log_sep_natIcc {A B : ℝ} (hA : 0 < A) {m n : ℕ}
    (hm : m ∈ Work.BMF.natIcc A B) (hn : n ∈ Work.BMF.natIcc A B) (hmn : m ≠ n) :
    1 / (B + 1) ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  rcases lt_trichotomy m n with hlt | heq | hgt
  · have h1 := log_sep_lt hA hm hn hlt
    have h2 : Real.log (m : ℝ) < Real.log (n : ℝ) := by
      apply Real.log_lt_log <;> [skip; exact_mod_cast hlt]
      rw [Work.BMF.natIcc, Finset.mem_Icc] at hm
      have := Nat.ceil_pos.mpr hA
      exact_mod_cast (by omega : 1 ≤ m)
    rw [abs_of_neg (by linarith : Real.log (↑m) - Real.log (↑n) < 0)]
    linarith
  · exact absurd heq hmn
  · have h1 := log_sep_lt hA hn hm hgt
    have h2 : Real.log (n : ℝ) < Real.log (m : ℝ) := by
      apply Real.log_lt_log <;> [skip; exact_mod_cast hgt]
      rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
      have := Nat.ceil_pos.mpr hA
      exact_mod_cast (by omega : 1 ≤ n)
    rw [abs_of_pos (by linarith : 0 < Real.log (↑m) - Real.log (↑n))]
    linarith

/-! ### The mean-value (large sieve) bound for one window -/

lemma window_mean_value :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A B S : ℝ) (a : ℕ → ℂ), 0 < A → 0 ≤ S →
        (∫ t in (-S)..S,
            ‖∑ m ∈ Work.BMF.natIcc A B, a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
          ≤ C * (2 * S + (B + 1)) *
              ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  refine ⟨2 * C₀ + 1, by positivity, ?_⟩
  intro A B S a hA hS
  by_cases hB : 0 < B + 1
  · set N := (Work.BMF.natIcc A B).card with hN
    set e : ↥(Work.BMF.natIcc A B) ≃ Fin N := Finset.equivFin _ with he
    set b : Fin N → ℂ := fun i =>
      a ((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ) /
        (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ) : ℂ) with hb
    set μ : Fin N → ℝ := fun i =>
      -(Real.log (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ)) with hmu
    have hδ : 0 < 1 / (B + 1) := by positivity
    have hm1 : ∀ x : ↥(Work.BMF.natIcc A B), 1 ≤ ((x : ℕ)) := by
      intro x
      have hmem := Finset.mem_Icc.mp x.2
      have h1 : 1 ≤ ⌈A⌉₊ := Nat.ceil_pos.mpr hA
      omega
    have hsep : ∀ i j : Fin N, i ≠ j → 1 / (B + 1) ≤ |μ i - μ j| := by
      intro i j hij
      have hne : (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) ≠
          (((e.symm j : ↥(Work.BMF.natIcc A B)) : ℕ)) := by
        intro h'
        exact hij (e.symm.injective (Subtype.coe_injective h'))
      have hi : (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) ∈ Work.BMF.natIcc A B :=
        (e.symm i).2
      have hj : (((e.symm j : ↥(Work.BMF.natIcc A B)) : ℕ)) ∈ Work.BMF.natIcc A B :=
        (e.symm j).2
      have hkey := log_sep_natIcc hA hi hj hne
      rw [hmu]
      simp only []
      rw [show -(Real.log (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ))
          - -(Real.log (((e.symm j : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ))
          = Real.log (((e.symm j : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ)
            - Real.log (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ) by ring, abs_sub_comm]
      exact hkey
    have hsum_eq : ∀ t : ℝ,
        (∑ m ∈ Work.BMF.natIcc A B, a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
          = ∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ))) := by
      intro t
      rw [← Finset.sum_attach (Work.BMF.natIcc A B)
            (fun m => a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))),
        ← Finset.univ_eq_attach (Work.BMF.natIcc A B)]
      rw [← Equiv.sum_comp e.symm (fun x : ↥(Work.BMF.natIcc A B) =>
            a ((x : ℕ)) * (((x : ℕ)) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hb, hmu]
      rw [Work.BMF.cpow_neg_one_sub_I _ (hm1 (e.symm i)) t]
      ring
    have hint : (∫ t in (-S)..S,
          ‖∑ m ∈ Work.BMF.natIcc A B, a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        = ∫ t in (-S)..S,
            ‖∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      exact congrArg (fun z => ‖z‖ ^ 2) (hsum_eq t)
    have hS2 : (∑ i : Fin N, ‖b i‖ ^ 2)
        = ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2 := by
      rw [← Equiv.sum_comp e (fun i : Fin N => ‖b i‖ ^ 2)]
      have h1 : ∀ x : ↥(Work.BMF.natIcc A B),
          ‖b (e x)‖ ^ 2 = ‖a ((x : ℕ)) / (((x : ℕ)) : ℂ)‖ ^ 2 := by
        intro x; simp only [hb]; rw [Equiv.symm_apply_apply]
      simp only [h1]
      rw [← Finset.sum_attach (Work.BMF.natIcc A B) (fun n => ‖a n‖ ^ 2 / (n : ℝ) ^ 2)]
      rw [Finset.univ_eq_attach]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [norm_div, Complex.norm_natCast, div_pow]
    have hls := hC₀ (1 / (B + 1)) hδ N μ b hsep (-S) S (by linarith)
    have hcoef : S - (-S) + C₀ / (1 / (B + 1)) = 2 * S + C₀ * (B + 1) := by
      rw [one_div, div_inv_eq_mul]; ring
    have hmain : (∫ t in (-S)..S,
          ‖∑ m ∈ Work.BMF.natIcc A B, a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        ≤ (2 * S + C₀ * (B + 1)) *
            ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2 := by
      calc (∫ t in (-S)..S,
            ‖∑ m ∈ Work.BMF.natIcc A B, a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
          = ∫ t in (-S)..S,
              ‖∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2 := hint
        _ ≤ (S - (-S) + C₀ / (1 / (B + 1))) * ∑ i : Fin N, ‖b i‖ ^ 2 := hls
        _ = (2 * S + C₀ * (B + 1)) *
              ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2 := by
            rw [hcoef, hS2]
    have hsum_nonneg : 0 ≤ ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2 :=
      Finset.sum_nonneg fun m _ => by positivity
    calc (∫ t in (-S)..S,
          ‖∑ m ∈ Work.BMF.natIcc A B, a m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        ≤ (2 * S + C₀ * (B + 1)) *
            ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2 := hmain
      _ ≤ (2 * C₀ + 1) * (2 * S + (B + 1)) *
            ∑ m ∈ Work.BMF.natIcc A B, ‖a m‖ ^ 2 / (m : ℝ) ^ 2 := by
          have h1 : 2 * S + C₀ * (B + 1) ≤ (2 * C₀ + 1) * (2 * S + (B + 1)) := by
            nlinarith [hS, hB, hC₀pos]
          exact mul_le_mul_of_nonneg_right h1 hsum_nonneg
  · -- the window is empty
    have hempty : Work.BMF.natIcc A B = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      have hmem := Finset.mem_Icc.mp hm
      have h1 : 1 ≤ ⌈A⌉₊ := Nat.ceil_pos.mpr hA
      have h2 : ⌊B⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
      intervalIntegral.integral_zero]
    ring_nf
    norm_num

/-! ### Harmonic bounds for the windows -/

lemma sum_Icc_inv_sub_inv_succ (N M : ℕ) (hNM : N ≤ M) :
    (∑ m ∈ Finset.Icc N M, ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1)))
      = 1 / (N : ℝ) - 1 / ((M : ℝ) + 1) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (f := fun m => (1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1))
        (by omega), ih]
      push_cast
      ring

lemma sum_Icc_inv_sq_le (N M : ℕ) (hN : 1 ≤ N) :
    (∑ m ∈ Finset.Icc N M, (1 : ℝ) / (m : ℝ) ^ 2) ≤ 2 / (N : ℝ) := by
  by_cases hNM : N ≤ M
  · have hpt : ∀ m ∈ Finset.Icc N M,
        (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 * ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_trans hN hm.1)
      have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
      have hm1' : (0 : ℝ) < (m : ℝ) + 1 := by linarith
      rw [mul_sub, mul_one_div, mul_one_div]
      field_simp
      nlinarith [hm1]
    calc (∑ m ∈ Finset.Icc N M, (1 : ℝ) / (m : ℝ) ^ 2)
        ≤ ∑ m ∈ Finset.Icc N M, 2 * ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1)) :=
          Finset.sum_le_sum hpt
      _ = 2 * (1 / (N : ℝ) - 1 / ((M : ℝ) + 1)) := by
          rw [← Finset.mul_sum, sum_Icc_inv_sub_inv_succ N M hNM]
      _ ≤ 2 / (N : ℝ) := by
          have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
          have : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
          have h2 : 2 * (1 / (N : ℝ)) = 2 / (N : ℝ) := by ring
          linarith
  · have hempty : Finset.Icc N M = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      rw [Finset.mem_Icc] at hm
      omega
    rw [hempty, Finset.sum_empty]
    positivity

lemma natIcc_inv_sq_sum_le (A B : ℝ) (hA : 0 < A) :
    (∑ m ∈ Work.BMF.natIcc A B, (1 : ℝ) / (m : ℝ) ^ 2) ≤ 2 / A := by
  have hc : 1 ≤ ⌈A⌉₊ := Nat.ceil_pos.mpr hA
  have hAc : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have h1 : (∑ m ∈ Work.BMF.natIcc A B, (1 : ℝ) / (m : ℝ) ^ 2)
      = ∑ m ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, (1 : ℝ) / (m : ℝ) ^ 2 := rfl
  rw [h1]
  refine le_trans (sum_Icc_inv_sq_le ⌈A⌉₊ ⌊B⌋₊ hc) ?_
  exact div_le_div_of_nonneg_left (by norm_num) hA hAc

lemma winIdx_inv_sq_le (X K : ℝ) (j : ℕ) (hX : 1 ≤ X) :
    (∑ m ∈ mrDirect.winIdx K X j, (1 : ℝ) / (m : ℝ) ^ 2)
      ≤ 2 * Real.exp (((j : ℝ) + 1) / K) / X := by
  have hXpos : 0 < X := by linarith
  have hA : 0 < X * Real.exp (-((j : ℝ) + 1) / K) :=
    mul_pos hXpos (Real.exp_pos _)
  have h := natIcc_inv_sq_sum_le (X * Real.exp (-((j : ℝ) + 1) / K))
    (2 * X * Real.exp (-(j : ℝ) / K)) hA
  have heq : 2 / (X * Real.exp (-((j : ℝ) + 1) / K))
      = 2 * Real.exp (((j : ℝ) + 1) / K) / X := by
    rw [show -((j : ℝ) + 1) / K = -(((j : ℝ) + 1) / K) by ring]
    rw [Real.exp_neg]
    field_simp
  rw [heq] at h
  exact h

lemma winIdx_inv_sq_le_two (X K : ℝ) (j : ℕ) (hX : 0 < X) :
    (∑ m ∈ mrDirect.winIdx K X j, (1 : ℝ) / (m : ℝ) ^ 2) ≤ 2 := by
  have hA : 0 < X * Real.exp (-((j : ℝ) + 1) / K) :=
    mul_pos hX (Real.exp_pos _)
  have hc : 1 ≤ ⌈X * Real.exp (-((j : ℝ) + 1) / K)⌉₊ := Nat.ceil_pos.mpr hA
  have h1 := sum_Icc_inv_sq_le ⌈X * Real.exp (-((j : ℝ) + 1) / K)⌉₊
    ⌊2 * X * Real.exp (-(j : ℝ) / K)⌋₊ hc
  have h2 : (∑ m ∈ mrDirect.winIdx K X j, (1 : ℝ) / (m : ℝ) ^ 2)
      = ∑ m ∈ Finset.Icc ⌈X * Real.exp (-((j : ℝ) + 1) / K)⌉₊
          ⌊2 * X * Real.exp (-(j : ℝ) / K)⌋₊, (1 : ℝ) / (m : ℝ) ^ 2 := rfl
  rw [h2]
  refine le_trans h1 ?_
  rw [div_le_iff₀ (by exact_mod_cast hc : (0:ℝ) < (⌈X * Real.exp (-((j : ℝ) + 1) / K)⌉₊ : ℕ))]
  have : (1 : ℝ) ≤ (⌈X * Real.exp (-((j : ℝ) + 1) / K)⌉₊ : ℝ) := by exact_mod_cast hc
  linarith

/-! ### Crude geometric sums over `indexSet` -/

lemma indexSet_exp_neg_sum_le (K P Q α : ℝ) (hK : 3 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hα0 : 0 < α) (hα1 : α ≤ 1 / 4) :
    (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)))
      ≤ 3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2) := by
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hLP : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hLQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hLPQ : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPpos]; linarith
  set N : ℕ := ⌊K * Real.log P⌋₊ with hN
  set M : ℕ := ⌊K * Real.log Q⌋₊ with hM
  have hidx : mrDirect.indexSet K P Q = Finset.Icc N M := rfl
  have hNlow : K * Real.log P - 1 < (N : ℝ) := by
    have h := Nat.lt_floor_add_one (K * Real.log P)
    rw [hN]; linarith
  have hcount : ((M + 1 - N : ℕ) : ℝ) ≤ K * Real.log (Q / P) + 2 := by
    by_cases h : N ≤ M + 1
    · have h1 : ((M + 1 - N : ℕ) : ℝ) = (M : ℝ) + 1 - (N : ℝ) := by
        rw [Nat.cast_sub h]; push_cast; ring
      have h2 : (M : ℝ) ≤ K * Real.log Q := by
        have h3 : ((⌊K * Real.log Q⌋₊ : ℕ) : ℝ) ≤ K * Real.log Q :=
          Nat.floor_le (mul_nonneg hKpos.le (Real.log_nonneg (by linarith)))
        rw [hM]; exact h3
      have h4 : Real.log (Q / P) = Real.log Q - Real.log P :=
        Real.log_div hQpos.ne' hPpos.ne'
      rw [h4, h1]; linarith
    · have h1 : M + 1 - N = 0 := by omega
      rw [h1]
      simp only [Nat.cast_zero]
      nlinarith [hLPQ, hK]
  have hpt : ∀ j ∈ Finset.Icc N M,
      Real.exp (-(2 * α * (j : ℝ) / K)) ≤ Real.exp (-(2 * α * (N : ℝ) / K)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    apply Real.exp_le_exp.mpr
    have h1 : 2 * α * (N : ℝ) / K = (2 * α / K) * (N : ℝ) := by ring
    have h2 : 2 * α * (j : ℝ) / K = (2 * α / K) * (j : ℝ) := by ring
    have h3 : (2 * α / K) * (N : ℝ) ≤ (2 * α / K) * (j : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hj.1) (by positivity)
    linarith
  have hstep : (∑ j ∈ Finset.Icc N M, Real.exp (-(2 * α * (j : ℝ) / K)))
      ≤ (K * Real.log (Q / P) + 2) * Real.exp (-(2 * α * (K * Real.log P - 1) / K)) := by
    calc (∑ j ∈ Finset.Icc N M, Real.exp (-(2 * α * (j : ℝ) / K)))
        ≤ ∑ _j ∈ Finset.Icc N M, Real.exp (-(2 * α * (N : ℝ) / K)) := Finset.sum_le_sum hpt
      _ = ((Finset.Icc N M).card : ℝ) * Real.exp (-(2 * α * (N : ℝ) / K)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((M + 1 - N : ℕ) : ℝ) * Real.exp (-(2 * α * (N : ℝ) / K)) := by
          rw [Nat.card_Icc]
      _ ≤ (K * Real.log (Q / P) + 2) * Real.exp (-(2 * α * (N : ℝ) / K)) :=
          mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
      _ ≤ (K * Real.log (Q / P) + 2) *
            Real.exp (-(2 * α * (K * Real.log P - 1) / K)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply Real.exp_le_exp.mpr
          have h1 : 2 * α * (N : ℝ) / K = (2 * α / K) * (N : ℝ) := by ring
          have h2 : 2 * α * (K * Real.log P - 1) / K = (2 * α / K) * (K * Real.log P - 1) := by ring
          have h3 : (2 * α / K) * (K * Real.log P - 1) ≤ (2 * α / K) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left (le_of_lt hNlow) (by positivity)
          linarith
  have hexp : Real.exp (-(2 * α * (K * Real.log P - 1) / K))
      = P ^ (-(2 * α)) * Real.exp (2 * α / K) := by
    rw [show -(2 * α * (K * Real.log P - 1) / K)
        = (-(2 * α)) * Real.log P + 2 * α / K by field_simp; ring]
    rw [Real.exp_add, Real.rpow_def_of_pos hPpos]
    ring_nf
  have hexp3 : Real.exp (2 * α / K) ≤ 3 := by
    calc Real.exp (2 * α / K) ≤ Real.exp 1 := by
          apply Real.exp_le_exp.mpr
          rw [div_le_one hKpos]
          linarith
      _ ≤ 3 := le_of_lt Real.exp_one_lt_three
  calc (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)))
      = ∑ j ∈ Finset.Icc N M, Real.exp (-(2 * α * (j : ℝ) / K)) := by rw [hidx]
    _ ≤ (K * Real.log (Q / P) + 2) * Real.exp (-(2 * α * (K * Real.log P - 1) / K)) := hstep
    _ = (K * Real.log (Q / P) + 2) * (P ^ (-(2 * α)) * Real.exp (2 * α / K)) := by rw [hexp]
    _ ≤ (K * Real.log (Q / P) + 2) * (P ^ (-(2 * α)) * 3) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_left hexp3 (Real.rpow_pos_of_pos hPpos _).le
    _ = 3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2) := by ring

lemma indexSet_exp_pos_sum_le (K P Q α : ℝ) (hK : 3 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hα0 : 0 < α) (hα1 : α ≤ 1 / 4) :
    (∑ j ∈ mrDirect.indexSet K P Q, Real.exp ((1 - 2 * α) * (j : ℝ) / K))
      ≤ 3 * Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2) := by
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hLPQ : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPpos]; linarith
  set N : ℕ := ⌊K * Real.log P⌋₊ with hN
  set M : ℕ := ⌊K * Real.log Q⌋₊ with hM
  have hidx : mrDirect.indexSet K P Q = Finset.Icc N M := rfl
  have hc1 : 0 ≤ 1 - 2 * α := by linarith
  have hcount : ((M + 1 - N : ℕ) : ℝ) ≤ K * Real.log (Q / P) + 2 := by
    by_cases h : N ≤ M + 1
    · have h1 : ((M + 1 - N : ℕ) : ℝ) = (M : ℝ) + 1 - (N : ℝ) := by
        rw [Nat.cast_sub h]; push_cast; ring
      have h2 : (M : ℝ) ≤ K * Real.log Q := by
        have h3 : ((⌊K * Real.log Q⌋₊ : ℕ) : ℝ) ≤ K * Real.log Q :=
          Nat.floor_le (mul_nonneg hKpos.le (Real.log_nonneg (by linarith)))
        rw [hM]; exact h3
      have h3 : K * Real.log P - 1 < (N : ℝ) := by
        have h5 := Nat.lt_floor_add_one (K * Real.log P)
        rw [hN]; linarith
      have h4 : Real.log (Q / P) = Real.log Q - Real.log P :=
        Real.log_div hQpos.ne' hPpos.ne'
      rw [h4, h1]; linarith
    · have h1 : M + 1 - N = 0 := by omega
      rw [h1]
      simp only [Nat.cast_zero]
      nlinarith [hLPQ, hK]
  have hMup : (M : ℝ) ≤ K * Real.log Q := by
    have h3 : ((⌊K * Real.log Q⌋₊ : ℕ) : ℝ) ≤ K * Real.log Q :=
      Nat.floor_le (mul_nonneg hKpos.le (Real.log_nonneg (by linarith)))
    rw [hM]; exact h3
  have hpt : ∀ j ∈ Finset.Icc N M,
      Real.exp ((1 - 2 * α) * (j : ℝ) / K) ≤ Real.exp ((1 - 2 * α) * (M : ℝ) / K) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hKpos.le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj.2) hc1
  have hstep : (∑ j ∈ Finset.Icc N M, Real.exp ((1 - 2 * α) * (j : ℝ) / K))
      ≤ (K * Real.log (Q / P) + 2) * Real.exp ((1 - 2 * α) * (M : ℝ) / K) := by
    calc (∑ j ∈ Finset.Icc N M, Real.exp ((1 - 2 * α) * (j : ℝ) / K))
        ≤ ∑ _j ∈ Finset.Icc N M, Real.exp ((1 - 2 * α) * (M : ℝ) / K) := Finset.sum_le_sum hpt
      _ = ((Finset.Icc N M).card : ℝ) * Real.exp ((1 - 2 * α) * (M : ℝ) / K) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((M + 1 - N : ℕ) : ℝ) * Real.exp ((1 - 2 * α) * (M : ℝ) / K) := by
          rw [Nat.card_Icc]
      _ ≤ (K * Real.log (Q / P) + 2) * Real.exp ((1 - 2 * α) * (M : ℝ) / K) :=
          mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
  have hmexp : Real.exp ((1 - 2 * α) * (M : ℝ) / K) ≤ Q ^ (1 - 2 * α) := by
    rw [Real.rpow_def_of_pos hQpos]
    apply Real.exp_le_exp.mpr
    have h3 : (1 - 2 * α) * (M : ℝ) ≤ (1 - 2 * α) * (K * Real.log Q) :=
      mul_le_mul_of_nonneg_left hMup hc1
    have h5 : (1 - 2 * α) * (K * Real.log Q) / K = (1 - 2 * α) * Real.log Q := by
      field_simp
    calc (1 - 2 * α) * (M : ℝ) / K ≤ (1 - 2 * α) * (K * Real.log Q) / K :=
          div_le_div_of_nonneg_right h3 hKpos.le
      _ = Real.log Q * (1 - 2 * α) := by rw [h5, mul_comm]
  calc (∑ j ∈ mrDirect.indexSet K P Q, Real.exp ((1 - 2 * α) * (j : ℝ) / K))
      = ∑ j ∈ Finset.Icc N M, Real.exp ((1 - 2 * α) * (j : ℝ) / K) := by rw [hidx]
    _ ≤ (K * Real.log (Q / P) + 2) * Real.exp ((1 - 2 * α) * (M : ℝ) / K) := hstep
    _ ≤ (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) * 3) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        calc Real.exp ((1 - 2 * α) * (M : ℝ) / K) ≤ Q ^ (1 - 2 * α) := hmexp
          _ ≤ Q ^ (1 - 2 * α) * 3 := by
              have h2 : (0:ℝ) < Q ^ (1 - 2 * α) := Real.rpow_pos_of_pos hQpos _
              linarith
    _ = 3 * Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2) := by ring


theorem goodSet_E1_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X K P Q S α : ℝ) (b c : ℕ → ℂ),
        1 ≤ X → 3 ≤ K → 2 ≤ P → P ≤ Q → 0 ≤ S → 0 < α → α ≤ 1 / 4 →
        (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
        (∀ t : ℝ, ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          ‖Work.BMF.mrDirect.primePoly c K j t‖ ≤ Real.exp (-(α * (j : ℝ) / K))) →
        K * Real.log (Q / P) *
          (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
            ∫ t in (-S)..S,
              ‖Work.BMF.mrDirect.primePoly c K j t *
                Work.BMF.mrDirect.remPoly b P Q K X j t‖ ^ 2)
        ≤ C * (1 + 1 / α) * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 *
            (S / X * Q ^ (1 - 2 * α) + P ^ (-(2 * α))) := by
  obtain ⟨C_W, hCWpos, hCW⟩ := window_mean_value
  refine ⟨100 * (C_W + 1), by positivity, ?_⟩
  intro X K P Q S α b c hX hK hP hPQ hS hα0 hα1 hb hc hgood
  have hXpos : 0 < X := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hLnn : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPpos]; linarith
  have hppnn : 0 ≤ P ^ (-(2 * α)) := (Real.rpow_pos_of_pos hPpos _).le
  have hqqnn : 0 ≤ Q ^ (1 - 2 * α) / X :=
    div_nonneg (Real.rpow_nonneg hQpos.le _) hXpos.le
  set E : ℕ → ℝ := fun j => ∑ m ∈ mrDirect.winIdx K X j,
      ‖b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ^ 2 / (m : ℝ) ^ 2 with hEdef
  have hEnn : ∀ j, 0 ≤ E j := by
    intro j; rw [hEdef]; exact Finset.sum_nonneg fun m _ => by positivity
  -- (1) the coefficient sum is at most the plain harmonic window sum
  have hEle : ∀ j, E j ≤ ∑ m ∈ mrDirect.winIdx K X j, (1 : ℝ) / (m : ℝ) ^ 2 := by
    intro j
    rw [hEdef]
    apply Finset.sum_le_sum
    intro m hm
    have hcoef : ‖b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ≤ 1 := by
      have hb1 : ‖b m‖ ≤ 1 := hb m
      have h2 : 1 ≤ mrDirect.omegaCount P Q m + 1 := by omega
      have h3 : ‖((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ≤ 1 :=
        norm_inv_natCast_le_one h2
      calc ‖b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖
          = ‖b m‖ * ‖((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ := norm_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hb1 h3 (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    have h4 : ‖b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ^ 2 ≤ 1 := by
      have h5 := norm_nonneg (b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹)
      nlinarith [hcoef, h5]
    calc ‖b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ^ 2 / (m : ℝ) ^ 2
        ≤ 1 / (m : ℝ) ^ 2 := div_le_div_of_nonneg_right h4 (by positivity)
      _ = 1 / (m : ℝ) ^ 2 := rfl
  -- (2) per-j bound: pointwise decay of `primePoly` + mean value bound for `remPoly`
  have hperj : ∀ j ∈ mrDirect.indexSet K P Q,
      (∫ t in (-S)..S, ‖mrDirect.primePoly c K j t * mrDirect.remPoly b P Q K X j t‖ ^ 2)
        ≤ C_W * (2 * S + (2 * X * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * E j) := by
    intro j hj
    have hcontQ : Continuous fun t : ℝ => mrDirect.primePoly c K j t := continuous_primePoly c K j
    have hcontR : Continuous fun t : ℝ => mrDirect.remPoly b P Q K X j t :=
      continuous_remPoly b P Q K X j hXpos
    have hcont1 : Continuous fun t : ℝ =>
        ‖mrDirect.primePoly c K j t * mrDirect.remPoly b P Q K X j t‖ ^ 2 :=
      (hcontQ.mul hcontR).norm.pow 2
    have hcont2 : Continuous fun t : ℝ =>
        Real.exp (-(2 * α * (j : ℝ) / K)) * ‖mrDirect.remPoly b P Q K X j t‖ ^ 2 :=
      continuous_const.mul (hcontR.norm.pow 2)
    have hpt : ∀ t : ℝ, ‖mrDirect.primePoly c K j t * mrDirect.remPoly b P Q K X j t‖ ^ 2
        ≤ Real.exp (-(2 * α * (j : ℝ) / K)) * ‖mrDirect.remPoly b P Q K X j t‖ ^ 2 := by
      intro t
      have hq := hgood t j hj
      have hq2 : ‖mrDirect.primePoly c K j t‖ ^ 2 ≤ Real.exp (-(2 * α * (j : ℝ) / K)) := by
        have h1 : Real.exp (-(α * (j : ℝ) / K)) ^ 2 = Real.exp (-(2 * α * (j : ℝ) / K)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        calc ‖mrDirect.primePoly c K j t‖ ^ 2 ≤ Real.exp (-(α * (j : ℝ) / K)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hq 2
          _ = Real.exp (-(2 * α * (j : ℝ) / K)) := h1
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right hq2 (by positivity)
    have hmono : (∫ t in (-S)..S,
          ‖mrDirect.primePoly c K j t * mrDirect.remPoly b P Q K X j t‖ ^ 2)
        ≤ ∫ t in (-S)..S,
            Real.exp (-(2 * α * (j : ℝ) / K)) * ‖mrDirect.remPoly b P Q K X j t‖ ^ 2 :=
      intervalIntegral.integral_mono (by linarith) (hcont1.intervalIntegrable _ _)
        (hcont2.intervalIntegrable _ _) (fun t => hpt t)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hmv := hCW (X * Real.exp (-((j : ℝ) + 1) / K)) (2 * X * Real.exp (-(j : ℝ) / K)) S
      (fun m => b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹)
      (mul_pos hXpos (Real.exp_pos _)) hS
    have hrew : (∫ t in (-S)..S, ‖mrDirect.remPoly b P Q K X j t‖ ^ 2)
        = ∫ t in (-S)..S,
            ‖∑ m ∈ Work.BMF.natIcc (X * Real.exp (-((j : ℝ) + 1) / K))
                (2 * X * Real.exp (-(j : ℝ) / K)),
              b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹ *
                (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
      have hfun : (fun t : ℝ => ‖mrDirect.remPoly b P Q K X j t‖ ^ 2)
          = fun t : ℝ =>
              ‖∑ m ∈ Work.BMF.natIcc (X * Real.exp (-((j : ℝ) + 1) / K))
                  (2 * X * Real.exp (-(j : ℝ) / K)),
                b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹ *
                  (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
        funext t
        rw [show mrDirect.remPoly b P Q K X j t
            = ∑ m ∈ Work.BMF.natIcc (X * Real.exp (-((j : ℝ) + 1) / K))
                (2 * X * Real.exp (-(j : ℝ) / K)),
                b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹ *
                  (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) from rfl]
      rw [hfun]
    have hre : (∫ t in (-S)..S,
            ‖∑ m ∈ Work.BMF.natIcc (X * Real.exp (-((j : ℝ) + 1) / K))
                (2 * X * Real.exp (-(j : ℝ) / K)),
              b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹ *
                (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        ≤ C_W * (2 * S + (2 * X * Real.exp (-(j : ℝ) / K) + 1)) * E j := by
      refine le_trans hmv ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hEdef]
      exact le_of_eq rfl
    calc (∫ t in (-S)..S, ‖mrDirect.primePoly c K j t * mrDirect.remPoly b P Q K X j t‖ ^ 2)
        ≤ Real.exp (-(2 * α * (j : ℝ) / K)) *
            (∫ t in (-S)..S, ‖mrDirect.remPoly b P Q K X j t‖ ^ 2) := hmono
      _ = Real.exp (-(2 * α * (j : ℝ) / K)) *
            (∫ t in (-S)..S,
              ‖∑ m ∈ Work.BMF.natIcc (X * Real.exp (-((j : ℝ) + 1) / K))
                  (2 * X * Real.exp (-(j : ℝ) / K)),
                b m * ((((mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹ *
                  (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2) := by rw [hrew]
      _ ≤ Real.exp (-(2 * α * (j : ℝ) / K)) *
            (C_W * (2 * S + (2 * X * Real.exp (-(j : ℝ) / K) + 1)) * E j) :=
          mul_le_mul_of_nonneg_left hre (Real.exp_pos _).le
      _ = C_W * (2 * S + (2 * X * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * E j) := by ring
  -- (3) the three sums over `j`
  have hSq1 : (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
      ≤ 20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X) := by
    have hstep : (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
        ≤ (2 / X) * Real.exp (1 / K) *
            (∑ j ∈ mrDirect.indexSet K P Q, Real.exp ((1 - 2 * α) * (j : ℝ) / K)) := by
      calc (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
          ≤ ∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) *
              (2 * Real.exp (((j : ℝ) + 1) / K) / X) := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (le_trans (hEle j) (winIdx_inv_sq_le X K j hX))
              (Real.exp_pos _).le
        _ = ∑ j ∈ mrDirect.indexSet K P Q,
              (2 / X) * Real.exp ((1 - 2 * α) * (j : ℝ) / K + 1 / K) := by
            apply Finset.sum_congr rfl
            intro j hj
            have h1 : Real.exp (-(2 * α * (j : ℝ) / K)) * Real.exp (((j : ℝ) + 1) / K)
                = Real.exp ((1 - 2 * α) * (j : ℝ) / K + 1 / K) := by
              rw [← Real.exp_add]
              congr 1
              ring
            calc Real.exp (-(2 * α * (j : ℝ) / K)) * (2 * Real.exp (((j : ℝ) + 1) / K) / X)
                = (2 / X) * (Real.exp (-(2 * α * (j : ℝ) / K)) *
                    Real.exp (((j : ℝ) + 1) / K)) := by ring
              _ = (2 / X) * Real.exp ((1 - 2 * α) * (j : ℝ) / K + 1 / K) := by rw [h1]
        _ = (2 / X) * Real.exp (1 / K) *
              (∑ j ∈ mrDirect.indexSet K P Q, Real.exp ((1 - 2 * α) * (j : ℝ) / K)) := by
            calc (∑ j ∈ mrDirect.indexSet K P Q,
                  (2 / X) * Real.exp ((1 - 2 * α) * (j : ℝ) / K + 1 / K))
                = ∑ j ∈ mrDirect.indexSet K P Q,
                    (2 / X) * (Real.exp (1 / K) * Real.exp ((1 - 2 * α) * (j : ℝ) / K)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [Real.exp_add]
                  ring
              _ = (2 / X) * (∑ j ∈ mrDirect.indexSet K P Q,
                    Real.exp (1 / K) * Real.exp ((1 - 2 * α) * (j : ℝ) / K)) := by
                  rw [← Finset.mul_sum]
              _ = (2 / X) * (Real.exp (1 / K) *
                    (∑ j ∈ mrDirect.indexSet K P Q, Real.exp ((1 - 2 * α) * (j : ℝ) / K))) := by
                  rw [← Finset.mul_sum]
              _ = (2 / X) * Real.exp (1 / K) *
                    (∑ j ∈ mrDirect.indexSet K P Q, Real.exp ((1 - 2 * α) * (j : ℝ) / K)) := by
                  ring
    have hexpK : Real.exp (1 / K) ≤ 3 := by
      calc Real.exp (1 / K) ≤ Real.exp 1 := by
            apply Real.exp_le_exp.mpr
            rw [div_le_one hKpos]
            linarith
        _ ≤ 3 := le_of_lt Real.exp_one_lt_three
    have hpos1 : (0:ℝ) ≤ (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X) := by
      have : (0:ℝ) ≤ K * Real.log (Q / P) := by nlinarith [hLnn, hKpos]
      nlinarith [this, hqqnn]
    have hpos2 : (0:ℝ) ≤ 2 / X * Real.exp (1 / K) := by positivity
    calc (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
        ≤ (2 / X) * Real.exp (1 / K) *
            (∑ j ∈ mrDirect.indexSet K P Q, Real.exp ((1 - 2 * α) * (j : ℝ) / K)) := hstep
      _ ≤ (2 / X) * Real.exp (1 / K) * (3 * Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2)) := by
          apply mul_le_mul_of_nonneg_left _ hpos2
          exact indexSet_exp_pos_sum_le K P Q α hK hP hPQ hα0 hα1
      _ ≤ 20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X) := by
          rw [show (2 / X) * Real.exp (1 / K) * (3 * Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2))
              = 6 * Real.exp (1 / K) * ((K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X)) by ring]
          nlinarith [hexpK, hpos1]
  have hSq2 : (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
      ≤ 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by
    have h1 : ∀ j, E j ≤ 2 := fun j => le_trans (hEle j) (winIdx_inv_sq_le_two X K j hXpos)
    calc (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
        ≤ ∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * 2 := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (h1 j) (Real.exp_pos _).le
      _ = 2 * (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K))) := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ 2 * (3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) :=
          mul_le_mul_of_nonneg_left (indexSet_exp_neg_sum_le K P Q α hK hP hPQ hα0 hα1)
            (by norm_num)
      _ = 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by ring
  have hSBE : (∑ j ∈ mrDirect.indexSet K P Q,
        (2 * X * Real.exp (-(j : ℝ) / K)) * (Real.exp (-(2 * α * (j : ℝ) / K)) * E j))
      ≤ 36 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by
    have h1 : ∀ j : ℕ, (2 * X * Real.exp (-(j : ℝ) / K)) * E j ≤ 4 * Real.exp (1 / K) := by
      intro j
      have h2 : E j ≤ 2 * Real.exp (((j : ℝ) + 1) / K) / X :=
        le_trans (hEle j) (winIdx_inv_sq_le X K j hX)
      calc (2 * X * Real.exp (-(j : ℝ) / K)) * E j
          ≤ (2 * X * Real.exp (-(j : ℝ) / K)) * (2 * Real.exp (((j : ℝ) + 1) / K) / X) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 4 * Real.exp (1 / K) := by
            rw [show (2 * X * Real.exp (-(j : ℝ) / K)) * (2 * Real.exp (((j : ℝ) + 1) / K) / X)
                = 4 * (Real.exp (-(j : ℝ) / K) * Real.exp (((j : ℝ) + 1) / K)) by field_simp; ring]
            rw [show Real.exp (-(j : ℝ) / K) * Real.exp (((j : ℝ) + 1) / K)
                = Real.exp (1 / K) by
              rw [← Real.exp_add]; congr 1; ring]
    calc (∑ j ∈ mrDirect.indexSet K P Q,
          (2 * X * Real.exp (-(j : ℝ) / K)) * (Real.exp (-(2 * α * (j : ℝ) / K)) * E j))
        ≤ ∑ j ∈ mrDirect.indexSet K P Q,
            (4 * Real.exp (1 / K)) * Real.exp (-(2 * α * (j : ℝ) / K)) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have h2 : (2 * X * Real.exp (-(j : ℝ) / K)) *
                (Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
              = ((2 * X * Real.exp (-(j : ℝ) / K)) * E j) *
                Real.exp (-(2 * α * (j : ℝ) / K)) := by
            ring
          rw [h2]
          exact mul_le_mul_of_nonneg_right (h1 j) (Real.exp_pos _).le
      _ = (4 * Real.exp (1 / K)) *
            (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K))) := by
          rw [← Finset.mul_sum]
      _ ≤ (4 * Real.exp (1 / K)) *
            (3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) :=
          mul_le_mul_of_nonneg_left (indexSet_exp_neg_sum_le K P Q α hK hP hPQ hα0 hα1)
            (by positivity)
      _ ≤ 36 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by
          have hexpK : Real.exp (1 / K) ≤ 3 := by
            calc Real.exp (1 / K) ≤ Real.exp 1 := by
                  apply Real.exp_le_exp.mpr
                  rw [div_le_one hKpos]
                  linarith
              _ ≤ 3 := le_of_lt Real.exp_one_lt_three
          have hpos1 : (0:ℝ) ≤ (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by
            have : (0:ℝ) ≤ K * Real.log (Q / P) := by nlinarith [hLnn, hKpos]
            nlinarith [this, hppnn]
          nlinarith [hexpK, hpos1]
  -- (4) sum the per-j bounds
  have hsumI : (∑ j ∈ mrDirect.indexSet K P Q,
        (∫ t in (-S)..S, ‖mrDirect.primePoly c K j t * mrDirect.remPoly b P Q K X j t‖ ^ 2))
      ≤ C_W * (K * Real.log (Q / P) + 2) *
          (40 * S * (Q ^ (1 - 2 * α) / X) + 42 * P ^ (-(2 * α))) := by
    have hsplit : (∑ j ∈ mrDirect.indexSet K P Q,
          C_W * (2 * S + (2 * X * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * E j))
        = C_W * (2 * S * (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
            + ((∑ j ∈ mrDirect.indexSet K P Q,
                  (2 * X * Real.exp (-(j : ℝ) / K)) * (Real.exp (-(2 * α * (j : ℝ) / K)) * E j))
              + (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j))) := by
      have hpt : ∀ j ∈ mrDirect.indexSet K P Q,
          C_W * (2 * S + (2 * X * Real.exp (-(j : ℝ) / K) + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
          = C_W * (2 * S * (Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
              + ((2 * X * Real.exp (-(j : ℝ) / K)) * (Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
                + Real.exp (-(2 * α * (j : ℝ) / K)) * E j)) := by
        intro j hj
        ring
      rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    calc (∑ j ∈ mrDirect.indexSet K P Q,
          (∫ t in (-S)..S, ‖mrDirect.primePoly c K j t * mrDirect.remPoly b P Q K X j t‖ ^ 2))
        ≤ ∑ j ∈ mrDirect.indexSet K P Q,
            C_W * (2 * S + (2 * X * Real.exp (-(j : ℝ) / K) + 1)) *
              (Real.exp (-(2 * α * (j : ℝ) / K)) * E j) := Finset.sum_le_sum hperj
      _ = C_W * (2 * S * (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
            + ((∑ j ∈ mrDirect.indexSet K P Q,
                  (2 * X * Real.exp (-(j : ℝ) / K)) * (Real.exp (-(2 * α * (j : ℝ) / K)) * E j))
              + (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j))) := hsplit
      _ ≤ C_W * (2 * S * (20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X))
            + (36 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α))
              + 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)))) := by
          have h1 : 2 * S * (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
              ≤ 2 * S * (20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X)) :=
            mul_le_mul_of_nonneg_left hSq1 (by linarith)
          have h2 : (∑ j ∈ mrDirect.indexSet K P Q,
                (2 * X * Real.exp (-(j : ℝ) / K)) * (Real.exp (-(2 * α * (j : ℝ) / K)) * E j))
              ≤ 36 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := hSBE
          have h3 : (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
              ≤ 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := hSq2
          have h4 : 2 * S * (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j)
                + ((∑ j ∈ mrDirect.indexSet K P Q,
                      (2 * X * Real.exp (-(j : ℝ) / K)) *
                        (Real.exp (-(2 * α * (j : ℝ) / K)) * E j))
                  + (∑ j ∈ mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) * E j))
              ≤ 2 * S * (20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X))
                + (36 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α))
                  + 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α))) := by linarith
          exact mul_le_mul_of_nonneg_left h4 hCWpos.le
      _ = C_W * (K * Real.log (Q / P) + 2) *
          (40 * S * (Q ^ (1 - 2 * α) / X) + 42 * P ^ (-(2 * α))) := by ring
  -- (5) final arithmetic
  rw [show S / X * Q ^ (1 - 2 * α) = S * (Q ^ (1 - 2 * α) / X) by ring]
  set L : ℝ := Real.log (Q / P) with hLdef
  set qq : ℝ := Q ^ (1 - 2 * α) / X with hqqdef
  set pp : ℝ := P ^ (-(2 * α)) with hppdef
  have hLnn' : 0 ≤ L := by rw [hLdef]; exact hLnn
  have hqqnn' : 0 ≤ qq := by rw [hqqdef]; exact hqqnn
  have hppnn' : 0 ≤ pp := by rw [hppdef]; exact hppnn
  have hKL' : K * L + 2 ≤ 2 * K * (L + 1) := by nlinarith [hKpos, hLnn']
  have hin' : 40 * S * qq + 42 * pp ≤ 42 * (S * qq + pp) := by
    have h := mul_nonneg hS hqqnn'
    linarith
  have hKsq' : 4 * K ^ 2 ≤ (K + 1) ^ 3 := by
    nlinarith [mul_nonneg hKpos.le (sq_nonneg (K - 1)), sq_nonneg (K + 1)]
  have hK2L' : K ^ 2 * L * (L + 1) ≤ ((K + 1) ^ 3 / 4) * (L + 1) * (L + 1) := by
    have h1 : K ^ 2 ≤ (K + 1) ^ 3 / 4 := by linarith [hKsq']
    nlinarith [h1, hLnn', hK, sq_nonneg (L + 1)]
  have h21' : 21 * C_W ≤ 100 * (C_W + 1) * (1 + 1 / α) := by
    have h3 : (1:ℝ) ≤ 1 + 1 / α := by
      have : 0 < 1 / α := by positivity
      linarith
    nlinarith [hCWpos, h3]
  have hsum0 : 0 ≤ S * qq + pp := by linarith
  have hX1 : 0 ≤ 40 * S * qq + 42 * pp := by linarith
  have hinner1 : C_W * (K * L + 2) * (40 * S * qq + 42 * pp)
      ≤ C_W * (2 * K * (L + 1)) * (40 * S * qq + 42 * pp) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKL' hCWpos.le) hX1
  have hinner2 : C_W * (2 * K * (L + 1)) * (40 * S * qq + 42 * pp)
      ≤ C_W * (2 * K * (L + 1)) * (42 * (S * qq + pp)) :=
    mul_le_mul_of_nonneg_left hin' (by positivity)
  have hstep1 : K * L * (C_W * (K * L + 2) * (40 * S * qq + 42 * pp))
      ≤ K * L * (C_W * (2 * K * (L + 1)) * (42 * (S * qq + pp))) :=
    mul_le_mul_of_nonneg_left (le_trans hinner1 hinner2) (mul_nonneg hKpos.le hLnn')
  have hstep2 : 84 * C_W * (K ^ 2 * L * (L + 1)) * (S * qq + pp)
      ≤ 84 * C_W * (((K + 1) ^ 3 / 4) * (L + 1) * (L + 1)) * (S * qq + pp) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK2L' (by positivity)) hsum0
  have hstep3 : 21 * C_W * (K + 1) ^ 3 * (L + 1) ^ 2 * (S * qq + pp)
      ≤ 100 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 3 * (L + 1) ^ 2 * (S * qq + pp) := by
    have h1 := mul_le_mul_of_nonneg_right h21'
      (show (0:ℝ) ≤ (K + 1) ^ 3 * (L + 1) ^ 2 * (S * qq + pp) by positivity)
    linarith
  have hmain : K * L * (C_W * (K * L + 2) * (40 * S * qq + 42 * pp))
      ≤ 100 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 3 * (L + 1) ^ 2 * (S * qq + pp) := by
    calc K * L * (C_W * (K * L + 2) * (40 * S * qq + 42 * pp))
        ≤ K * L * (C_W * (2 * K * (L + 1)) * (42 * (S * qq + pp))) := hstep1
      _ = 84 * C_W * (K ^ 2 * L * (L + 1)) * (S * qq + pp) := by ring
      _ ≤ 84 * C_W * (((K + 1) ^ 3 / 4) * (L + 1) * (L + 1)) * (S * qq + pp) := hstep2
      _ = 21 * C_W * (K + 1) ^ 3 * (L + 1) ^ 2 * (S * qq + pp) := by ring
      _ ≤ 100 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 3 * (L + 1) ^ 2 * (S * qq + pp) := hstep3
  have hstep : K * L * (∑ j ∈ mrDirect.indexSet K P Q,
        ∫ t in (-S)..S, ‖mrDirect.primePoly c K j t * mrDirect.remPoly b P Q K X j t‖ ^ 2)
      ≤ K * L * (C_W * (K * L + 2) * (40 * S * qq + 42 * pp)) :=
    mul_le_mul_of_nonneg_left hsumI (mul_nonneg hKpos.le hLnn')
  exact le_trans hstep hmain

end

end Work.BMF.mr_direct
