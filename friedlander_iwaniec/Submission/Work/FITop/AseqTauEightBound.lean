import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S20
import Submission.ASP.S30
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le_squarefree
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred

set_option maxHeartbeats 4000000

open Finset

namespace Work.FITop

/-- `ã_n = μ(n)² a_n` equals `a_n` for squarefree `n` and `0` otherwise. -/
lemma atilFIa_eq_indicator (n : ℕ) :
    atilFIa n = (if Squarefree n then (Submission.an n : ℝ) else 0) := by
  have hcast : ((ArithmeticFunction.moebius n : ℝ)) ^ 2
      = ((ArithmeticFunction.moebius n ^ 2 : ℤ) : ℝ) := by
    rw [Int.cast_pow]
  rw [atilFIa, Submission.ASP.atil, Submission.ASP.FIa, hcast, ArithmeticFunction.moebius_sq]
  by_cases hs : Squarefree n
  · rw [if_pos hs, if_pos hs]; simp
  · rw [if_neg hs, if_neg hs]; simp

lemma atilFIa_nonneg (n : ℕ) : 0 ≤ atilFIa n := by
  rw [atilFIa_eq_indicator n]; split_ifs <;> positivity

lemma atilFIa_one : atilFIa 1 = (Submission.an 1 : ℝ) := by
  rw [atilFIa_eq_indicator 1, if_pos squarefree_one]

/-- A squarefree number has no prime cube divisor. -/
lemma not_prime_cube_dvd_of_squarefree {d : ℕ} (hd : Squarefree d) :
    ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d := by
  intro p hp hdiv
  have hpp : p * p ∣ d := dvd_trans ⟨p, by ring⟩ hdiv
  exact (Nat.squarefree_iff_prime_squarefree.mp hd p hp) hpp

theorem AseqTauEightBound :
    ∃ C X₀ : ℕ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x →
      (∑ n ∈ Finset.Icc 1 x, Work.FITop.atilFIa n * (((n.divisors.card : ℝ))^8))
        ≤ C * Work.FITop.AcountAtil x * (Real.log (x:ℝ)) ^ (262144 : ℕ) := by
  classical
  obtain ⟨C0, hC0pos, hAd⟩ := Submission.ASP.Ad_le_tau_sq_div_of_cubefree
  obtain ⟨C1, hC1pos, hSum⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 18
  obtain ⟨X1, hAtil⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  have hGpos : (0:ℝ) < Submission.ASP.Gprod Submission.ASP.FIg := Submission.ASP.Gprod_FIg_pos
  let Cc : ℝ := (2:ℝ)^16 * (C0 * C1 * (2:ℝ)^262144)
  let Ktot : ℝ := Cc * (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1)
  have hCc_eq : Cc = (2:ℝ)^16 * (C0 * C1 * (2:ℝ)^262144) := rfl
  have hKtot_eq : Ktot = Cc * (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) := rfl
  have hCcpos : 0 < Cc := by
    rw [hCc_eq]
    exact mul_pos (by positivity) (by positivity)
  refine ⟨⌈Ktot⌉₊ + 1, max 3 X1, by omega, ?_⟩
  intro x hx
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hxX1 : X1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ x := by omega
  have hxR1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
  have hxRpos : (0:ℝ) < (x:ℝ) := by linarith
  have hlogxnn : 0 ≤ Real.log (x:ℝ) := Real.log_nonneg hxR1
  have hAseqnn : (0:ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  have hAcnn : (0:ℝ) ≤ Work.FITop.AcountAtil x := by
    rw [Work.FITop.AcountAtil, Submission.ASP.Acount]
    exact Finset.sum_nonneg (fun n _ => atilFIa_nonneg n)
  -- ### Step 1: pass to squarefree `n` and replace `ã_n` by `a_n`
  have hstep1 : (∑ n ∈ Finset.Icc 1 x, atilFIa n * (((n.divisors.card : ℝ))^8))
      = ∑ n ∈ (Finset.Icc 1 x).filter Squarefree,
          (Submission.an n : ℝ) * (((n.divisors.card : ℝ))^8) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [atilFIa_eq_indicator n]
    by_cases hs : Squarefree n <;> simp [hs]
  -- ### Step 2: the pointwise small-divisor bound for squarefree `n`
  have hstep2 : (∑ n ∈ (Finset.Icc 1 x).filter Squarefree,
        (Submission.an n : ℝ) * (((n.divisors.card : ℝ))^8))
      ≤ (2:ℝ)^16 * ∑ n ∈ (Finset.Icc 1 x).filter Squarefree,
          ∑ d ∈ n.divisors.filter (fun d => d^2 ≤ n),
            (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, hnsq⟩ := hn
    obtain ⟨d, hdvd, hdsq, hdbd⟩ :=
      Commons.NumberTheory.Divisors.small_divisor_tau_le_squarefree (k := 2) (by norm_num) hn1 hnsq
    have hdbd' : ((n.divisors.card : ℝ)) ≤ (2 * (d.divisors.card : ℝ))^(2:ℕ) := by
      have h := hdbd
      rw [Real.rpow_natCast] at h
      exact h
    have h8 : ((n.divisors.card : ℝ))^8 ≤ (2:ℝ)^16 * ((d.divisors.card : ℝ))^16 := by
      have h1 : ((n.divisors.card : ℝ))^8 ≤ ((2 * (d.divisors.card : ℝ))^(2:ℕ))^8 :=
        pow_le_pow_left₀ (by positivity) hdbd' 8
      calc ((n.divisors.card : ℝ))^8 ≤ ((2 * (d.divisors.card : ℝ))^(2:ℕ))^8 := h1
        _ = (2:ℝ)^16 * ((d.divisors.card : ℝ))^16 := by ring
    have hmem : d ∈ n.divisors.filter (fun d => d^2 ≤ n) := by
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hdvd, by omega⟩, hdsq⟩
    have hsum_ge : ((d.divisors.card : ℝ))^16
        ≤ ∑ e ∈ n.divisors.filter (fun d => d^2 ≤ n), ((e.divisors.card : ℝ))^16 :=
      Finset.single_le_sum (s := n.divisors.filter (fun d => d^2 ≤ n))
        (f := fun e => ((e.divisors.card : ℝ))^16) (fun e _ => by positivity) hmem
    have han : (0:ℝ) ≤ (Submission.an n : ℝ) := by positivity
    calc (Submission.an n : ℝ) * ((n.divisors.card : ℝ))^8
        ≤ (Submission.an n : ℝ) * ((2:ℝ)^16 * ((d.divisors.card : ℝ))^16) :=
          mul_le_mul_of_nonneg_left h8 han
      _ = (2:ℝ)^16 * ((Submission.an n : ℝ) * ((d.divisors.card : ℝ))^16) := by ring
      _ ≤ (2:ℝ)^16 * ((Submission.an n : ℝ) *
            ∑ e ∈ n.divisors.filter (fun d => d^2 ≤ n), ((e.divisors.card : ℝ))^16) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_ge han) (by positivity)
      _ = (2:ℝ)^16 * ∑ e ∈ n.divisors.filter (fun d => d^2 ≤ n),
            (Submission.an n : ℝ) * ((e.divisors.card : ℝ))^16 := by
          rw [Finset.mul_sum]
  -- ### Step 3: swap the order of summation and restrict to squarefree small `d`
  have hstep3 : (∑ n ∈ (Finset.Icc 1 x).filter Squarefree,
          ∑ d ∈ n.divisors.filter (fun d => d^2 ≤ n),
            (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16))
      ≤ ∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
          (((d.divisors.card : ℝ))^16) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n),
              (Submission.an n : ℝ)) := by
    have h3a : (∑ n ∈ (Finset.Icc 1 x).filter Squarefree,
          ∑ d ∈ n.divisors.filter (fun d => d^2 ≤ n),
            (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16))
        ≤ ∑ n ∈ (Finset.Icc 1 x).filter Squarefree, ∑ d ∈ n.divisors,
            (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16)
              * (if Squarefree d ∧ d^2 ≤ x then 1 else 0) := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnx⟩, hnsq⟩ := hn
      have hinner_eq : (∑ d ∈ n.divisors.filter (fun d => d^2 ≤ n),
            (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16))
          = ∑ d ∈ n.divisors, (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16)
              * (if d^2 ≤ n then 1 else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        by_cases hd : d^2 ≤ n <;> simp [hd]
      rw [hinner_eq]
      refine Finset.sum_le_sum (fun d hd => ?_)
      rw [Nat.mem_divisors] at hd
      obtain ⟨hdvd, _⟩ := hd
      have hdS : Squarefree d := Squarefree.squarefree_of_dvd hdvd hnsq
      by_cases hd2 : d^2 ≤ n
      · have hcond : Squarefree d ∧ d^2 ≤ x := ⟨hdS, le_trans hd2 hnx⟩
        rw [if_pos hd2, if_pos hcond]
      · rw [if_neg hd2]
        simp only [mul_zero]
        rcases em (Squarefree d ∧ d^2 ≤ x) with hc | hc
        · rw [if_pos hc]; positivity
        · rw [if_neg hc]; simp
    have h3b : (∑ n ∈ (Finset.Icc 1 x).filter Squarefree, ∑ d ∈ n.divisors,
            (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16)
              * (if Squarefree d ∧ d^2 ≤ x then 1 else 0))
        = ∑ d ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n),
            (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16)
              * (if Squarefree d ∧ d^2 ≤ x then 1 else 0) := by
      rw [Submission.ASP.sum_filter_divisors_swap (fun n => Squarefree n)
        (fun n d => (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16)
              * (if Squarefree d ∧ d^2 ≤ x then 1 else 0))]
    have h3c : (∑ d ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n),
            (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16)
              * (if Squarefree d ∧ d^2 ≤ x then 1 else 0))
        = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
            (((d.divisors.card : ℝ))^16) *
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n),
                (Submission.an n : ℝ)) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      by_cases hd : Squarefree d ∧ d^2 ≤ x
      · rw [if_pos hd]
        rw [if_pos hd]
        simp only [mul_one]
        rw [← Finset.sum_mul]
        ring
      · rw [if_neg hd]
        rw [if_neg hd]
        simp
    exact le_trans h3a (le_of_eq (h3b.trans h3c))
  -- ### Step 4: the congruence-sum bound, the `τ¹⁸/d` sum and the `log` estimate
  have hstep4 : (∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
          (((d.divisors.card : ℝ))^16) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n),
              (Submission.an n : ℝ)))
      ≤ C0 * (Submission.Aseq x : ℝ) * (C1 * (Real.log ((x:ℝ) + 2))^(262144:ℕ)) := by
    have hpt : ∀ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
        (((d.divisors.card : ℝ))^16) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n),
              (Submission.an n : ℝ))
          ≤ C0 * (Submission.Aseq x : ℝ) * ((((d.divisors.card : ℝ))^18) / (d:ℝ)) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, hdsq, hdd2⟩ := hd
      have hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d := not_prime_cube_dvd_of_squarefree hdsq
      have hAd' := hAd d x hd1 hcb hdd2
      have hinner : (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n),
            (Submission.an n : ℝ)) ≤ (Submission.Ad d x : ℝ) := by
        have hsub : (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n)
            ⊆ (Finset.range (x+1)).filter (fun n => d ∣ n) := by
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hn.2.2⟩
        calc (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n),
              (Submission.an n : ℝ))
            ≤ ∑ n ∈ (Finset.range (x+1)).filter (fun n => d ∣ n), (Submission.an n : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
          _ = (Submission.Ad d x : ℝ) := by
              rw [Submission.Ad, Nat.cast_sum]
      calc (((d.divisors.card : ℝ))^16) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n), (Submission.an n : ℝ))
          ≤ (((d.divisors.card : ℝ))^16) * (Submission.Ad d x : ℝ) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ (((d.divisors.card : ℝ))^16)
              * (C0 * ((((d.divisors.card : ℝ))^2) / (d:ℝ)) * (Submission.Aseq x : ℝ)) :=
            mul_le_mul_of_nonneg_left hAd' (by positivity)
        _ = C0 * (Submission.Aseq x : ℝ) * ((((d.divisors.card : ℝ))^18) / (d:ℝ)) := by ring
    calc (∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
          (((d.divisors.card : ℝ))^16) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n), (Submission.an n : ℝ)))
        ≤ ∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
            C0 * (Submission.Aseq x : ℝ) * ((((d.divisors.card : ℝ))^18) / (d:ℝ)) :=
          Finset.sum_le_sum hpt
      _ = C0 * (Submission.Aseq x : ℝ)
            * ∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
                ((((d.divisors.card : ℝ))^18) / (d:ℝ)) := by rw [Finset.mul_sum]
      _ ≤ C0 * (Submission.Aseq x : ℝ) * (C1 * (Real.log ((x:ℝ) + 2))^(262144:ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hsub : (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x)
              ⊆ Finset.Icc 1 x := Finset.filter_subset _ _
          have h1 : ∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
                ((((d.divisors.card : ℝ))^18) / (d:ℝ))
              ≤ ∑ d ∈ Finset.Icc 1 x, ((((d.divisors.card : ℝ))^18) / (d:ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
          have h2 := hSum x hx1
          have h3 : (2:ℕ)^18 = 262144 := by norm_num
          rw [h3] at h2
          exact le_trans h1 h2
  -- ### Step 5: `log (x+2) ≤ 2 log x`
  have hstep5 : (Real.log ((x:ℝ)+2))^262144 ≤ (2:ℝ)^262144 * (Real.log (x:ℝ))^262144 := by
    have hlog2nn : 0 ≤ Real.log ((x:ℝ)+2) := Real.log_nonneg (by linarith)
    have hle : Real.log ((x:ℝ)+2) ≤ 2 * Real.log (x:ℝ) := by
      have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
      have h1 : (x:ℝ)+2 ≤ (x:ℝ)*(x:ℝ) := by nlinarith
      have h2 : Real.log ((x:ℝ)+2) ≤ Real.log ((x:ℝ)*(x:ℝ)) := Real.log_le_log (by linarith) h1
      rw [Real.log_mul (by linarith : (x:ℝ) ≠ 0) (by linarith : (x:ℝ) ≠ 0)] at h2
      linarith
    calc (Real.log ((x:ℝ)+2))^262144 ≤ (2 * Real.log (x:ℝ))^262144 :=
          pow_le_pow_left₀ hlog2nn hle _
      _ = (2:ℝ)^262144 * (Real.log (x:ℝ))^262144 := by rw [mul_pow]
  -- ### Assembly
  have hS : (∑ n ∈ Finset.Icc 1 x, atilFIa n * (((n.divisors.card : ℝ))^8))
      ≤ Cc * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^262144 := by
    rw [hstep1]
    have h4 : (∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
          (((d.divisors.card : ℝ))^16) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n), (Submission.an n : ℝ)))
        ≤ (C0 * C1 * (2:ℝ)^262144) * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^262144 := by
      have h41 : C0 * (Submission.Aseq x : ℝ) * (C1 * (Real.log ((x:ℝ) + 2))^(262144:ℕ))
          ≤ C0 * (Submission.Aseq x : ℝ) * (C1 * ((2:ℝ)^262144 * (Real.log (x:ℝ))^262144)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hstep5 (le_of_lt hC1pos)
      have h42 : C0 * (Submission.Aseq x : ℝ) * (C1 * ((2:ℝ)^262144 * (Real.log (x:ℝ))^262144))
          = (C0 * C1 * (2:ℝ)^262144) * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^262144 := by
        ring
      exact le_trans hstep4 (le_trans h41 (le_of_eq h42))
    calc (∑ n ∈ (Finset.Icc 1 x).filter Squarefree,
            (Submission.an n : ℝ) * (((n.divisors.card : ℝ))^8))
        ≤ (2:ℝ)^16 * (∑ n ∈ (Finset.Icc 1 x).filter Squarefree,
            ∑ d ∈ n.divisors.filter (fun d => d^2 ≤ n),
              (Submission.an n : ℝ) * (((d.divisors.card : ℝ))^16)) := hstep2
      _ ≤ (2:ℝ)^16 * (∑ d ∈ (Finset.Icc 1 x).filter (fun d => Squarefree d ∧ d^2 ≤ x),
          (((d.divisors.card : ℝ))^16) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Squarefree n ∧ d ∣ n), (Submission.an n : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep3 (by norm_num)
      _ ≤ (2:ℝ)^16 * ((C0 * C1 * (2:ℝ)^262144) * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^262144) :=
          mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = Cc * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^262144 := by
          rw [hCc_eq]; ring
  have hAseq : (Submission.Aseq x : ℝ)
      ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * Work.FITop.AcountAtil x := by
    have hFI : (Submission.Aseq x : ℝ) = Submission.ASP.Acount Submission.ASP.FIa (x:ℝ) + 1 := by
      have h := Submission.ASP.FI_Acount_eq x
      linarith
    have hAtil' := hAtil x hxX1
    have hAc : Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (x:ℝ)
        = Work.FITop.AcountAtil x := rfl
    rw [hAc] at hAtil'
    have hAtil1 : (1:ℝ) ≤ Work.FITop.AcountAtil x := by
      have hmem1 : (1:ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hx1⟩
      have h1 : Work.FITop.atilFIa 1 ≤ Work.FITop.AcountAtil x := by
        rw [Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
        exact Finset.single_le_sum (fun n _ => atilFIa_nonneg n) hmem1
      have h2 : (1:ℝ) ≤ Work.FITop.atilFIa 1 := by
        rw [atilFIa_one]
        exact_mod_cast Submission.ASP.an_one_pos'
      linarith
    calc (Submission.Aseq x : ℝ) = Submission.ASP.Acount Submission.ASP.FIa (x:ℝ) + 1 := hFI
      _ ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg) * Work.FITop.AcountAtil x + 1 := by linarith
      _ ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg) * Work.FITop.AcountAtil x
            + Work.FITop.AcountAtil x := by linarith
      _ = (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * Work.FITop.AcountAtil x := by ring
  have hKtotle : Ktot ≤ ((⌈Ktot⌉₊ + 1 : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil Ktot
    have h2 : ((⌈Ktot⌉₊ : ℕ) : ℝ) ≤ ((⌈Ktot⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    linarith
  calc (∑ n ∈ Finset.Icc 1 x, atilFIa n * (((n.divisors.card : ℝ))^8))
      ≤ Cc * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^262144 := hS
    _ ≤ Cc * ((2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * Work.FITop.AcountAtil x)
          * (Real.log (x:ℝ))^262144 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlogxnn 262144)
        exact mul_le_mul_of_nonneg_left hAseq (le_of_lt hCcpos)
    _ = Ktot * Work.FITop.AcountAtil x * (Real.log (x:ℝ))^262144 := by
        rw [hKtot_eq]; ring
    _ ≤ ((⌈Ktot⌉₊ + 1 : ℕ) : ℝ) * Work.FITop.AcountAtil x * (Real.log (x:ℝ))^262144 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlogxnn 262144)
        exact mul_le_mul_of_nonneg_right hKtotle hAcnn

end Work.FITop
