import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog
import Submission.Commons.Analysis.Asymptotics.eventually_log_rpow_le_mul
import Submission.Commons.NumberTheory.Chebyshev.sum_Icc_prime_log_eq_theta_sub
import Submission.Commons.NumberTheory.PrimeNumberTheorem.not_coprime_prime_log_window_shift_le

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.PrimeNumberTheorem

private lemma abs_sub_le_abs' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa using abs_sub_le x 0 y

theorem theta_window_shift_powLog_largeN (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N q h : ℕ, 2 ≤ N → q ≠ 0 → (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) → h ≤ N →
      |(∑ m ∈ (Finset.Icc (N + h) (2 * N + h)).filter (fun m => m.Coprime q),
          (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)| ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  obtain ⟨x₀, hx₀⟩ := theta_sub_id_powLog A hA
  have hlogev : ∀ᶠ N : ℕ in atTop,
      (Real.log (N : ℝ)) ^ (A + 1) ≤ (1 / 4) * (N : ℝ) :=
    Commons.Analysis.Asymptotics.eventually_log_rpow_le_mul (A + 1) (by linarith) (1 / 4) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hlogev
  set N₀ : ℕ := max N₁ (max (Nat.ceil x₀ + 1) 4) with hN₀def
  have hN₁N₀ : N₁ ≤ N₀ := by rw [hN₀def]; exact le_max_left _ _
  have hceilN₀ : Nat.ceil x₀ + 1 ≤ N₀ := by
    rw [hN₀def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h4N₀ : 4 ≤ N₀ := by
    rw [hN₀def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  set K : ℝ := ∑ n ∈ Finset.Icc 2 (N₀ - 1),
      (((n : ℝ) + 1) * Real.log ((3 * n : ℕ) : ℝ) + (n : ℝ)) * (Real.log (n : ℝ)) ^ A / (n : ℝ)
      with hKdef
  refine ⟨max 8 K + 1, ?_, ?_⟩
  · linarith [le_max_left (8 : ℝ) K]
  · intro N q h hN2 hq hqN hh
    set a : ℕ := N + h with hadef
    set b : ℕ := 2 * N + h with hbdef
    have haN : N ≤ a := by omega
    have hab : a ≤ b := by omega
    have hba : b = a + N := by omega
    have hb3N : b ≤ 3 * N := by omega
    have ha3N : a ≤ 3 * N := by omega
    have ha1 : 1 ≤ a := by omega
    have hbcast : (b : ℝ) = (a : ℝ) + (N : ℝ) := by exact_mod_cast hba
    have hBnn : 0 ≤ ∑ m ∈ (Finset.Icc a b).filter (fun m => ¬ m.Coprime q),
        (if m.Prime then Real.log (m : ℝ) else 0) := by
      apply Finset.sum_nonneg
      intro m hm
      have hm1 : 1 ≤ m := le_trans ha1 (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      by_cases hp : m.Prime
      · rw [if_pos hp]; exact Real.log_nonneg (by exact_mod_cast hm1)
      · rw [if_neg hp]
    have hSnn : 0 ≤ ∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
        (if m.Prime then Real.log (m : ℝ) else 0) := by
      apply Finset.sum_nonneg
      intro m hm
      have hm1 : 1 ≤ m := le_trans ha1 (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      by_cases hp : m.Prime
      · rw [if_pos hp]; exact Real.log_nonneg (by exact_mod_cast hm1)
      · rw [if_neg hp]
    have hSB : (∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
          (if m.Prime then Real.log (m : ℝ) else 0))
        + (∑ m ∈ (Finset.Icc a b).filter (fun m => ¬ m.Coprime q),
          (if m.Prime then Real.log (m : ℝ) else 0))
        = ∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hsub := Commons.NumberTheory.Chebyshev.sum_Icc_prime_log_eq_theta_sub a b ha1 hab
    have hSle : (∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
          (if m.Prime then Real.log (m : ℝ) else 0))
        ≤ ((N : ℝ) + 1) * Real.log ((3 * N : ℕ) : ℝ) := by
      have h1 : (∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
            (if m.Prime then Real.log (m : ℝ) else 0))
          ≤ ∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0) := by
        linarith [hSB, hBnn]
      have h2 : (∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0))
          ≤ ((Finset.Icc a b).card : ℝ) * Real.log ((3 * N : ℕ) : ℝ) := by
        calc (∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0))
            ≤ ∑ _m ∈ Finset.Icc a b, Real.log ((3 * N : ℕ) : ℝ) := by
              apply Finset.sum_le_sum
              intro m hm
              have hmle : m ≤ 3 * N := le_trans (Finset.mem_Icc.mp hm).2 hb3N
              have hm0 : 0 < m := lt_of_lt_of_le (by omega : 0 < a)
                (Finset.mem_Icc.mp hm).1
              by_cases hp : m.Prime
              · rw [if_pos hp]
                exact Real.log_le_log (by exact_mod_cast hm0) (by exact_mod_cast hmle)
              · rw [if_neg hp]
                exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 3 * N))
          _ = ((Finset.Icc a b).card : ℝ) * Real.log ((3 * N : ℕ) : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : ((Finset.Icc a b).card : ℝ) = (N : ℝ) + 1 := by
        rw [Nat.card_Icc]
        have hc : b + 1 - a = N + 1 := by omega
        rw [hc]; push_cast; ring
      calc (∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
            (if m.Prime then Real.log (m : ℝ) else 0))
          ≤ ∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0) := h1
        _ ≤ ((Finset.Icc a b).card : ℝ) * Real.log ((3 * N : ℕ) : ℝ) := h2
        _ = ((N : ℝ) + 1) * Real.log ((3 * N : ℕ) : ℝ) := by rw [h3]
    by_cases hbig : N₀ ≤ N
    · have hN₁N : N₁ ≤ N := le_trans hN₁N₀ hbig
      have hceilN : Nat.ceil x₀ + 1 ≤ N := le_trans hceilN₀ hbig
      have hN4 : 4 ≤ N := le_trans h4N₀ hbig
      have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      have hlogNnn : 0 ≤ Real.log (N : ℝ) := le_of_lt hlogNpos
      have hpowpos : 0 < (Real.log (N : ℝ)) ^ A := Real.rpow_pos_of_pos hlogNpos A
      set X : ℝ := (N : ℝ) / (Real.log (N : ℝ)) ^ A with hXdef
      have hXpos : 0 < X := by rw [hXdef]; exact div_pos hNposR hpowpos
      have hXnn : 0 ≤ X := le_of_lt hXpos
      have hx₀N : x₀ ≤ (N : ℝ) := by
        have h1 : x₀ ≤ (Nat.ceil x₀ : ℝ) := Nat.le_ceil x₀
        have h2 : ((Nat.ceil x₀ : ℕ) : ℝ) ≤ ((Nat.ceil x₀ + 1 : ℕ) : ℝ) := by
          push_cast; linarith
        have h3 : ((Nat.ceil x₀ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hceilN
        linarith
      have h1log : (Real.log (N : ℝ)) ^ (A + 1) ≤ (1 / 4) * (N : ℝ) := hN₁ N hN₁N
      have hpow_add : (Real.log (N : ℝ)) ^ (A + 1) = (Real.log (N : ℝ)) ^ A * Real.log (N : ℝ) := by
        rw [Real.rpow_add hlogNpos, Real.rpow_one]
      have hlog3N : Real.log ((3 * N : ℕ) : ℝ) = Real.log 3 + Real.log (N : ℝ) := by
        rw [Nat.cast_mul]; exact Real.log_mul (by norm_num) (ne_of_gt hNposR)
      have hlog3le : Real.log 3 ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 3 ≤ N))
      have hlog3Nle : Real.log ((3 * N : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
        rw [hlog3N]; linarith
      have hlog3N_le : Real.log ((3 * N : ℕ) : ℝ) ≤ X := by
        have hstep : 2 * Real.log (N : ℝ) ≤ X := by
          rw [hXdef, le_div_iff₀ hpowpos]
          have heq : 2 * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A
              = 2 * (Real.log (N : ℝ)) ^ (A + 1) := by rw [hpow_add]; ring
          rw [heq]; linarith [h1log]
        linarith [hlog3Nle, hstep]
      have hhalflog : (1 / 2) * Real.log (N : ℝ) ≤ X := by
        rw [hXdef, le_div_iff₀ hpowpos]
        have heq : (1 / 2) * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A
            = (1 / 2) * (Real.log (N : ℝ)) ^ (A + 1) := by rw [hpow_add]; ring
        rw [heq]; linarith [h1log]
      have hthbnd : ∀ x : ℕ, N ≤ x → x ≤ 3 * N → |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤ 3 * X := by
        intro x hNx hx3N
        have hx₀x : x₀ ≤ (x : ℝ) := le_trans hx₀N (by exact_mod_cast hNx)
        have hlogxpos : 0 < Real.log (x : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < x))
        have hlogNle : Real.log (N : ℝ) ≤ Real.log (x : ℝ) :=
          Real.log_le_log hNposR (by exact_mod_cast hNx)
        have hpows : (Real.log (N : ℝ)) ^ A ≤ (Real.log (x : ℝ)) ^ A :=
          Real.rpow_le_rpow hlogNnn hlogNle hA.le
        have key : |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤ 3 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
          refine (hx₀ (x : ℝ) hx₀x).trans ?_
          calc (x : ℝ) / (Real.log (x : ℝ)) ^ A
              ≤ ((3 * N : ℕ) : ℝ) / (Real.log (x : ℝ)) ^ A := by
                apply div_le_div_of_nonneg_right (by exact_mod_cast hx3N)
                exact le_of_lt (Real.rpow_pos_of_pos hlogxpos A)
            _ = 3 * (N : ℝ) / (Real.log (x : ℝ)) ^ A := by push_cast; ring
            _ ≤ 3 * (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
                div_le_div_of_nonneg_left (by positivity) hpowpos hpows
        calc |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤ 3 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := key
          _ = 3 * X := by rw [hXdef]; ring
      have hga : |(if a.Prime then Real.log (a : ℝ) else 0)| ≤ X := by
        have hle : (if a.Prime then Real.log (a : ℝ) else 0) ≤ Real.log ((3 * N : ℕ) : ℝ) := by
          by_cases hp : a.Prime
          · rw [if_pos hp]
            exact Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast ha3N)
          · rw [if_neg hp]
            exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 3 * N))
        have hnn : 0 ≤ (if a.Prime then Real.log (a : ℝ) else 0) := by
          by_cases hp : a.Prime
          · rw [if_pos hp]; exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ a))
          · rw [if_neg hp]
        rw [abs_of_nonneg hnn]
        linarith [hle, hlog3N_le]
      have hTN : (∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)
          = (Chebyshev.theta (b : ℝ) - (b : ℝ)) - (Chebyshev.theta (a : ℝ) - (a : ℝ))
            + (if a.Prime then Real.log (a : ℝ) else 0) := by
        rw [hsub, hbcast]; ring
      have hTbnd : |(∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
          ≤ 3 * X + 3 * X + X := by
        have hbb := hthbnd b (by omega : N ≤ b) hb3N
        have haa := hthbnd a haN ha3N
        rw [hTN]
        calc |(Chebyshev.theta (b : ℝ) - (b : ℝ)) - (Chebyshev.theta (a : ℝ) - (a : ℝ))
              + (if a.Prime then Real.log (a : ℝ) else 0)|
            ≤ |(Chebyshev.theta (b : ℝ) - (b : ℝ)) - (Chebyshev.theta (a : ℝ) - (a : ℝ))|
              + |(if a.Prime then Real.log (a : ℝ) else 0)| := abs_add_le _ _
          _ ≤ (|Chebyshev.theta (b : ℝ) - (b : ℝ)| + |Chebyshev.theta (a : ℝ) - (a : ℝ)|)
              + |(if a.Prime then Real.log (a : ℝ) else 0)| := by
                exact add_le_add (abs_sub_le_abs' _ _) le_rfl
          _ ≤ 3 * X + 3 * X + X := by linarith [hbb, haa, hga]
      have hBbound : (∑ m ∈ (Finset.Icc a b).filter (fun m => ¬ m.Coprime q),
          (if m.Prime then Real.log (m : ℝ) else 0)) ≤ (1 / 2) * Real.log (N : ℝ) := by
        have h := Commons.NumberTheory.PrimeNumberTheorem.not_coprime_prime_log_window_shift_le N q h (by omega : 1 ≤ N) hq hqN
        simpa [hadef, hbdef] using h
      have hsplit : (∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
            (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)
          = ((∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ))
            - (∑ m ∈ (Finset.Icc a b).filter (fun m => ¬ m.Coprime q),
                (if m.Prime then Real.log (m : ℝ) else 0)) := by
        linarith [hSB]
      have hfinal : |(∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
            (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)| ≤ 8 * X := by
        rw [hsplit]
        have h1 : |((∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ))
              - (∑ m ∈ (Finset.Icc a b).filter (fun m => ¬ m.Coprime q),
                  (if m.Prime then Real.log (m : ℝ) else 0))|
            ≤ |(∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
              + (1 / 2) * Real.log (N : ℝ) := by
          calc |((∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ))
                - (∑ m ∈ (Finset.Icc a b).filter (fun m => ¬ m.Coprime q),
                    (if m.Prime then Real.log (m : ℝ) else 0))|
              ≤ |(∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
                + |(∑ m ∈ (Finset.Icc a b).filter (fun m => ¬ m.Coprime q),
                    (if m.Prime then Real.log (m : ℝ) else 0))| := abs_sub_le_abs' _ _
            _ = |(∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
                + (∑ m ∈ (Finset.Icc a b).filter (fun m => ¬ m.Coprime q),
                    (if m.Prime then Real.log (m : ℝ) else 0)) := by rw [abs_of_nonneg hBnn]
            _ ≤ |(∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
                + (1 / 2) * Real.log (N : ℝ) := by linarith [hBbound]
        have h2 : |(∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
              + (1 / 2) * Real.log (N : ℝ) ≤ 8 * X := by
          linarith [hTbnd, hhalflog]
        linarith [h1, h2]
      have h8C : (8 : ℝ) ≤ max 8 K + 1 := by linarith [le_max_left (8 : ℝ) K]
      have hgoalX : (max 8 K + 1) * (N : ℝ) / (Real.log (N : ℝ)) ^ A = (max 8 K + 1) * X := by
        rw [hXdef]; ring
      rw [hgoalX]
      calc |(∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
              (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
          ≤ 8 * X := hfinal
        _ ≤ (max 8 K + 1) * X := mul_le_mul_of_nonneg_right h8C hXnn
    · have hNlt : N < N₀ := not_le.mp hbig
      have hNmem : N ∈ Finset.Icc 2 (N₀ - 1) := by
        rw [Finset.mem_Icc]; exact ⟨hN2, by omega⟩
      have htermnn : ∀ n ∈ Finset.Icc 2 (N₀ - 1),
          0 ≤ (((n : ℝ) + 1) * Real.log ((3 * n : ℕ) : ℝ) + (n : ℝ)) * (Real.log (n : ℝ)) ^ A / (n : ℝ) := by
        intro n hn
        have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have h1 : 0 ≤ ((n : ℝ) + 1) * Real.log ((3 * n : ℕ) : ℝ) + (n : ℝ) := by
          have hlog : 0 ≤ Real.log ((3 * n : ℕ) : ℝ) :=
            Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 3 * n))
          have hm : (0 : ℝ) ≤ ((n : ℝ) + 1) * Real.log ((3 * n : ℕ) : ℝ) :=
            mul_nonneg (by positivity) hlog
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have h2 : 0 ≤ (Real.log (n : ℝ)) ^ A :=
          Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) A
        have h3 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        exact div_nonneg (mul_nonneg h1 h2) (le_of_lt h3)
      have hleK : (((N : ℝ) + 1) * Real.log ((3 * N : ℕ) : ℝ) + (N : ℝ))
            * (Real.log (N : ℝ)) ^ A / (N : ℝ) ≤ K := by
        rw [hKdef]
        exact Finset.single_le_sum htermnn hNmem
      have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      have hpowpos : 0 < (Real.log (N : ℝ)) ^ A := Real.rpow_pos_of_pos hlogNpos A
      have hKN : ((N : ℝ) + 1) * Real.log ((3 * N : ℕ) : ℝ) + (N : ℝ)
          ≤ K * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) := by
        have hmul := mul_le_mul_of_nonneg_right hleK
          (show (0 : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ A from le_of_lt (div_pos hNposR hpowpos))
        have hsimp : (((N : ℝ) + 1) * Real.log ((3 * N : ℕ) : ℝ) + (N : ℝ))
              * (Real.log (N : ℝ)) ^ A / (N : ℝ) * ((N : ℝ) / (Real.log (N : ℝ)) ^ A)
            = ((N : ℝ) + 1) * Real.log ((3 * N : ℕ) : ℝ) + (N : ℝ) := by
          field_simp
        rwa [hsimp] at hmul
      have hNA : |(∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
            (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
          ≤ ((N : ℝ) + 1) * Real.log ((3 * N : ℕ) : ℝ) + (N : ℝ) := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hSle], by linarith [hSnn]⟩
      have hXnn : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ A := le_of_lt (div_pos hNposR hpowpos)
      have hKC : K ≤ max 8 K + 1 := by linarith [le_max_right (8 : ℝ) K]
      calc |(∑ m ∈ (Finset.Icc a b).filter (fun m => m.Coprime q),
              (if m.Prime then Real.log (m : ℝ) else 0)) - (N : ℝ)|
          ≤ ((N : ℝ) + 1) * Real.log ((3 * N : ℕ) : ℝ) + (N : ℝ) := hNA
        _ ≤ K * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) := hKN
        _ ≤ (max 8 K + 1) * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) :=
            mul_le_mul_of_nonneg_right hKC hXnn
        _ = (max 8 K + 1) * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring

end Commons.NumberTheory.PrimeNumberTheorem
