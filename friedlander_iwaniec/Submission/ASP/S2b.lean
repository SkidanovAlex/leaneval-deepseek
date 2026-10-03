/-
  Companion paper ("Asymptotic sieve for primes"), §2: the technical reductions
  `(R) ⟹ (R′)` (and the parallel `(B) ⟹ (B′)`).

  * `sum_tau_pow_mul_Ad_le` : **(2.1)** — the crude bound (1.6) implies
    `∑_{d ≤ x} τ(d)^{20/3}A_d(x) ≪ A(x)(log x)^{2^48}` (the paper's exponent is `2^20`;
    our chain is cruder but any exponent `≥ 3` suffices for `(R′)`, see below).
  * `sum_squarefree_tau_pow_mul_abs_rd_le` : **(2.3)** — combining (2.1) and (2.2).
  * `Rprime_of_R_and_23'` : **(R) + (2.3) ⟹ (R′)** by Hölder, with the exponent-matched pair
    `(R)` at `(log D)^{-2^50}` and (2.3) at `(log D)^{2^48}`.
-/
import Mathlib
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.Analysis.MeanInequalities.sum_rpow_holder

open Finset

noncomputable section

namespace Submission.ASP


/-! ### §2: the divisor-sum estimates -/

/-- The double divisor swap `∑_{d ≤ x}∑_{n ≤ x, d | n} = ∑_{n ≤ x}∑_{d | n}`. -/
lemma sum_dvd_swap (x : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), f d n)
      = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d n := by
  classical
  have h1 : ∀ d : ℕ, (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), f d n)
      = ∑ n ∈ Finset.Icc 1 x, if d ∣ n then f d n else 0 := by
    intro d; rw [Finset.sum_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_filter]
  congr 1
  ext d
  rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnx : n ≤ x := (Finset.mem_Icc.mp hn).2
  constructor
  · rintro ⟨hd, hdn⟩
    exact ⟨hdn, by omega⟩
  · rintro ⟨hdn, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdn (by omega),
      le_trans (Nat.le_of_dvd (by omega) hdn) hnx⟩, hdn⟩

/-- **(2.1)** of the companion paper (with a generous exponent): the crude bound (1.6) implies
`∑_{d ≤ x} τ(d)^{20/3} A_d(x) ≪ A(x)(log x)^{2^48}`. -/
theorem sum_tau_pow_mul_Ad_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {A C : ℝ}
    (hA : 0 < A) (hC : 0 < C)
    (h16 : ∀ x d : ℕ, 1 ≤ d → d ^ 3 ≤ x →
      (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n)
        ≤ C * (d : ℝ)⁻¹ * ((d.divisors.card : ℝ) ^ 8) * A) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ x : ℕ,
      (∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) *
        (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n))
        ≤ C' * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48) := by
  classical
  obtain ⟨C₄, hC₄pos, hC₄⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 48
  refine ⟨C * 2 ^ 40 * C₄, by positivity, ?_⟩
  intro x
  -- ### Step 1: pointwise, `τ(n)^8 ≤ ∑_{d | n, d³ ≤ n} (2τ(d))^{40}`
  have hstep1 : ∀ n : ℕ, 1 ≤ n →
      ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ))
        ≤ ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ n),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) := by
    intro n hn
    obtain ⟨d, hdvd, hdle, hdb⟩ :=
      Commons.NumberTheory.Divisors.small_divisor_tau_le (k := 3) (by norm_num) hn
    have h2 : ((n.divisors.card : ℝ)) ^ ((8:ℕ):ℝ)
        ≤ ((2 * (d.divisors.card : ℝ)) ^ ((3 : ℝ) * Real.log 3 / Real.log 2)) ^ ((8:ℕ):ℝ) :=
      Real.rpow_le_rpow (x := (n.divisors.card : ℝ))
        (y := (2 * (d.divisors.card : ℝ)) ^ ((3 : ℝ) * Real.log 3 / Real.log 2))
        (z := 8) (by positivity) hdb (by norm_num)
    have hpos2 : (1 : ℝ) ≤ 2 * (d.divisors.card : ℝ) := by
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hpos : (1 : ℝ) ≤ (d.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d,
          (Nat.pos_of_dvd_of_pos hdvd (by omega)).ne'⟩⟩
      linarith
    have h3 : ((2 * (d.divisors.card : ℝ)) ^ ((3 : ℝ) * Real.log 3 / Real.log 2)) ^ ((8:ℕ):ℝ)
        = (2 * (d.divisors.card : ℝ)) ^ (((3 : ℝ) * Real.log 3 / Real.log 2) * 8) :=
      (Real.rpow_mul (by positivity : (0:ℝ) ≤ 2 * (d.divisors.card : ℝ)) _ _).symm
    have hexp : ((3 : ℝ) * Real.log 3 / Real.log 2) * 8 ≤ 40 := by
      have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hmono : (3:ℝ) * Real.log 3 ≤ 5 * Real.log 2 := by
        have h27 : Real.log (27:ℝ) = 3 * Real.log 3 := by
          rw [show (27:ℝ) = 3^3 by norm_num, Real.log_pow]; ring
        have h32 : Real.log (32:ℝ) = 5 * Real.log 2 := by
          rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; ring
        have := Real.log_le_log (by norm_num : (0:ℝ) < 27) (by norm_num : (27:ℝ) ≤ 32)
        linarith
      have hthis : ((3 : ℝ) * Real.log 3 / Real.log 2) * 8
          = (3 * Real.log 3 * 8) / Real.log 2 := by ring
      rw [hthis, div_le_iff₀ h2pos]
      linarith
    have h4 : (2 * (d.divisors.card : ℝ)) ^ (((3 : ℝ) * Real.log 3 / Real.log 2) * 8)
        ≤ (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpos2 hexp
    have hmem : d ∈ n.divisors.filter (fun e => e ^ 3 ≤ n) :=
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, by omega⟩, hdle⟩
    refine le_trans h2 (le_trans (le_of_eq h3) (le_trans h4 ?_))
    exact Finset.single_le_sum (f := fun e => (2 * (e.divisors.card : ℝ)) ^ ((40:ℕ):ℝ))
      (fun e _ => by positivity) hmem
  -- ### Step 2: `∑_d τ(d)^{20/3} A_d ≤ ∑_n a_n τ(n)^8`
  have hstep2 : ∀ x : ℕ,
      (∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) *
        (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n))
      ≤ ∑ n ∈ Finset.Icc 1 x, a n * ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)) := by
    intro x
    have h1 : (∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) *
        (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n))
        = ∑ d ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n),
            a n * ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [h1, sum_dvd_swap]
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hsub : ∑ d ∈ n.divisors, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ))
        ≤ ∑ d ∈ n.divisors, ((n.divisors.card : ℝ) ^ ((7:ℕ):ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hle : (d.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (Nat.divisors_subset_of_dvd (n := n) (m := d) (Nat.one_le_iff_ne_zero.mp hn1) hdvd)
      have hτ : (1 : ℝ) ≤ (d.divisors.card : ℝ) := by
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, hdpos.ne'⟩⟩
      calc (d.divisors.card : ℝ) ^ (20 / 3 : ℝ)
          ≤ (d.divisors.card : ℝ) ^ ((7:ℕ):ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hτ (by norm_num)
        _ ≤ (n.divisors.card : ℝ) ^ ((7:ℕ):ℝ) :=
            Real.rpow_le_rpow (by positivity) hle (by norm_num)
    have hsub2 : a n * ∑ d ∈ n.divisors, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ))
        ≤ a n * ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)) := by
      refine le_trans (mul_le_mul_of_nonneg_left hsub (ha n)) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hτn : (0:ℝ) < (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩⟩
      rw [show (↑n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)
          = (↑n.divisors.card) * (↑n.divisors.card) ^ ((7:ℕ):ℝ) by
        rw [show ((8:ℕ):ℝ) = (1:ℝ) + ((7:ℕ):ℝ) by norm_num,
          Real.rpow_add hτn, Real.rpow_one]]
    rw [← Finset.mul_sum]
    exact hsub2
  -- ### Step 3: `∑_n a_n τ(n)^8 ≤ ∑_{d³ ≤ x} (2τ(d))^{40} A_d(x)`
  have hstep3 : ∀ x : ℕ,
      (∑ n ∈ Finset.Icc 1 x, a n * ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)))
        ≤ ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n) := by
    intro x
    have ha1 : (∑ n ∈ Finset.Icc 1 x, a n * ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)))
        ≤ ∑ n ∈ Finset.Icc 1 x, a n * ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnx : n ≤ x := (Finset.mem_Icc.mp hn).2
      have hsub : n.divisors.filter (fun e => e ^ 3 ≤ n)
          ⊆ n.divisors.filter (fun e => e ^ 3 ≤ x) := by
        intro d hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, le_trans hd.2 (by exact_mod_cast hnx)⟩
      have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun e _ _ => by positivity : ∀ e ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
          e ∉ n.divisors.filter (fun e => e ^ 3 ≤ n) → (0:ℝ) ≤ (2 * (e.divisors.card : ℝ)) ^ (40:ℝ))
      exact mul_le_mul_of_nonneg_left (le_trans (hstep1 n (Finset.mem_Icc.mp hn).1) h) (ha n)
    refine le_trans ha1 ?_
    have hswap : (∑ n ∈ Finset.Icc 1 x, a n * ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ))
        = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n) := by
      have h1 : ∀ n : ℕ, a n * ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ)
          = ∑ d ∈ n.divisors, (if d ^ 3 ≤ x then
              (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) * a n else 0) := by
        intro n
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d _
        by_cases h : d ^ 3 ≤ x
        · simp only [h, if_true]; ring
        · simp only [h, if_false]
      simp only [h1]
      rw [← sum_dvd_swap]
      have h2 : ∀ d : ℕ, (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n),
            (if d ^ 3 ≤ x then (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) * a n else 0))
          = (if d ^ 3 ≤ x then
              ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n),
                (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) * a n else 0) := by
        intro d
        by_cases h : d ^ 3 ≤ x
        · simp only [h, if_true]
        · simp only [h, if_false, Finset.sum_const_zero]
      simp only [h2]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
    rw [hswap]
  -- ### Step 4: apply (1.6) and `sum_tau_pow_div_le`
  have hstep4 : ∀ x : ℕ,
      (∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n))
        ≤ C * 2 ^ 40 * C₄ * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48) := by
    intro x
    rcases Nat.eq_zero_or_pos x with hx0 | hxpos
    · subst hx0
      have hempty : (Finset.Icc 1 0).filter (fun d => d ^ 3 ≤ 0) = ∅ := by
        rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1)]
        rfl
      rw [hempty, Finset.sum_empty]
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le ?_) hC₄pos.le) hA.le) ?_
      · norm_num
      · apply pow_nonneg
        apply Real.log_nonneg
        norm_num
    · have hterm : ∀ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
          (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n)
            ≤ C * 2 ^ 40 * A * (((d.divisors.card : ℝ) ^ 48) / (d : ℝ)) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
        have hd3 : d ^ 3 ≤ x := (Finset.mem_filter.mp hd).2
        have hS := h16 x d hd1 hd3
        have hdpos : (0:ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        calc (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n)
            ≤ (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
                (C * (d : ℝ)⁻¹ * ((d.divisors.card : ℝ) ^ 8) * A) :=
              mul_le_mul_of_nonneg_left hS (by positivity)
          _ = C * 2 ^ 40 * A * (((d.divisors.card : ℝ) ^ 48) / (d : ℝ)) := by
              rw [Real.rpow_natCast]
              ring
      calc ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n)
          ≤ ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
              C * 2 ^ 40 * A * (((d.divisors.card : ℝ) ^ 48) / (d : ℝ)) :=
            Finset.sum_le_sum hterm
        _ = C * 2 ^ 40 * A *
              ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
                (((d.divisors.card : ℝ) ^ 48) / (d : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ C * 2 ^ 40 * A * (C₄ * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine le_trans ?_ (hC₄ x hxpos)
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro d hd _
            positivity
        _ = C * 2 ^ 40 * C₄ * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48) := by ring
  exact le_trans (hstep2 x) (le_trans (hstep3 x) (hstep4 x))


/-- **(2.3)** of the companion paper: combining (2.1) and (2.2) (and the defining relation
`A_d(x) = g(d)A(x) + r_d(x)`). -/
theorem sum_squarefree_tau_pow_mul_abs_rd_le {Ad r g : ℕ → ℝ} {A C₁ C₂ : ℝ}
    (hA : 0 < A) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (h21 : ∀ x : ℕ,
      (∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * Ad d)
        ≤ C₁ * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48))
    (h22 : ∀ x : ℕ,
      (∑ d ∈ (Finset.Icc 1 x).filter Squarefree, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * g d)
        ≤ C₂ * (Real.log ((x : ℝ) + 2)) ^ 11)
    (hrd : ∀ d : ℕ, Ad d = g d * A + r d)
    (hAd : ∀ d : ℕ, 0 ≤ Ad d) (hg : ∀ d : ℕ, 0 ≤ g d) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ x : ℕ,
      (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
        ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * |r d|)
        ≤ C₃ * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48) := by
  classical
  refine ⟨C₁ + 2 * C₂, by positivity, ?_⟩
  intro x
  rcases Nat.eq_zero_or_pos x with hx0 | hxpos
  · subst hx0
    rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.filter_empty, Finset.sum_empty]
    refine mul_nonneg (mul_nonneg (by positivity) hA.le) ?_
    apply pow_nonneg
    apply Real.log_nonneg
    norm_num
  have hlog1 : (1:ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxpos
    have h3 : (3:ℝ) ≤ (x:ℝ) + 2 := by linarith
    have he : Real.exp 1 ≤ (3:ℝ) := by
      have h := Real.exp_one_lt_d9; linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) he
      _ ≤ Real.log ((x:ℝ) + 2) := Real.log_le_log (by norm_num) h3
  have hL0 : (0:ℝ) < Real.log ((x : ℝ) + 2) := lt_of_lt_of_le one_pos hlog1
  have h1 : ∀ d : ℕ, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * |r d|
      ≤ ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * (Ad d + g d * A) := by
    intro d
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hrd' : r d = Ad d - g d * A := by have := hrd d; linarith
    rw [hrd']
    calc |Ad d - g d * A| ≤ |Ad d| + |g d * A| := abs_sub _ _
      _ = Ad d + g d * A := by
          rw [abs_of_nonneg (hAd d), abs_of_nonneg (mul_nonneg (hg d) hA.le)]
  have h2 : ∀ d ∈ (Finset.Icc 1 x).filter Squarefree,
      ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * (Ad d + g d * A)
        = ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * Ad d
          + A * (((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * g d) := by
    intro d _; ring
  have h3 : (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
        ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * (Ad d + g d * A))
      = (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
          ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * Ad d)
        + A * (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
            ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * g d) := by
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.mul_sum]
  have h4 : (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
          ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * Ad d)
      ≤ ∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * Ad d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => mul_nonneg (by positivity) (hAd d))
  have h5 : (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
        ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * |r d|)
      ≤ C₁ * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48)
        + A * (C₂ * (Real.log ((x : ℝ) + 2)) ^ 11) := by
    calc (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
          ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * |r d|)
        ≤ ∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
            ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * (Ad d + g d * A) :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ = (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
            ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * Ad d)
          + A * (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
              ((d.divisors.card : ℝ) ^ (20 / 3 : ℝ)) * g d) := h3
      _ ≤ C₁ * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48)
          + A * (C₂ * (Real.log ((x : ℝ) + 2)) ^ 11) :=
          add_le_add (le_trans h4 (h21 x)) (mul_le_mul_of_nonneg_left (h22 x) hA.le)
  refine le_trans h5 ?_
  set L : ℝ := (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48) with hLdef
  have h11' : (Real.log ((x : ℝ) + 2)) ^ 11 ≤ L := by
    rw [hLdef]; exact pow_le_pow_right₀ hlog1 (by norm_num)
  have hLnn : (0:ℝ) ≤ L := by
    rw [hLdef]; apply pow_nonneg; exact le_of_lt hL0
  have hstep : A * (C₂ * (Real.log ((x : ℝ) + 2)) ^ 11) ≤ C₂ * (A * L) := by
    calc A * (C₂ * (Real.log ((x : ℝ) + 2)) ^ 11)
        = C₂ * (A * (Real.log ((x : ℝ) + 2)) ^ 11) := by ring
      _ ≤ C₂ * (A * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h11' hA.le) hC₂.le
  have hgoal : C₁ * A * L + C₂ * (A * L) = (C₁ + C₂) * A * L := by ring
  calc C₁ * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48)
        + A * (C₂ * (Real.log ((x : ℝ) + 2)) ^ 11)
      = C₁ * A * L + A * (C₂ * (Real.log ((x : ℝ) + 2)) ^ 11) := by rw [hLdef]
    _ ≤ C₁ * A * L + C₂ * (A * L) := add_le_add le_rfl hstep
    _ = (C₁ + C₂) * A * L := hgoal
    _ ≤ (C₁ + 2 * C₂) * A * L := by
        have hAL : (0:ℝ) ≤ A * L := mul_nonneg hA.le hLnn
        nlinarith [hAL, hC₂]
    _ = (C₁ + 2 * C₂) * A * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 48) := by rw [hLdef]

/-- **Companion §2, the Hölder step** (exponent-matched variant of `S2.Rprime_of_R_and_23`):
`(R)` at `(log D)^{-2^50}` together with `(2.3)` at `(log D)^{2^48}` implies `(R′)`.
Hölder gives `(3/4)·2^48 − (1/4)·2^50 = −2^46 ≤ −3`. -/
theorem Rprime_of_R_and_23' {D : ℕ} (hD : 1 ≤ D) {r : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hlog1 : 1 ≤ Real.log (D : ℝ))
    (hR : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r d|)
      ≤ A * (Real.log (D : ℝ)) ^ (-((2 : ℝ) ^ 50)))
    (h23 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (20 / 3 : ℝ) * |r d|)
      ≤ A * (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ 48)) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, ((d.divisors.card : ℝ)) ^ 5 * |r d|)
      ≤ A * (Real.log (D : ℝ)) ^ (-(3 : ℝ)) := by
  classical
  set x : ℝ := Real.log (D : ℝ) with hx
  have hx0 : 0 ≤ x := le_trans zero_le_one hlog1
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hlog1
  have hholder := Commons.Analysis.MeanInequalities.sum_rpow_holder
    (F := fun d : ℕ => ((d.divisors.card : ℝ)))
    (R := fun d : ℕ => if Squarefree d then |r d| else 0)
    (fun d => by positivity) (fun d => by positivity) D
  have hLs : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ 5 * |r d|)
      = ∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ)) ^ 5 * (if Squarefree d then |r d| else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : Squarefree d <;> simp [h]
  have hUs : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (20 / 3 : ℝ) * |r d|)
      = ∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ)) ^ (20 / 3 : ℝ) * (if Squarefree d then |r d| else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : Squarefree d <;> simp [h]
  have hVs : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r d|)
      = ∑ d ∈ Finset.Icc 1 D, (if Squarefree d then |r d| else 0) := by
    rw [Finset.sum_filter]
  have hkey : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ 5 * |r d|)
      ≤ (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((d.divisors.card : ℝ)) ^ (20 / 3 : ℝ) * |r d|) ^ (3 / 4 : ℝ)
        * (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r d|) ^ (1 / 4 : ℝ) := by
    rw [hLs, hUs, hVs]
    exact hholder
  refine le_trans hkey ?_
  have hU0 : 0 ≤ (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (20 / 3 : ℝ) * |r d|) :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (by positivity) (abs_nonneg _))
  have hV0 : 0 ≤ (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r d|) :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hApos : 0 ≤ A * x ^ ((2 : ℝ) ^ 48) := mul_nonneg hA (Real.rpow_nonneg hx0 _)
  refine le_trans (mul_le_mul (Real.rpow_le_rpow hU0 h23 (by norm_num))
    (Real.rpow_le_rpow hV0 hR (by norm_num)) (Real.rpow_nonneg hV0 _)
    (Real.rpow_nonneg hApos _)) ?_
  have hexp : ((2 : ℝ) ^ 48) * (3 / 4) + (-((2 : ℝ) ^ 50)) * (1 / 4) = -((2 : ℝ) ^ 46) := by
    norm_num
  have step1 : (A * x ^ ((2 : ℝ) ^ 48)) ^ (3 / 4 : ℝ)
        * (A * x ^ (-((2 : ℝ) ^ 50))) ^ (1 / 4 : ℝ)
      = (A ^ (3 / 4 : ℝ) * A ^ (1 / 4 : ℝ))
        * (x ^ (((2 : ℝ) ^ 48) * (3 / 4)) * x ^ ((-((2 : ℝ) ^ 50)) * (1 / 4))) := by
    rw [Real.mul_rpow hA (Real.rpow_nonneg hx0 _), Real.mul_rpow hA (Real.rpow_nonneg hx0 _),
      ← Real.rpow_mul hx0, ← Real.rpow_mul hx0]
    ring
  have step2 : (A ^ (3 / 4 : ℝ) * A ^ (1 / 4 : ℝ))
        * (x ^ (((2 : ℝ) ^ 48) * (3 / 4)) * x ^ ((-((2 : ℝ) ^ 50)) * (1 / 4)))
      = A * x ^ (-((2 : ℝ) ^ 46)) := by
    rcases eq_or_lt_of_le hA with hA0 | hA0
    · rw [← hA0]; simp
    · rw [← Real.rpow_add hA0, ← Real.rpow_add hxpos,
        show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one, hexp]
  rw [step1, step2]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)) hA


end Submission.ASP

end
