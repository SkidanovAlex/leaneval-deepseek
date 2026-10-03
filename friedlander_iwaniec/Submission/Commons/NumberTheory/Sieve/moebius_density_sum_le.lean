import Mathlib
import Submission.Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog

namespace Commons.NumberTheory.Sieve

open Finset

/-- Estimate **(2.4) of the companion paper "Asymptotic sieve for primes"**
(Friedlander–Iwaniec, Ann. of Math. 148 (1998) 1041–1065): for a multiplicative density
`g` with `0 ≤ g(p) < 1`, `g(p) ≪ 1/p` and `∑_{p ≤ y} g(p) = log log y + c + O((log y)^{-10})`,
the Möbius-weighted sum is `∑_{d ≤ y, (d,ϱ)=1} μ(d) g(d) ≪ β_ϱ (log y)^{-6}`, where
`β_ϱ = ∏_{p ∣ ϱ} (1 + p^{-1/2})`.  This is the analytic core of §§4–5 of the companion. -/
theorem moebius_density_sum_le {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ϱ y : ℕ), 1 ≤ ϱ → 2 ≤ y →
      |∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d ϱ),
          (ArithmeticFunction.moebius d : ℝ) * g d|
        ≤ C * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) *
            (Real.log y) ^ (-(6 : ℤ)) := by
  classical
  -- Squarefree truncation of `g`; the Möbius sum only sees squarefree integers.
  let g' : ℕ → ℝ := fun n => if Squarefree n then g n else 0
  have hg'_eq : ∀ n, Squarefree n → g' n = g n := by
    intro n hn; dsimp only [g']; rw [if_pos hn]
  have hg'_zero : ∀ n, ¬ Squarefree n → g' n = 0 := by
    intro n hn; dsimp only [g']; rw [if_neg hn]
  -- Nonnegativity everywhere
  have hg'_nonneg : ∀ n, 0 ≤ g' n := by
    intro n
    by_cases hn : Squarefree n
    · rw [hg'_eq n hn, g_eq_prod_primeFactors g hmul hg1 n hn]
      exact Finset.prod_nonneg (fun p hpmem => (hp p (Nat.prime_of_mem_primeFactors hpmem)).1)
    · rw [hg'_zero n hn]
  -- Multiplicativity
  have hg'_one : g' 1 = 1 := by
    rw [hg'_eq 1 squarefree_one]; exact hg1
  have hg'_mul : ∀ m n : ℕ, Nat.Coprime m n → g' (m * n) = g' m * g' n := by
    intro m n hmn
    by_cases hsq : Squarefree (m * n)
    · obtain ⟨hm, hn⟩ := (Nat.squarefree_mul hmn).mp hsq
      rw [hg'_eq (m * n) hsq, hg'_eq m hm, hg'_eq n hn, hmul m n hmn]
    · have hkey : ¬ (Squarefree m ∧ Squarefree n) := fun h => hsq ((Nat.squarefree_mul hmn).mpr h)
      rw [hg'_zero (m * n) hsq]
      rcases not_and_or.mp hkey with hm | hn
      · rw [hg'_zero m hm]; ring
      · rw [hg'_zero n hn]; ring
  -- Prime values
  have hg'_lt : ∀ p : ℕ, p.Prime → g' p < 1 := by
    intro p hpp
    rw [hg'_eq p (Irreducible.squarefree hpp)]
    exact (hp p hpp).2
  have hg'_le : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g' p ≤ C / (p : ℝ) := by
    obtain ⟨C0, hC0⟩ := hbound
    refine ⟨max C0 1, by positivity, fun p hpp => ?_⟩
    rw [hg'_eq p (Irreducible.squarefree hpp)]
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have h2 : C0 / (p : ℝ) ≤ max C0 1 / (p : ℝ) :=
      (div_le_div_iff_of_pos_right hp0).mpr (le_max_left C0 1)
    exact le_trans (hC0 p hpp) h2
  -- The prime-sum hypothesis, transposed to `g'` and to the `primesLE` form.
  have hg'_sum : ∃ c C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE, g' p) - (Real.log (Real.log y) + c)| ≤
        C * (Real.log y) ^ (-10 : ℝ) := by
    obtain ⟨c, C, h9c⟩ := h9
    refine ⟨c, max C 1, by positivity, fun y hy => ?_⟩
    have hpr : (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime = (⌊y⌋₊).primesLE := by
      ext p
      rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨h2, hple⟩, hpp⟩; exact ⟨hple, hpp⟩
      · rintro ⟨hple, hpp⟩; exact ⟨⟨hpp.two_le, hple⟩, hpp⟩
    have hsum_eq : (∑ p ∈ (⌊y⌋₊).primesLE, g' p)
        = (∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) := by
      rw [← hpr]
      apply Finset.sum_congr rfl
      intro p hpmem
      exact hg'_eq p (Irreducible.squarefree (Finset.mem_filter.mp hpmem).2)
    have hconv : (Real.log y) ^ (-(10 : ℤ)) = (Real.log y) ^ (-10 : ℝ) := by
      rw [← Real.rpow_intCast (Real.log y) (-(10 : ℤ))]; norm_num
    have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
    have hpos : 0 < (Real.log y) ^ (-10 : ℝ) := Real.rpow_pos_of_pos hlogpos _
    have habs : (∑ p ∈ (⌊y⌋₊).primesLE, g' p) - (Real.log (Real.log y) + c)
        = (∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p)
            - Real.log (Real.log y) - c := by
      rw [hsum_eq]; ring
    rw [habs]
    refine le_trans (h9c y hy) ?_
    rw [hconv]
    exact mul_le_mul_of_nonneg_right (le_max_left C 1) hpos.le
  -- Apply the general Friedman–Iwaniec (2.4) estimate in the commons.
  obtain ⟨C, hCpos, hbound'⟩ :=
    sieve_mu_sum_coprime_powLog g' hg'_nonneg hg'_one hg'_mul hg'_lt hg'_le hg'_sum
  refine ⟨C, hCpos, fun ϱ y hϱ hy => ?_⟩
  -- The two sums agree term by term: `μ` kills the non-squarefree integers.
  have hsum_eq : (∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d ϱ),
        (ArithmeticFunction.moebius d : ℝ) * g d)
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ),
        (ArithmeticFunction.moebius d : ℝ) * g' d := by
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hs : Squarefree d
    · rw [hg'_eq d hs]; simp only [hs, true_and]
    · have hmu : (ArithmeticFunction.moebius d : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; norm_num
      rw [hmu]; simp [hs]
  have hexp : (Real.log (y:ℝ)) ^ (-6 : ℝ) = (Real.log (y:ℝ)) ^ (-(6 : ℤ)) := by
    simp [Real.rpow_intCast]
  rw [hsum_eq, ← hexp]
  exact hbound' ϱ y hϱ hy

end Commons.NumberTheory.Sieve
