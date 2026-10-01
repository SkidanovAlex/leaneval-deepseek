import Mathlib
import Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex
import Submission.Work.LinnikAreas.Density4.sum_divisors_smooth_moebius

namespace Work.ZeroDensity.Jutila

open Finset

/-- `U t 1 = Σ_{k ≤ t} μ(k)/k`: at `l = 1` the coprimality filter is trivially satisfied. -/
private lemma U_one_eq_sum (t : ℕ) :
    U t 1 = ∑ k ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) := by
  have hset : (Finset.Icc 1 t).filter (fun m => Nat.Coprime m 1) = Finset.Icc 1 t := by
    ext m
    simp
  rw [U]
  exact Finset.sum_congr hset (fun m _ => rfl)

/-- For `d ≠ 0`, `rad d ∣ l` iff every prime divisor of `d` divides `l`. -/
private lemma rad_dvd_iff_forall_prime {d l : ℕ} (hd : d ≠ 0) :
    rad d ∣ l ↔ ∀ p : ℕ, p.Prime → p ∣ d → p ∣ l := by
  constructor
  · intro h p hp hpd
    have hprad : p ∣ rad d := by
      rw [rad]
      exact Finset.dvd_prod_of_mem (fun q : ℕ => q)
        (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩)
    exact hprad.trans h
  · intro h
    rcases eq_or_ne l 0 with hl | hl
    · subst hl
      exact dvd_zero _
    · rw [rad, Nat.prod_primeFactors_dvd_iff hl]
      intro p hp
      obtain ⟨hp', hpd, _⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hp', h p hp' hpd, hl⟩

/-- The `SmoothOf` predicate (`d ∣ l ^ d`) agrees with `rad d ∣ l` for nonzero `d`. -/
private lemma smoothOf_iff_rad_dvd {d l : ℕ} (hd : d ≠ 0) :
    Work.LinnikAreas.Density4.SmoothOf d l ↔ rad d ∣ l :=
  (Work.LinnikAreas.Density4.smoothOf_iff_prime_dvd hd).trans
    (rad_dvd_iff_forall_prime hd).symm

/-- (To be placed in namespace `Work.ZeroDensity.Jutila`, importing
`Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs`, which defines
`U y l = Σ_{m ≤ y, (m,l)=1} μ(m)/m` and `rad n = ∏ p ∈ n.primeFactors, p`.)
**Sieve expansion of the coprime Möbius reciprocal sum:**
`U y l = Σ_{d ≤ y, rad d ∣ l} (1/d)·U (y/d) 1`.  It comes from the Möbius-inversion
identity `μ(m)·[(m,l)=1] = Σ_{d ∣ m, rad d ∣ l} μ(m/d)` (the coefficient identity of the
Dirichlet series identity `Π_{p∤l}(1-p^{-s}) = (Σ_{rad d ∣ l} d^{-s})·(1/ζ(s))`), summed
against `1/m` and reindexed by `m = d·k`. -/
theorem sieveU_expansion (y l : ℕ) (hl : 1 ≤ l) :
    U y l = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => rad d ∣ l),
      (1 / (d : ℝ)) * U (y / d) 1 := by
  -- Replace the filter condition `rad d ∣ l` by the equivalent, decidable `SmoothOf d l`.
  have hfilter : (Finset.Icc 1 y).filter (fun d => rad d ∣ l)
      = (Finset.Icc 1 y).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l) := by
    apply Finset.filter_congr
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    exact (smoothOf_iff_rad_dvd (by omega)).symm
  rw [hfilter]
  -- Expand `U (y/d) 1` termwise.
  have h1 : ∀ d : ℕ, (1 / (d : ℝ)) * U (y / d) 1
      = ∑ m ∈ Finset.Icc 1 (y / d),
          (1 / (d : ℝ)) * ((ArithmeticFunction.moebius m : ℝ) / (m : ℝ)) := by
    intro d
    rw [U_one_eq_sum, Finset.mul_sum]
  -- Reindex the pairs `(d, m)` with `d` smooth and `m ≤ y/d` by `(n, d)` with `d ∣ n`.
  have hRHS : (∑ d ∈ (Finset.Icc 1 y).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
        (1 / (d : ℝ)) * U (y / d) 1)
      = ∑ n ∈ Finset.Icc 1 y,
          (∑ d ∈ n.divisors.filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
              (ArithmeticFunction.moebius (n / d) : ℝ)) * (1 / (n : ℝ)) := by
    calc (∑ d ∈ (Finset.Icc 1 y).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
            (1 / (d : ℝ)) * U (y / d) 1)
        = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
            ∑ m ∈ Finset.Icc 1 (y / d),
              (1 / (d : ℝ)) * ((ArithmeticFunction.moebius m : ℝ) / (m : ℝ)) :=
          Finset.sum_congr rfl (fun d _ => h1 d)
      _ = ∑ n ∈ Finset.Icc 1 y,
            ∑ d ∈ n.divisors.filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
              (1 / (d : ℝ))
                * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ)) :=
          Work.LinnikAreas.Density4.sum_Icc_div_reindex y
            (fun d => Work.LinnikAreas.Density4.SmoothOf d l)
            (fun d m => (1 / (d : ℝ)) * ((ArithmeticFunction.moebius m : ℝ) / (m : ℝ)))
      _ = ∑ n ∈ Finset.Icc 1 y,
            (∑ d ∈ n.divisors.filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
                (ArithmeticFunction.moebius (n / d) : ℝ)) * (1 / (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro n _
          trans ∑ d ∈ n.divisors.filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
              (ArithmeticFunction.moebius (n / d) : ℝ) * (1 / (n : ℝ))
          · apply Finset.sum_congr rfl
            intro d hd
            obtain ⟨hdmem, _⟩ := Finset.mem_filter.mp hd
            obtain ⟨hdvd, hnne⟩ := Nat.mem_divisors.mp hdmem
            have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hnne)).ne'
            rw [Nat.cast_div_charZero hdvd]
            field_simp
          · rw [Finset.sum_mul]
  -- The left-hand side, with the coprimality filter written as an indicator factor.
  have hLHS : U y l = ∑ n ∈ Finset.Icc 1 y,
        (if Nat.Coprime n l then (ArithmeticFunction.moebius n : ℝ) else 0) * (1 / (n : ℝ)) := by
    rw [U, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : Nat.Coprime n l
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [hRHS, hLHS]
  -- Apply the Möbius inversion identity to the inner divisor sum.
  apply Finset.sum_congr rfl
  intro n _
  rw [Work.LinnikAreas.Density4.sum_divisors_smooth_moebius n l]

end Work.ZeroDensity.Jutila
