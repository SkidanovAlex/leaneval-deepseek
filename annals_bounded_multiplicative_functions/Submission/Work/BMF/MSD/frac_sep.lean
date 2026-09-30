import Mathlib
import Submission.Work.BMF.MSD.basic
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.MSD

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF
open Work.BMF.MSD

/-- The reduced fractions `a/p`, `p` prime in `[P,Q]`, `1 ≤ a < p`, are `1/Q²`-separated in
circular distance. -/
theorem frac_sep (P Q : ℝ) (hP : 2 ≤ P) (hQ : P ≤ Q)
    {p q a b : ℕ} (hp : p ∈ primesIn P Q) (hq : q ∈ primesIn P Q)
    (ha : a ∈ Finset.Ico 1 p) (hb : b ∈ Finset.Ico 1 q) (hne : (p, a) ≠ (q, b)) :
    1 / Q ^ 2 ≤ circDist ((a : ℝ) / p - (b : ℝ) / q) := by
  -- Extract primality and the size bound `p, q ≤ Q` from membership in `primesIn P Q`.
  have hpprime : p.Prime := by
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter] at hp; exact hp.2
  have hqprime : q.Prime := by
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter] at hq; exact hq.2
  have hp_le : (p:ℝ) ≤ Q := by
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter] at hp
    obtain ⟨hmem, _⟩ := hp
    rw [Finset.mem_Icc] at hmem
    obtain ⟨_, hhi⟩ := hmem
    calc (p:ℝ) ≤ (⌊Q⌋₊ : ℕ) := by exact_mod_cast hhi
      _ ≤ Q := Nat.floor_le (by linarith)
  have hq_le : (q:ℝ) ≤ Q := by
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter] at hq
    obtain ⟨hmem, _⟩ := hq
    rw [Finset.mem_Icc] at hmem
    obtain ⟨_, hhi⟩ := hmem
    calc (q:ℝ) ≤ (⌊Q⌋₊ : ℕ) := by exact_mod_cast hhi
      _ ≤ Q := Nat.floor_le (by linarith)
  have ha1 : 1 ≤ a := (Finset.mem_Ico.mp ha).1
  have ha2 : a < p := (Finset.mem_Ico.mp ha).2
  have hb1 : 1 ≤ b := (Finset.mem_Ico.mp hb).1
  have hb2 : b < q := (Finset.mem_Ico.mp hb).2
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqprime.pos
  -- The integer numerator of the difference and the denominator `D = p q`.
  set K : ℤ := (a:ℤ)*(q:ℤ) - (b:ℤ)*(p:ℤ) with hK
  set N : ℤ := (p:ℤ)*(q:ℤ) with hN
  set D : ℝ := (p:ℝ)*(q:ℝ) with hD
  -- The integer nearest to the difference.
  set m : ℤ := ⌊(a:ℝ)/p - (b:ℝ)/q + 1/2⌋ with hm
  have hDpos : 0 < D := by rw [hD]; exact mul_pos hppos hqpos
  have hNcast : ((N:ℤ):ℝ) = D := by rw [hN, hD]; push_cast; ring
  have ht : (a:ℝ)/p - (b:ℝ)/q = (K:ℝ)/D := by
    rw [hK, hD]; push_cast; field_simp
  -- `a/p = b/q` would force `(p,a) = (q,b)`, so the numerator is nonzero.
  have hK_ne : K ≠ 0 := by
    intro h0
    rw [hK] at h0
    have heq : a * q = b * p := by
      have h2 : ((a*q : ℕ) : ℤ) = ((b*p : ℕ) : ℤ) := by
        push_cast; linarith
      exact Nat.cast_injective h2
    have hpa : p ∣ a * q := by rw [heq]; exact dvd_mul_left p b
    rcases hpprime.dvd_mul.mp hpa with hpa' | hpq
    · have : p ≤ a := Nat.le_of_dvd (by omega) hpa'
      omega
    · have hpq_eq : p = q := (Nat.prime_dvd_prime_iff_eq hpprime hqprime).mp hpq
      have hab : a = b := by
        have h' : a * p = b * p := by rw [← hpq_eq] at heq; exact heq
        exact Nat.mul_right_cancel hpprime.pos h'
      exact hne (by rw [hpq_eq, hab])
  -- `|K| < D`, since `0 < a < p` and `0 < b < q`.
  have hK_abs : |(K:ℝ)| < D := by
    have hKreal : (K:ℝ) = (a:ℝ)*q - (b:ℝ)*p := by rw [hK]; push_cast; ring
    have haa : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha1
    have hba : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb1
    have ha2' : (a:ℝ) < (p:ℝ) := by exact_mod_cast ha2
    have hb2' : (b:ℝ) < (q:ℝ) := by exact_mod_cast hb2
    rw [hKreal, hD, abs_lt]
    constructor <;> nlinarith [mul_pos hppos hqpos]
  -- The difference `a/p - b/q - m = (K - m N)/D` has nonzero integer numerator.
  have hK''_ne : (K - m*N) ≠ 0 := by
    intro h0
    have hKm : (K:ℝ) = (m:ℝ)*D := by
      have := congrArg (fun z : ℤ => (z:ℝ)) h0
      push_cast at this
      rw [hNcast] at this
      linarith
    have habsK : |(K:ℝ)| = |(m:ℝ)| * D := by rw [hKm, abs_mul, abs_of_pos hDpos]
    have hmabs : |(m:ℝ)| * D < D := by rw [← habsK]; exact hK_abs
    have hmlt1 : |(m:ℝ)| < 1 := by nlinarith [hDpos]
    have hm0 : m = 0 := by
      have h := abs_lt.mp hmlt1
      have h1 : (-1:ℤ) < m := by exact_mod_cast h.1
      have h2 : m < 1 := by exact_mod_cast h.2
      omega
    rw [hm0, zero_mul, sub_zero] at h0
    exact hK_ne h0
  have hK''_ge : (1:ℝ) ≤ |((K - m*N : ℤ) : ℝ)| := by
    have h1 : (1:ℤ) ≤ |K - m*N| := Int.one_le_abs hK''_ne
    calc (1:ℝ) ≤ ((|K - m*N| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |((K - m*N : ℤ) : ℝ)| := by rw [Int.cast_abs]
  have hcd : circDist ((a:ℝ)/p - (b:ℝ)/q) = |(a:ℝ)/p - (b:ℝ)/q - (m:ℝ)| := by
    rw [circDist, ← hm]
  have ht_sub : (a:ℝ)/p - (b:ℝ)/q - (m:ℝ) = ((K - m*N : ℤ):ℝ)/D := by
    have key : ((K - m*N : ℤ):ℝ) = (K:ℝ) - (m:ℝ)*D := by
      rw [← hNcast]; push_cast; ring
    rw [ht, key]
    field_simp
  have hDle : D ≤ Q^2 := by
    rw [hD]; nlinarith [hp_le, hq_le, hppos, hqpos]
  have h1D : (1:ℝ)/D ≤ |((K - m*N : ℤ):ℝ)|/D :=
    div_le_div_of_nonneg_right hK''_ge (le_of_lt hDpos)
  have h1Q : (1:ℝ)/Q^2 ≤ 1/D := one_div_le_one_div_of_le hDpos hDle
  rw [hcd, ht_sub, abs_div, abs_of_pos hDpos]
  calc (1:ℝ)/Q^2 ≤ 1/D := h1Q
    _ ≤ |((K - m*N : ℤ):ℝ)|/D := h1D

end Work.BMF.MSD
