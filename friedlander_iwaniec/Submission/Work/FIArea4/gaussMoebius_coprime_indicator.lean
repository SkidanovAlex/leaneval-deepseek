/-
# The Möbius-type indicator of coprimality in `ℤ[i]`

Friedlander–Iwaniec, *The polynomial X² + Y⁴ captures its primes*, Ann. of Math. **148** (1998),
use the Möbius function of `ℤ[i]` to write the coprimality condition `(z₁,z₂) = 1` as a sum over
the **primary** common divisors of `z₁` and `z₂`:

  `∑_{w primary, w | z₁, w | z₂} μ(w) = [ (z₁,z₂) = 1 ]`.

Here `μ` is the Möbius function of the unique factorization monoid `ℤ[i]`
(`UniqueFactorizationMonoid.moebius`, so `‖μ‖ ≤ 1` and `μ 1 = 1`) and "primary" is the paper's
condition (5.3)–(5.5), i.e. `z ≡ 1 mod 2(1+i)` (`Work.FIPlan.IsPrimary`).  The content of the
identity is that the primary divisors are exactly one representative per associate class of
divisors, and Möbius inversion over the resulting product-of-chains divisor lattice.

The arithmetic is developed in `Work.FIArea4.GaussMoebiusCore`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.GaussMoebiusCore

set_option autoImplicit false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

open Zsqrtd

/-- An odd natural number is nonzero. -/
theorem odd_nat_ne_zero {n : ℕ} (h : Odd n) : n ≠ 0 := by
  rintro rfl
  obtain ⟨k, hk⟩ := h
  omega

/-- A Gaussian integer of odd norm is nonzero. -/
theorem odd_gnorm_ne_zero {z : GaussianInt} (h : Odd (Work.FIPlan.gnorm z)) : z ≠ 0 := by
  intro hz
  rw [hz, gnorm_zero] at h
  exact (odd_nat_ne_zero h) rfl

theorem gaussMoebius_coprime_indicator :
    ∃ μ : GaussianInt → ℂ, (∀ z : GaussianInt, ‖μ z‖ ≤ 1) ∧ (μ 1 = 1) ∧
      ∀ z1 z2 : GaussianInt, Odd (Work.FIPlan.gnorm z1) → Odd (Work.FIPlan.gnorm z2) →
        ∃ s : Finset GaussianInt,
          (∀ w ∈ s, w ∣ z1 ∧ w ∣ z2 ∧ Work.FIPlan.IsPrimary w) ∧
          (∀ w : GaussianInt, w ∣ z1 → w ∣ z2 → Work.FIPlan.IsPrimary w → w ∈ s) ∧
          ((Work.FIPlan.GaussCoprime z1 z2 → (∑ w ∈ s, μ w) = 1) ∧
           (¬ Work.FIPlan.GaussCoprime z1 z2 → (∑ w ∈ s, μ w) = 0)) := by
  classical
  refine ⟨fun z => (UniqueFactorizationMonoid.moebius z : ℂ), ?_, ?_, ?_⟩
  · -- `‖μ z‖ ≤ 1`
    intro z
    rw [Complex.norm_intCast]
    have h : UniqueFactorizationMonoid.moebius z = 0 ∨
        UniqueFactorizationMonoid.moebius z = 1 ∨ UniqueFactorizationMonoid.moebius z = -1 := by
      by_cases hs : Squarefree z
      · rw [Squarefree.moebius_eq hs]
        rcases Nat.even_or_odd (UniqueFactorizationMonoid.factors z).card with he | ho
        · exact Or.inr (Or.inl (Even.neg_one_pow he))
        · exact Or.inr (Or.inr (Odd.neg_one_pow ho))
      · exact Or.inl (UniqueFactorizationMonoid.moebius_of_not_squarefree hs)
    rcases h with h | h | h <;> rw [h] <;> norm_num
  · -- `μ 1 = 1`
    show (UniqueFactorizationMonoid.moebius 1 : ℂ) = 1
    rw [UniqueFactorizationMonoid.moebius_one]; norm_num
  · -- the coprimality indicator
    intro z1 z2 h1 h2
    show ∃ s : Finset GaussianInt,
        (∀ w ∈ s, w ∣ z1 ∧ w ∣ z2 ∧ Work.FIPlan.IsPrimary w) ∧
        (∀ w : GaussianInt, w ∣ z1 → w ∣ z2 → Work.FIPlan.IsPrimary w → w ∈ s) ∧
        ((Work.FIPlan.GaussCoprime z1 z2 →
            (∑ w ∈ s, (UniqueFactorizationMonoid.moebius w : ℂ)) = 1) ∧
         (¬ Work.FIPlan.GaussCoprime z1 z2 →
            (∑ w ∈ s, (UniqueFactorizationMonoid.moebius w : ℂ)) = 0))
    have hz1 : z1 ≠ 0 := odd_gnorm_ne_zero h1
    set g : GaussianInt := EuclideanDomain.gcd z1 z2 with hg
    have hgnz : g ≠ 0 := by
      intro h
      have hz1' : z1 = 0 := by
        have hd := EuclideanDomain.gcd_dvd_left z1 z2
        rw [← hg, h] at hd
        exact zero_dvd_iff.mp hd
      exact hz1 hz1'
    have hgodd : Odd (Work.FIPlan.gnorm g) := by
      rw [hg]
      exact odd_gnorm_of_dvd_odd (EuclideanDomain.gcd_dvd_left z1 z2) h1
    have hB : (Work.FIPlan.gnorm g : ℤ) ≤ ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) := by
      have hdvd : Work.FIPlan.gnorm g ∣ Work.FIPlan.gnorm z1 := by
        apply gnorm_dvd
        rw [hg]
        exact EuclideanDomain.gcd_dvd_left z1 z2
      exact_mod_cast Nat.le_of_dvd (gnorm_pos hz1) hdvd
    refine ⟨(Work.FIPlan.gBox ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)).filter
        (fun w => w ∣ z1 ∧ w ∣ z2 ∧ Work.FIPlan.IsPrimary w), ?_, ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_filter] at hw
      exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2⟩
    · intro w hw1 hw2 hwprim
      simp only [Finset.mem_filter]
      exact ⟨primaryDivisor_mem_gBox hz1 hw1 hwprim, hw1, hw2, hwprim⟩
    · have hfilter : (Work.FIPlan.gBox ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)).filter
            (fun w => w ∣ z1 ∧ w ∣ z2 ∧ Work.FIPlan.IsPrimary w)
          = (Work.FIPlan.gBox ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)).filter
            (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w) := by
        refine Finset.filter_congr (fun w _ => ?_)
        rw [hg]
        constructor
        · rintro ⟨ha, hb, hp⟩
          exact ⟨EuclideanDomain.dvd_gcd ha hb, hp⟩
        · rintro ⟨hgd, hp⟩
          exact ⟨hgd.trans (EuclideanDomain.gcd_dvd_left z1 z2),
            hgd.trans (EuclideanDomain.gcd_dvd_right z1 z2), hp⟩
      have hsum : (∑ w ∈ (Work.FIPlan.gBox ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)).filter
            (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w),
          (UniqueFactorizationMonoid.moebius w : ℂ)) = if IsUnit g then 1 else 0 :=
        sum_primaryDivs_eq_of_le g hgnz hgodd hB
      constructor
      · intro hcop
        rw [hfilter, hsum]
        have : IsUnit g := by
          rw [hg]
          exact (EuclideanDomain.gcd_isUnit_iff (x := z1) (y := z2)).mpr hcop
        rw [if_pos this]
      · intro hnc
        rw [hfilter, hsum]
        have : ¬ IsUnit g := by
          rw [hg]
          exact fun h => hnc ((EuclideanDomain.gcd_isUnit_iff (x := z1) (y := z2)).mp h)
        rw [if_neg this]

end

end Work.FIArea4
