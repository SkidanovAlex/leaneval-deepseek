/-
# `Submission.Work.FIArea6.S16ErrTwo.NcDefs` — vocabulary for the non-coprime mass of §16

Definitions (and their elementary API) for the coprimality removal of *FI* (16.4), used by
`Work.FIArea6.S16ErrTwo.ncMass_le`:

* `tauG z = τ(|z|²)`, the divisor weight of a Gaussian integer;
* `ncPi Pa`, the candidate set of common Gaussian primes of a non-coprime pair of support points
  (the primes in the box `gBox (ncKb Pa)` with norm `> Pz`);
* `ncRad Pa π`, the radius of the box containing the quotients `z/π` of the support points `z`
  divisible by `π`;
* `ncS Pa φ π`, the `τ`-mass of the polar support carried by the multiples of `π`.

This module is deliberately free of `sorry`.
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea1.conjunct2_defs
import Submission.Work.FIArea6.ncHelpers
import Submission.Work.FIArea1.card_primes_dvd_le

set_option autoImplicit false

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Definitions -/

/-- The `τ`-weight `τ(|z|²)` of a Gaussian integer, as a real number. -/
def tauG (z : GaussianInt) : ℝ := (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)

/-- The candidate set of common Gaussian primes of a non-coprime pair of support points: the
primes in the box `gBox (ncKb Pa)` (which contains every divisor of a point of the polar support)
whose norm exceeds the small-prime cutoff `Pz` (5.8). -/
def ncPi (Pa : Work.FITop.Params) : Finset GaussianInt :=
  (Work.FIPlan.gBox (Work.FIArea6.ncKb Pa)).filter
    (fun π => Prime π ∧ Pa.Pz < Work.FIPlan.gnorm π)

/-- The radius of the box containing the quotients `z/π`, `z` a support point divisible by `π`:
`|z/π|² ≤ 2N/|π|² ≤ 8N/|π|²` because `|z|² ≤ (1+θ)N ≤ 2N`. -/
def ncRad (Pa : Work.FITop.Params) (π : GaussianInt) : ℤ :=
  (⌈Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ))⌉₊ : ℤ)

/-- The pair weight of the non-coprime union bound: `τ(z₁)τ(z₂)` for a non-coprime pair of
Gaussian integers and `0` for a coprime pair. -/
def ncPairW (z1 z2 : GaussianInt) : ℝ :=
  if Work.FIPlan.GaussCoprime z1 z2 then 0 else tauG z1 * tauG z2

/-- The `τ`-mass of the polar support carried by the multiples of `π`. -/
def ncS (Pa : Work.FITop.Params) (φ : ℝ) (π : GaussianInt) : ℝ :=
  ∑ z ∈ Work.FIArea1.polarSupp Pa φ, (if π ∣ z then tauG z else 0)

/-! ## Elementary API -/

lemma tauG_nonneg (z : GaussianInt) : 0 ≤ tauG z := by
  unfold tauG; positivity

lemma mem_ncPi {Pa : Work.FITop.Params} {π : GaussianInt} :
    π ∈ ncPi Pa ↔ π ∈ Work.FIPlan.gBox (Work.FIArea6.ncKb Pa) ∧ Prime π
      ∧ Pa.Pz < Work.FIPlan.gnorm π := by
  rw [ncPi, Finset.mem_filter]

lemma prime_of_mem_ncPi {Pa : Work.FITop.Params} {π : GaussianInt} (h : π ∈ ncPi Pa) :
    Prime π := ((mem_ncPi.mp h).2.1)

lemma gnorm_gt_Pz_of_mem_ncPi {Pa : Work.FITop.Params} {π : GaussianInt} (h : π ∈ ncPi Pa) :
    Pa.Pz < Work.FIPlan.gnorm π := ((mem_ncPi.mp h).2.2)

lemma ncS_nonneg (Pa : Work.FITop.Params) (φ : ℝ) (π : GaussianInt) : 0 ≤ ncS Pa φ π := by
  unfold ncS
  refine Finset.sum_nonneg (fun z _ => ?_)
  by_cases h : π ∣ z
  · rw [if_pos h]; exact tauG_nonneg z
  · rw [if_neg h]

lemma ncPairW_nonneg (z1 z2 : GaussianInt) : 0 ≤ ncPairW z1 z2 := by
  unfold ncPairW
  by_cases h : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos h]
  · rw [if_neg h]; exact mul_nonneg (tauG_nonneg z1) (tauG_nonneg z2)

/-- **A Gaussian prime has prime-power norm.**  Every Gaussian prime divides a rational prime `p`
(`Work.FIArea1.exists_natPrime_dvd_gauss_prime`), so its norm divides `p²`, hence is `p` or `p²`;
in particular `τ(|π|²) ≤ 3`. -/
lemma tauG_le_three_of_prime {π : GaussianInt} (hπ : Prime π) : tauG π ≤ 3 := by
  obtain ⟨p, hp, hdvd⟩ := Work.FIArea1.exists_natPrime_dvd_gauss_prime π hπ
  have hgn : Work.FIPlan.gnorm π ∣ p ^ 2 := by
    have h := Work.FIArea1.gnorm_dvd_gnorm_of_dvd hdvd
    rwa [Work.FIArea1.gnorm_natCast] at h
  have hne1 : Work.FIPlan.gnorm π ≠ 1 := by
    intro h1
    exact hπ.not_isUnit (Zsqrtd.norm_eq_one_iff.mp h1)
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hgn
  have hk0 : k ≠ 0 := by
    intro h0
    exact hne1 (by rw [hk, h0]; simp)
  have hk12 : k = 1 ∨ k = 2 := by omega
  have hcard : (Work.FIPlan.gnorm π).divisors.card ≤ 3 := by
    rcases hk12 with h1 | h2
    · have h1' : Work.FIPlan.gnorm π = p := by rw [hk, h1, pow_one]
      rw [h1', Nat.Prime.divisors hp, Finset.card_pair hp.ne_one.symm]; norm_num
    · have h2' : Work.FIPlan.gnorm π = p ^ 2 := by rw [hk, h2]
      rw [h2', Nat.divisors_prime_pow hp 2]; simp
  unfold tauG
  exact_mod_cast hcard

end

end Work.FIArea6.S16ErrTwo
