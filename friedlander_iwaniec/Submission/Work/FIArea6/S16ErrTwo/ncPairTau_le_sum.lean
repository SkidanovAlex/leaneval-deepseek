import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.NcDefs
import Submission.Work.FIArea1.gauss_prime_common_divisor
import Submission.Work.FIArea1.WneDefs
import Submission.Work.FIArea6.ncHelpers

set_option autoImplicit false

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary facts -/

/-- Every point of the polar support has `|z|² ≤ 2N`. -/
lemma ncPairTau_gnorm_le_two_N {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hz : z ∈ Work.FIArea1.polarSupp Pa φ) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * Pa.N :=
  Work.FIArea1.wne_gnorm_le_two_N hz

/-- A prime of norm `> Pz` dividing a point `z` of the polar support lies in `ncPi Pa`: its norm
divides `|z|² ≤ 2N`, so it lies in the Gaussian box `gBox (ncKb Pa)`
(`Work.FIArea6.ncMem_gBox`). -/
lemma ncPairTau_mem_ncPi_of_dvd {Pa : Work.FITop.Params} {φ : ℝ} {z π : GaussianInt}
    (hz : z ∈ Work.FIArea1.polarSupp Pa φ) (hπ : Prime π) (hd : π ∣ z)
    (hgt : Pa.Pz < Work.FIPlan.gnorm π) : π ∈ ncPi Pa := by
  rw [mem_ncPi]
  refine ⟨?_, hπ, hgt⟩
  have hz0 : 0 < Work.FIPlan.gnorm z := by
    have h1 : Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) :=
      (Work.FIArea1.mem_polarSupp.mp hz).2.1.2.1
    have h2 : (0 : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by linarith [Pa.hN1]
    exact_mod_cast h2
  have hle : ((Work.FIPlan.gnorm π : ℕ) : ℝ) ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hz0 (Work.FIArea1.gnorm_dvd_gnorm_of_dvd hd)
  exact Work.FIArea6.ncMem_gBox Pa hle (ncPairTau_gnorm_le_two_N hz)

/-! ## The union bound -/

/-- **The τ-mass of the non-coprime polar support is dominated by the sum over common Gaussian
primes.**  Every pair of points of `polarSupp Pa φ` that is not coprime in `ℤ[i]` shares a Gaussian
prime `π` with `|π|² > Pz` (`Work.FIArea1.gauss_prime_common_divisor`), and `π ∈ ncPi Pa`:
`|π|² ≤ |z₁|² ≤ (1+θ)N ≤ 2N` (`InPolarBox` + `θ ≤ 1`), so `π` lies in the box `gBox (ncKb Pa)`
(`Work.FIArea6.ncMem_gBox`).  The square `(ncS Pa φ π)² = (Σ_{z ∈ polarSupp, π ∣ z} τ(|z|²))²`
contains the pair's weight `τ(|z₁|²)τ(|z₂|²)` as one of its (non-negative) terms, and summing over
all `π ∈ ncPi Pa` only over-counts.  (`ncPairW z₁ z₂` is that weight.) -/
theorem ncPairTau_le_sum (Pa : Work.FITop.Params) (φ : ℝ) :
    (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ, ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ,
        Work.FIArea6.S16ErrTwo.ncPairW z1 z2)
      ≤ ∑ π ∈ Work.FIArea6.S16ErrTwo.ncPi Pa,
          (Work.FIArea6.S16ErrTwo.ncS Pa φ π) ^ 2 := by
  classical
  -- the pair weight carried by a candidate prime `π`: `τ(|z₁|²)τ(|z₂|²)` if `π ∣ z₁` and
  -- `π ∣ z₂`, and `0` otherwise
  set E : GaussianInt → GaussianInt → GaussianInt → ℝ :=
    (fun z1 z2 π => if π ∣ z1 ∧ π ∣ z2 then tauG z1 * tauG z2 else 0) with hE
  have hEeq : ∀ z1 z2 π, E z1 z2 π
      = (if π ∣ z1 ∧ π ∣ z2 then tauG z1 * tauG z2 else 0) := fun z1 z2 π => rfl
  have hEnn : ∀ z1 z2 π, 0 ≤ E z1 z2 π := by
    intro z1 z2 π
    rw [hEeq]
    by_cases h : π ∣ z1 ∧ π ∣ z2
    · rw [if_pos h]; exact mul_nonneg (tauG_nonneg z1) (tauG_nonneg z2)
    · rw [if_neg h]
  -- the pointwise union bound over the common prime
  have hpoint : ∀ z1 ∈ Work.FIArea1.polarSupp Pa φ, ∀ z2 ∈ Work.FIArea1.polarSupp Pa φ,
      ncPairW z1 z2 ≤ ∑ π ∈ ncPi Pa, E z1 z2 π := by
    intro z1 h1 z2 h2
    by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
    · have hzero : ncPairW z1 z2 = 0 := by rw [ncPairW, if_pos hcop]
      rw [hzero]
      exact Finset.sum_nonneg (fun π _ => hEnn z1 z2 π)
    · obtain ⟨π0, hprime, hd1, hd2, hgt⟩ :=
        Work.FIArea1.gauss_prime_common_divisor h1 h2 hcop
      have hmem : π0 ∈ ncPi Pa := ncPairTau_mem_ncPi_of_dvd h1 hprime hd1 hgt
      have hsingle := Finset.single_le_sum (fun π _ => hEnn z1 z2 π) hmem
      have hval : E z1 z2 π0 = tauG z1 * tauG z2 := by
        rw [hEeq, if_pos ⟨hd1, hd2⟩]
      rw [hval] at hsingle
      have hpair : ncPairW z1 z2 = tauG z1 * tauG z2 := by
        rw [ncPairW, if_neg hcop]
      rw [hpair]
      exact hsingle
  have step1 : (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
        ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ncPairW z1 z2)
      ≤ ∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
          ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ∑ π ∈ ncPi Pa, E z1 z2 π :=
    Finset.sum_le_sum (fun z1 h1 => Finset.sum_le_sum (fun z2 h2 => hpoint z1 h1 z2 h2))
  have step2 : (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
        ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ∑ π ∈ ncPi Pa, E z1 z2 π)
      = ∑ π ∈ ncPi Pa, ∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
          ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, E z1 z2 π := by
    rw [Finset.sum_congr rfl
      (fun z1 _ => (Finset.sum_comm : (∑ z2 ∈ Work.FIArea1.polarSupp Pa φ,
        ∑ π ∈ ncPi Pa, E z1 z2 π) = ∑ π ∈ ncPi Pa,
          ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, E z1 z2 π))]
    exact Finset.sum_comm
  -- the factorisation of the `π`-slice into the square of `ncS`
  have step3 : ∀ π ∈ ncPi Pa,
      (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ, ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, E z1 z2 π)
        = (ncS Pa φ π) ^ 2 := by
    intro π _
    have hfac : ∀ z1 z2 : GaussianInt, E z1 z2 π
        = (if π ∣ z1 then tauG z1 else 0) * (if π ∣ z2 then tauG z2 else 0) := by
      intro z1 z2
      rw [hEeq]
      by_cases h1 : π ∣ z1
      · by_cases h2 : π ∣ z2
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
        · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
    have hncS : ncS Pa φ π
        = ∑ z ∈ Work.FIArea1.polarSupp Pa φ, (if π ∣ z then tauG z else 0) := by
      rw [ncS]
    calc (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
          ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, E z1 z2 π)
        = (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ, (if π ∣ z1 then tauG z1 else 0))
            * (∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, (if π ∣ z2 then tauG z2 else 0)) := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl (fun z1 _ =>
            Finset.sum_congr rfl (fun z2 _ => hfac z1 z2))
      _ = (ncS Pa φ π) ^ 2 := by
          rw [hncS]; ring
  calc (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
        ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ncPairW z1 z2)
      ≤ ∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
          ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ∑ π ∈ ncPi Pa, E z1 z2 π := step1
    _ = ∑ π ∈ ncPi Pa, ∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
          ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, E z1 z2 π := step2
    _ = ∑ π ∈ ncPi Pa, (ncS Pa φ π) ^ 2 := Finset.sum_congr rfl step3

end

end Work.FIArea6.S16ErrTwo
