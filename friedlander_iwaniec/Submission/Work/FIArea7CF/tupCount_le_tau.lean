/-
# `Submission.Work.FIArea7CF.tupCount_le_tau` — clash-free copy of `Submission.Work.FIArea7.Pub213.tupCount_le_tau`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.Conv6Defs
import Submission.Work.FIArea7CF.r2count_upper
import Submission.Work.FIArea7CF.R2countDefs
import Submission.Work.FIArea7CF.nzTup_filter_prod_subset_piFinset

set_option autoImplicit false

namespace Work.FIArea7.Pub213

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `#Sz m = r2count m ≤ 4·τ(m)`: the number of Gaussian integers of norm `m ≠ 0` is at most
`4` times the number of divisors of `m` (`r2count_upper` for the product over the primes
`≡ 1 (mod 4)`, `Nat.card_divisors` for the divisor count). -/
lemma sz_card_le_four_mul_divisors_card (m : ℕ) (hm : m ≠ 0) :
    (Work.FIArea7.Sz m).card ≤ 4 * m.divisors.card := by
  rw [← Work.FIArea7.r2count_eq_Sz_card m]
  refine (Work.FIArea7.r2count_upper m (Nat.pos_of_ne_zero hm)).trans ?_
  rw [Nat.card_divisors hm]
  refine Nat.mul_le_mul_left 4 ?_
  refine Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
    (fun p _ => Nat.zero_le _) (fun p _ _ => by omega)

/-- **The number of nonzero Gaussian divisors of `u` is at most `4·τ(|u|²)²`**, in the explicit
form of the union of the norm layers `Sz m` over the divisors `m` of `|u|²`. -/
lemma card_biUnion_Sz_divisors_le (u : GaussianInt) (hu : u ≠ 0) :
    ((Work.FIPlan.gnorm u).divisors.biUnion (fun m => Work.FIArea7.Sz m)).card
      ≤ 4 * (Work.FIPlan.gnorm u).divisors.card ^ 2 := by
  set N : ℕ := Work.FIPlan.gnorm u with hNdef
  have hNne : N ≠ 0 := by
    rw [hNdef]
    exact fun h => hu (Work.FIArea7.gnorm_eq_zero_iff.mp h)
  calc (N.divisors.biUnion (fun m => Work.FIArea7.Sz m)).card
      ≤ ∑ m ∈ N.divisors, (Work.FIArea7.Sz m).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ N.divisors, 4 * N.divisors.card := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        have hmdvd : m ∣ N := (Nat.mem_divisors.mp hm).1
        have hm0 : m ≠ 0 := (Nat.pos_of_mem_divisors hm).ne'
        calc (Work.FIArea7.Sz m).card ≤ 4 * m.divisors.card :=
              sz_card_le_four_mul_divisors_card m hm0
          _ ≤ 4 * N.divisors.card :=
              Nat.mul_le_mul_left 4 (Finset.card_le_card (Nat.divisors_subset_of_dvd hNne hmdvd))
    _ = 4 * N.divisors.card ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

/-- **The six-tuple count is bounded by a power of the divisor function**: for `u ≠ 0` the
number of tuples of `nzTup R N` with product `u` is at most `4⁶·τ(|u|²)¹²`.

The tuple is determined by its six entries, each of which is a nonzero Gaussian divisor of `u`;
the number of those is at most `4·τ(|u|²)²` (`card_biUnion_Sz_divisors_le`). -/
theorem tupCount_le_tau (R : ℤ) (N : ℝ) (u : GaussianInt) (hN : 1 ≤ N) (hu : u ≠ 0) :
    (tupCount R N u : ℝ)
      ≤ (4 : ℝ) ^ 6 * (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12 := by
  set τ : ℕ := (Work.FIPlan.gnorm u).divisors.card with hτdef
  set D : Finset GaussianInt := (Work.FIPlan.gnorm u).divisors.biUnion (fun m => Work.FIArea7.Sz m) with hDdef
  -- the filtered tuples sit inside the product of the six divisor layers
  have hsub : (nzTup R N).filter (fun t => Work.FIArea7.tupProd t = u)
      ⊆ Fintype.piFinset (fun _ : Fin 6 => D) := by
    rw [hDdef]
    exact nzTup_filter_prod_subset_piFinset R N u hu
  have hcard : tupCount R N u ≤ D.card ^ 6 := by
    rw [tupCount]
    calc ((nzTup R N).filter (fun t => Work.FIArea7.tupProd t = u)).card
        ≤ (Fintype.piFinset (fun _ : Fin 6 => D)).card := Finset.card_le_card hsub
      _ = D.card ^ 6 := by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hDcard : D.card ≤ 4 * τ ^ 2 := by
    rw [hDdef, hτdef]
    exact card_biUnion_Sz_divisors_le u hu
  have hnat : tupCount R N u ≤ 4 ^ 6 * τ ^ 12 := by
    calc tupCount R N u ≤ D.card ^ 6 := hcard
      _ ≤ (4 * τ ^ 2) ^ 6 := Nat.pow_le_pow_left hDcard 6
      _ = 4 ^ 6 * τ ^ 12 := by ring
  have hcast : (tupCount R N u : ℝ) ≤ (4 : ℝ) ^ 6 * (τ : ℝ) ^ 12 := by
    have h : ((tupCount R N u : ℕ) : ℝ) ≤ ((4 ^ 6 * τ ^ 12 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have h' : ((4 ^ 6 * τ ^ 12 : ℕ) : ℝ) = (4 : ℝ) ^ 6 * (τ : ℝ) ^ 12 := by
      push_cast
      ring
    rwa [h'] at h
  calc (tupCount R N u : ℝ)
      ≤ (4 : ℝ) ^ 6 * (τ : ℝ) ^ 12 := hcast
    _ = (4 : ℝ) ^ 6 * (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12 := by rw [hτdef]

end

end Work.FIArea7.Pub213
