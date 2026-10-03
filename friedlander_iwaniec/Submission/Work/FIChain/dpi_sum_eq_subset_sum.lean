import Mathlib
import Submission.Work.FIChain.BpWinDefs

namespace Work.FIChain

open Finset
open scoped BigOperators

/-- The divisor sum `Σ_{d | Π(Pz), d > Δπ} τ(d)^k / d` over the divisors of the squarefree
primorial `Π(Pz) = ∏_{p ≤ Pz} p` equals the subset sum `Σ_{S ⊆ {p ≤ Pz}, ∏_{p∈S} p > Δπ}
∏_{p∈S} 2^k / p`, because the squarefree divisors of `Π(Pz)` are exactly the products
`∏_{p∈S} p` with `S ⊆ {p ≤ Pz}`, and for such a divisor `d = ∏_{p∈S} p` one has
`τ(d) = 2^{|S|}` and hence `τ(d)^k / d = 2^{k|S|} / ∏_{p∈S} p = ∏_{p∈S} 2^k / p`. -/
theorem dpi_sum_eq_subset_sum (k : ℕ) (κ : ℝ) (x Pz : ℕ) :
    (∑ d ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun d => Work.FIChain.Dpi x κ < d),
        ((d.divisors.card : ℝ)) ^ k / (d : ℝ))
      = ∑ S ∈ (Nat.primesLE Pz).powerset.filter (fun S => Work.FIChain.Dpi x κ < ∏ p ∈ S, p),
          ∏ p ∈ S, (2:ℝ)^k / (p:ℝ) := by
  classical
  have hPnz : ProdP Pz ≠ 0 := (ProdP_pos Pz).ne'
  have hPsq : Squarefree (ProdP Pz) := ProdP_squarefree Pz
  have hPf : (ProdP Pz).primeFactors = Nat.primesLE Pz := primeFactors_primorial Pz
  have hPprod : ProdP Pz = ∏ p ∈ Nat.primesLE Pz, p := ProdP_eq_prod Pz
  refine Finset.sum_bij' (fun a _ => a.primeFactors) (fun b _ => ∏ p ∈ b, p) ?_ ?_ ?_ ?_ ?_
  · -- `a.primeFactors` lies in the (filtered) powerset: `a | Π(Pz)`, so `a` is squarefree
    -- with `primeFactors a ⊆ primesLE Pz`, and `∏_{p | a} p = a > Δπ`.
    intro a ha
    obtain ⟨ha_div, ha_gt⟩ := Finset.mem_filter.mp ha
    have ha_dvd : a ∣ ProdP Pz := Nat.dvd_of_mem_divisors ha_div
    have ha_sq : Squarefree a := hPsq.squarefree_of_dvd ha_dvd
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · rw [← hPf]
      exact Nat.primeFactors_mono ha_dvd hPnz
    · rw [Nat.prod_primeFactors_of_squarefree ha_sq]
      exact ha_gt
  · -- If `b ⊆ primesLE Pz` then `∏_{p∈b} p` is a divisor of `Π(Pz)` that exceeds `Δπ`.
    intro b hb
    obtain ⟨hb_sub, hb_gt⟩ := Finset.mem_filter.mp hb
    have hb_sub' : b ⊆ Nat.primesLE Pz := Finset.mem_powerset.mp hb_sub
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hPnz⟩, ?_⟩
    · rw [hPprod]
      exact Finset.prod_dvd_prod_of_subset b (Nat.primesLE Pz) (fun p => p) hb_sub'
    · exact hb_gt
  · -- `∏_{p ∈ primeFactors a} p = a` for the squarefree `a | Π(Pz)`.
    intro a ha
    obtain ⟨ha_div, -⟩ := Finset.mem_filter.mp ha
    have ha_dvd : a ∣ ProdP Pz := Nat.dvd_of_mem_divisors ha_div
    have ha_sq : Squarefree a := hPsq.squarefree_of_dvd ha_dvd
    exact Nat.prod_primeFactors_of_squarefree ha_sq
  · -- `primeFactors (∏_{p∈b} p) = b` for `b` a set of primes.
    intro b hb
    obtain ⟨hb_sub, -⟩ := Finset.mem_filter.mp hb
    have hb_sub' : b ⊆ Nat.primesLE Pz := Finset.mem_powerset.mp hb_sub
    exact Nat.primeFactors_prod (fun p hp => (Nat.mem_primesLE.mp (hb_sub' hp)).2)
  · -- Terms match: `τ(a)^k / a = ∏_{p | a} 2^k / p` for squarefree `a | Π(Pz)`.
    intro a ha
    obtain ⟨ha_div, -⟩ := Finset.mem_filter.mp ha
    have ha_dvd : a ∣ ProdP Pz := Nat.dvd_of_mem_divisors ha_div
    have ha_sq : Squarefree a := hPsq.squarefree_of_dvd ha_dvd
    have ha_nz : a ≠ 0 := (Nat.pos_of_dvd_of_pos ha_dvd (ProdP_pos Pz)).ne'
    have hcard : a.divisors.card = 2 ^ a.primeFactors.card := by
      rw [Nat.card_divisors ha_nz]
      have h2 : (∏ p ∈ a.primeFactors, (a.factorization p + 1))
          = ∏ p ∈ a.primeFactors, 2 := by
        refine Finset.prod_congr rfl (fun p hp => ?_)
        simp [Nat.factorization_eq_one_of_squarefree ha_sq (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)]
      rw [h2, Finset.prod_const]
    have hL : ((a.divisors.card : ℝ)) ^ k = (2:ℝ) ^ (k * a.primeFactors.card) := by
      rw [hcard]
      push_cast
      rw [← pow_mul, Nat.mul_comm a.primeFactors.card k]
    have hR : (∏ p ∈ a.primeFactors, (2:ℝ)^k / (p:ℝ))
        = (2:ℝ) ^ (k * a.primeFactors.card) / (a:ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const]
      rw [← pow_mul]
      rw [← Nat.cast_prod (fun p => p) a.primeFactors, Nat.prod_primeFactors_of_squarefree ha_sq]
    rw [hL, hR]

end Work.FIChain
