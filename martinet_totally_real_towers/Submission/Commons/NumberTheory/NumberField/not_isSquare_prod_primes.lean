import Mathlib
import Submission.Commons.NumberTheory.Nat.isSquare_of_rat_sq
import Submission.Commons.Data.Nat.squarefree_prod_primes

namespace Commons.NumberTheory.NumberField

open scoped BigOperators

theorem not_isSquare_prod_primes {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ s, Nat.Prime (p i))
    (hinj : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j)
    (hne : s.Nonempty) :
    ∀ r : ℚ, r ^ 2 ≠ ((∏ i ∈ s, p i : ℕ) : ℚ) := by
  classical
  intro r hr
  set n : ℕ := ∏ i ∈ s, p i with hn
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => (hp i hi).ne_zero)
  -- a product of distinct primes is squarefree
  have hsq : Squarefree n := by
    rw [hn]
    have hinj' : Set.InjOn p ↑s := fun i hi j hj hij => hinj i hi j hj hij
    have hprod : (∏ q ∈ s.image p, q) = ∏ i ∈ s, p i :=
      Finset.prod_image (f := id) (g := p) hinj'
    rw [← hprod]
    refine Commons.Data.Nat.squarefree_prod_primes ?_
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact hp i hi
  -- a nonzero natural that is a rational square is a natural square
  have hisq : IsSquare n :=
    Commons.NumberTheory.Nat.isSquare_of_rat_sq hn0 ⟨r, hr⟩
  obtain ⟨m, hm⟩ := hisq
  -- a squarefree number that is a square must be 1
  have hdvd : m * m ∣ n * 1 := by
    rw [hm]
    exact ⟨1, rfl⟩
  have hm1 : m ∣ 1 := Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hsq hdvd
  rw [Nat.dvd_one] at hm1
  have hn1 : n = 1 := by rw [hm, hm1, one_mul]
  -- but a prime divides n
  obtain ⟨i₀, hi₀⟩ := hne
  have hq := hp i₀ hi₀
  have hqdvd : p i₀ ∣ n := by
    rw [hn]
    exact Finset.dvd_prod_of_mem p hi₀
  rw [hn1] at hqdvd
  exact hq.not_dvd_one hqdvd

end Commons.NumberTheory.NumberField
