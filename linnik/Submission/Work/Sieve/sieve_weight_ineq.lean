import Mathlib
import Submission.Work.Sieve.y_prod_primes
import Submission.Work.Sieve.mul_prod_primeFactors_inj
import Submission.Work.Sieve.mul_prod_primeFactors_le

open scoped BigOperators

namespace Work.Sieve

/-- Sieve weight inequality: for a (coprime-)multiplicative nonnegative weight `y` on
squarefree integers, summing the squarefree weights up to `R/d` over integers coprime
to a squarefree modulus `d`, then multiplying by `∏_{p | d} (1 + y p)`, is dominated
by the full squarefree-weighted sum up to `R`.

The product is expanded as `∑_{t ⊆ primeFactors d} ∏_{p ∈ t} y p`; the resulting
double sum is reindexed by the injective map `(r, t) ↦ r * ∏_{p ∈ t} p`, whose image
lies in `{1, …, R}` (a product of distinct primes dividing `d` is at most `d`). -/
theorem sieve_weight_ineq (y : ℕ → ℝ)
    (hy_mul : ∀ m n : ℕ, Squarefree m → Squarefree n → Nat.Coprime m n →
      y (m * n) = y m * y n)
    (hy_nonneg : ∀ n : ℕ, Squarefree n → 0 ≤ y n)
    (R d : ℕ) (hd : d ≠ 0) (hds : Squarefree d) :
    (∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d),
        (if Squarefree r then (1 : ℝ) else 0) * y r)
      * (∏ p ∈ d.primeFactors, (1 + y p))
      ≤ ∑ n ∈ Finset.Icc 1 R, (if Squarefree n then (1 : ℝ) else 0) * y n := by
  classical
  set Sq : Finset ℕ := (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d) with hSq
  set T : Finset (Finset ℕ) := d.primeFactors.powerset with hT
  -- Expand the Euler-type product over the powerset of the prime factors.
  have hprod : (∏ p ∈ d.primeFactors, (1 + y p)) = ∑ t ∈ T, ∏ p ∈ t, y p := by
    rw [hT]; exact Finset.prod_one_add d.primeFactors
  -- Pointwise identity: the weight of `r` times the weight of the subset `t`
  -- equals the weight of the product `r * ∏_{p ∈ t} p`.
  have hpt : ∀ x ∈ Sq ×ˢ T,
      ((if Squarefree x.1 then (1 : ℝ) else 0) * y x.1) * (∏ p ∈ x.2, y p)
        = (if Squarefree (x.1 * ∏ p ∈ x.2, p) then (1 : ℝ) else 0) * y (x.1 * ∏ p ∈ x.2, p) := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨hxS, hxT⟩ := hx
    rw [Finset.mem_filter] at hxS
    obtain ⟨_, hxcop⟩ := hxS
    rw [Finset.mem_powerset] at hxT
    have hpr : ∀ p ∈ x.2, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hxT hp)
    by_cases hsft : Squarefree x.1
    · rw [if_pos hsft]
      by_cases hne : x.2.Nonempty
      · -- all primes in the subset are coprime to `r`, and the prime product is squarefree
        obtain ⟨hsfP, hyP⟩ := y_prod_primes y hy_mul x.2 hpr hne
        have hPt_dvd : (∏ p ∈ x.2, p) ∣ d := by
          rw [← Nat.prod_primeFactors_of_squarefree hds]
          exact Finset.prod_dvd_prod_of_subset x.2 d.primeFactors (fun p => p) hxT
        have hcop : Nat.Coprime x.1 (∏ p ∈ x.2, p) := hxcop.coprime_dvd_right hPt_dvd
        have hsfmul : Squarefree (x.1 * ∏ p ∈ x.2, p) :=
          (Nat.squarefree_mul hcop).mpr ⟨hsft, hsfP⟩
        rw [if_pos hsfmul]
        have hy : y (x.1 * ∏ p ∈ x.2, p) = y x.1 * (∏ p ∈ x.2, y p) := by
          rw [hy_mul x.1 (∏ p ∈ x.2, p) hsft hsfP hcop, hyP]
        rw [hy]; ring
      · -- empty subset: both sides reduce to the weight of `r`
        have hempty : x.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        rw [hempty]
        simp [hsft]
    · -- `r` is not squarefree, so neither is `r * ∏_{p ∈ t} p`
      rw [if_neg hsft]
      have hnsf : ¬ Squarefree (x.1 * ∏ p ∈ x.2, p) :=
        fun h => hsft ((Nat.squarefree_mul_iff.mp h).2.1)
      rw [if_neg hnsf]
      ring
  -- The map `(r, t) ↦ r * ∏_{p ∈ t} p` is injective on the index set.
  have hinj : Set.InjOn (fun x : ℕ × Finset ℕ => x.1 * ∏ p ∈ x.2, p) ↑(Sq ×ˢ T) := by
    intro x hx x' hx' hxx'
    rw [Finset.mem_coe, Finset.mem_product] at hx hx'
    obtain ⟨hxS, hxT⟩ := hx
    obtain ⟨hxS', hxT'⟩ := hx'
    rw [Finset.mem_filter] at hxS hxS'
    obtain ⟨_, hxcop⟩ := hxS
    obtain ⟨_, hxcop'⟩ := hxS'
    rw [Finset.mem_powerset] at hxT hxT'
    obtain ⟨hteq, hreq⟩ := mul_prod_primeFactors_inj hds hxT hxT' hxcop hxcop' hxx'
    exact Prod.ext hreq hteq
  -- The image is contained in `{1, …, R}`.
  have hsubset : ((Sq ×ˢ T).image (fun x : ℕ × Finset ℕ => x.1 * ∏ p ∈ x.2, p)) ⊆ Finset.Icc 1 R := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    rw [Finset.mem_product] at hx
    obtain ⟨hxS, hxT⟩ := hx
    rw [Finset.mem_filter] at hxS
    obtain ⟨hxI, _⟩ := hxS
    rw [Finset.mem_powerset] at hxT
    rw [Finset.mem_Icc] at hxI ⊢
    refine ⟨?_, ?_⟩
    · have h1 : (1 : ℕ) ≤ ∏ p ∈ x.2, p :=
        Finset.one_le_prod₀ (fun p hp => (Nat.prime_of_mem_primeFactors (hxT hp)).one_le)
      exact le_trans (le_of_eq (one_mul 1).symm) (Nat.mul_le_mul hxI.1 h1)
    · exact mul_prod_primeFactors_le hd hds hxI.2 hxT
  -- Assemble.
  have key : (∑ r ∈ Sq, (if Squarefree r then (1 : ℝ) else 0) * y r) * (∏ p ∈ d.primeFactors, (1 + y p))
      ≤ ∑ n ∈ Finset.Icc 1 R, (if Squarefree n then (1 : ℝ) else 0) * y n := by
    calc
      (∑ r ∈ Sq, (if Squarefree r then (1 : ℝ) else 0) * y r) * (∏ p ∈ d.primeFactors, (1 + y p))
          = ∑ r ∈ Sq, ∑ t ∈ T, ((if Squarefree r then (1 : ℝ) else 0) * y r) * (∏ p ∈ t, y p) := by
            rw [hprod, Finset.sum_mul_sum]
      _ = ∑ x ∈ Sq ×ˢ T, ((if Squarefree x.1 then (1 : ℝ) else 0) * y x.1) * (∏ p ∈ x.2, y p) := by
            rw [Finset.sum_product]
      _ = ∑ x ∈ Sq ×ˢ T, (if Squarefree (x.1 * ∏ p ∈ x.2, p) then (1 : ℝ) else 0) * y (x.1 * ∏ p ∈ x.2, p) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hpt x hx
      _ = ∑ n ∈ (Sq ×ˢ T).image (fun x : ℕ × Finset ℕ => x.1 * ∏ p ∈ x.2, p), (if Squarefree n then (1 : ℝ) else 0) * y n := by
            rw [Finset.sum_image (f := fun n => (if Squarefree n then (1 : ℝ) else 0) * y n)
              (g := fun x : ℕ × Finset ℕ => x.1 * ∏ p ∈ x.2, p) (s := Sq ×ˢ T) hinj]
      _ ≤ ∑ n ∈ Finset.Icc 1 R, (if Squarefree n then (1 : ℝ) else 0) * y n := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
            intro n _ _
            by_cases h : Squarefree n
            · rw [if_pos h, one_mul]; exact hy_nonneg n h
            · rw [if_neg h, zero_mul]
  exact key

end Work.Sieve
