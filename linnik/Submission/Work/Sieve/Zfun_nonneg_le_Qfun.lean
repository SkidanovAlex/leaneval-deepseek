import Mathlib
import Submission.Work.Sieve.gFun_theory
import Submission.Work.Sieve.G_at_one_defs
import Submission.Work.LinnikAreas.Sieve.Defs

namespace Work.Sieve

/-- A product of (distinct) primes is squarefree. -/
private lemma squarefree_prod_primes : ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
    Squarefree (∏ p ∈ s, p) := by
  classical
  intro s
  induction s using Finset.cons_induction with
  | empty => intro _; simp
  | cons a s ha ih =>
    intro hs
    rw [Finset.prod_cons]
    have ha' : Nat.Prime a := hs a (Finset.mem_cons_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_cons_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      rw [Nat.Prime.coprime_iff_not_dvd ha']
      intro hdvd
      obtain ⟨i, hi, hai⟩ := (Nat.prime_iff.mp ha').exists_mem_finset_dvd hdvd
      have haeq : a = i := (Nat.prime_dvd_prime_iff_eq ha' (hs' i hi)).mp hai
      exact ha (haeq.symm ▸ hi)
    exact (Nat.squarefree_mul hcop).mpr ⟨(Nat.prime_iff.mp ha').squarefree, ih hs'⟩

/-- **Bound on the local factor `Z_k`.** For every level `R` and every `k`,
`0 ≤ Z_k = Σ_{m ∣ rad(q), k·m ≤ R} 1/g(m) ≤ Q(χ₁) = ∏_{p ∣ q}(1 + 1/g(p))`:
the terms are non-negative (positivity of `g` on squarefree arguments) and the sum over the
squarefree divisors of `rad q`, cut off at `k·m ≤ R`, is at most the full product
`∏_{p ∣ q}(1 + 1/g(p))`.

Available: `Work.Sieve.gFun_theory` (for `n` squarefree: `g(n) = ∏_{p ∣ n} g(p)`, `g(p) > 0`,
hence `g(n) > 0`).  Hence `Σ_{m ∣ rad q} 1/g(m) = ∏_{p ∣ q}(1 + 1/g(p))` by multiplicativity, and
the filtered sum is a sub-sum of it. -/
theorem Zfun_nonneg_le_Qfun {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    (hreal : χ₁ ^ 2 = 1) (R k : ℕ) :
    0 ≤ Work.Sieve.Zfun χ₁ R k ∧ Work.Sieve.Zfun χ₁ R k ≤ Work.Sieve.Qfun χ₁ := by
  classical
  unfold Work.Sieve.Zfun Work.Sieve.Qfun
  set r := ∏ p ∈ q.primeFactors, p with hr
  set S := (Finset.Icc 1 R).filter (fun m => k * m ≤ R ∧ m ∣ r)
  have hrp : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hsq_r : Squarefree r := by rw [hr]; exact squarefree_prod_primes _ hrp
  have hr0 : r ≠ 0 := hsq_r.ne_zero
  have hrfac : r.primeFactors = q.primeFactors := by
    rw [hr]; exact Nat.primeFactors_prod_primeFactors q
  have hg := Work.Sieve.gFun_theory χ₁ hreal
  have hsqm : ∀ m ∈ S, Squarefree m := by
    intro m hm
    exact hsq_r.squarefree_of_dvd (Finset.mem_filter.mp hm).2.2
  have hgf : ∀ m ∈ S, 1 / Work.LinnikAreas.Sieve.gFun χ₁ m =
      ∏ p ∈ m.primeFactors, (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ := by
    intro m hm
    rw [hg.2.2.2.1 m (hsqm m hm), one_div, Finset.prod_inv_distrib]
  have hS_nonneg : 0 ≤ ∑ m ∈ S, 1 / Work.LinnikAreas.Sieve.gFun χ₁ m := by
    apply Finset.sum_nonneg
    intro m hm
    have hpos : 0 < Work.LinnikAreas.Sieve.gFun χ₁ m := hg.2.2.2.2.1 m (hsqm m hm)
    exact div_nonneg zero_le_one (le_of_lt hpos)
  have hub : ∑ m ∈ S, 1 / Work.LinnikAreas.Sieve.gFun χ₁ m ≤
      ∏ p ∈ q.primeFactors, (1 + (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹) := by
    rw [Finset.prod_one_add]
    have hsub : S.image (fun m => m.primeFactors) ⊆ q.primeFactors.powerset := by
      intro t ht
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
      rw [Finset.mem_powerset]
      have hmdvd : m ∣ r := (Finset.mem_filter.mp hm).2.2
      have h1 : m.primeFactors ⊆ r.primeFactors := Nat.primeFactors_mono hmdvd hr0
      rwa [hrfac] at h1
    have hinj : Set.InjOn (fun m : ℕ => m.primeFactors) (↑S : Set ℕ) := by
      intro m1 hm1 m2 hm2 heq
      have heq' : m1.primeFactors = m2.primeFactors := heq
      calc m1 = ∏ p ∈ m1.primeFactors, p :=
            (Nat.prod_primeFactors_of_squarefree (hsqm m1 hm1)).symm
        _ = ∏ p ∈ m2.primeFactors, p := by rw [heq']
        _ = m2 := Nat.prod_primeFactors_of_squarefree (hsqm m2 hm2)
    have hnonneg : ∀ t ∈ q.primeFactors.powerset, t ∉ S.image (fun m => m.primeFactors) →
        0 ≤ ∏ p ∈ t, (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ := by
      intro t ht _
      apply Finset.prod_nonneg
      intro p hpt
      have hp : p.Prime := hrp p ((Finset.mem_powerset.mp ht) hpt)
      exact inv_nonneg.mpr (le_of_lt (hg.2.1 p hp))
    calc ∑ m ∈ S, 1 / Work.LinnikAreas.Sieve.gFun χ₁ m
        = ∑ m ∈ S, ∏ p ∈ m.primeFactors, (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ :=
          Finset.sum_congr rfl hgf
      _ = ∑ t ∈ S.image (fun m => m.primeFactors),
            ∏ p ∈ t, (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ :=
          (Finset.sum_image (f := fun t : Finset ℕ =>
            ∏ p ∈ t, (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹) hinj).symm
      _ ≤ ∑ t ∈ q.primeFactors.powerset,
            ∏ p ∈ t, (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  exact ⟨hS_nonneg, hub⟩

end Work.Sieve
