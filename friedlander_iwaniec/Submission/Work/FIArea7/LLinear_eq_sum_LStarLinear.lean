import Mathlib
import Submission.Work.FIArea7.prop232Defs

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## The `m`-smooth part of a natural number

The index set of the expansion `L(N) = Σ_{k | m^∞} L∗`-type`(N/k)` of *FI* Prop. 23.2 is the set of
`m`-smooth numbers `k ≤ N`; the `k` attached to a given `n` is its `m`-smooth part,
`∏_{p | m} p ^ v_p(n)`.  This section develops that function and the facts needed for the
reindexing. -/

/-- The `m`-smooth part of `n`: the largest divisor of `n` all of whose prime factors divide `m`,
i.e. `∏_{p | m} p ^ (v_p n)`. -/
def smoothPart (m n : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p ^ n.factorization p

lemma smoothPart_ne_zero (m n : ℕ) : smoothPart m n ≠ 0 := by
  rw [smoothPart]
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- The `p`-adic valuation of the `m`-smooth part of `n`, as a sum over the primes of `m`. -/
lemma smoothPart_factorization (m n q : ℕ) :
    (smoothPart m n).factorization q
      = ∑ p ∈ m.primeFactors, (if p = q then n.factorization p else 0) := by
  rw [smoothPart, Nat.factorization_prod_apply]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization (Nat.prime_of_mem_primeFactors hp), Finsupp.single_apply]
    simp [mul_ite]
  · intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- The `p`-adic valuation of the `m`-smooth part of `n`: it is `v_p(n)` when `p | m` and `0`
otherwise. -/
lemma smoothPart_factorization' (m n q : ℕ) :
    (smoothPart m n).factorization q = if q ∈ m.primeFactors then n.factorization q else 0 := by
  rw [smoothPart_factorization, Finset.sum_ite_eq']

lemma smoothPart_factorization'' (m n q : ℕ) (hm : m ≠ 0) :
    (smoothPart m n).factorization q = if q.Prime ∧ q ∣ m then n.factorization q else 0 := by
  rw [smoothPart_factorization']
  by_cases h : q ∈ m.primeFactors
  · rw [if_pos h, if_pos ⟨(Nat.mem_primeFactors.mp h).1, (Nat.mem_primeFactors.mp h).2.1⟩]
  · rw [if_neg h, if_neg fun hc => h (Nat.mem_primeFactors.mpr ⟨hc.1, hc.2, hm⟩)]

/-- The `m`-smooth part of `n` divides `n`. -/
lemma smoothPart_dvd (m n : ℕ) (hn : n ≠ 0) : smoothPart m n ∣ n := by
  rw [← Nat.factorization_le_iff_dvd (smoothPart_ne_zero m n) hn, Finsupp.le_def]
  intro q
  rw [smoothPart_factorization']
  by_cases hq : q ∈ m.primeFactors
  · rw [if_pos hq]
  · rw [if_neg hq]; exact Nat.zero_le _

/-- Every prime divisor of the `m`-smooth part of `n` divides `m`. -/
lemma smoothPart_msmooth (m n : ℕ) : msmooth m (smoothPart m n) := by
  intro p hp hpd
  by_contra hpm
  have hz : (smoothPart m n).factorization p = 0 := by
    rw [smoothPart_factorization', if_neg]
    intro hmem
    exact hpm (Nat.dvd_of_mem_primeFactors hmem)
  have hpos := hp.factorization_pos_of_dvd (smoothPart_ne_zero m n) hpd
  omega

/-- The `m`-smooth part of `n` is at least `1`. -/
lemma smoothPart_pos (m n : ℕ) : 1 ≤ smoothPart m n := by
  rw [smoothPart]
  exact Finset.one_le_prod₀ fun p hp => Nat.one_le_pow _ p (Nat.prime_of_mem_primeFactors hp).pos

/-- The quotient `n / (m`-smooth part of `n)` is coprime to `m`. -/
lemma smoothPart_coprime (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.Coprime (n / smoothPart m n) m := by
  rw [← not_not (a := Nat.Coprime (n / smoothPart m n) m), Nat.Prime.not_coprime_iff_dvd]
  rintro ⟨p, hp, hpd, hpm⟩
  have hkmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩
  have hk_dvd := smoothPart_dvd m n hn
  have hkpos : 0 < smoothPart m n := Nat.pos_of_ne_zero (smoothPart_ne_zero m n)
  have hle : smoothPart m n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hk_dvd
  have hqne : n / smoothPart m n ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨ne_of_gt hkpos, hle⟩
  have hfact : (n / smoothPart m n).factorization p = 0 := by
    rw [Nat.factorization_div hk_dvd, Finsupp.tsub_apply, smoothPart_factorization',
      if_pos hkmem, tsub_self]
  have hpos := hp.factorization_pos_of_dvd hqne hpd
  omega

/-- A divisor of `m ^ N` is `m`-smooth. -/
lemma msmooth_of_dvd_pow (m k N : ℕ) (hm : m ≠ 0) (hk : k ∣ m ^ N) : msmooth m k := by
  have hkne : k ≠ 0 := fun h => by
    rw [h] at hk; exact pow_ne_zero N hm (zero_dvd_iff.mp hk)
  have hsub : k.primeFactors ⊆ m.primeFactors :=
    (Nat.exists_dvd_pow_iff hkne hm).mp ⟨N, hk⟩
  intro p hp hpk
  exact Nat.dvd_of_mem_primeFactors (hsub (Nat.mem_primeFactors.mpr ⟨hp, hpk, hkne⟩))

/-- If `n ≤ N` then the `m`-smooth part of `n` divides `m ^ N`. -/
lemma smoothPart_dvd_pow (m N n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnN : n ≤ N) :
    smoothPart m n ∣ m ^ N := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hkk : smoothPart m n ≤ n := Nat.le_of_dvd (by omega) (smoothPart_dvd m n hn0)
  have hsubset : (smoothPart m n).primeFactors ⊆ m.primeFactors := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, smoothPart_msmooth m n p hp.1 hp.2.1, hm0⟩
  have h1 : smoothPart m n ∣ m ^ (smoothPart m n) :=
    (Nat.dvd_pow_self_iff (smoothPart_ne_zero m n) hm0).mpr hsubset
  exact dvd_trans h1 (Nat.pow_dvd_pow m (by omega))

/-- **Uniqueness of the `m`-smooth decomposition.**  If `k ∣ n`, every prime of `k` divides `m`,
and `n / k` is coprime to `m`, then `k` is the `m`-smooth part of `n`. -/
lemma eq_smoothPart_of_dvd_of_msmooth_of_coprime (m n k : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hk : k ∣ n) (hkm : msmooth m k) (hcop : Nat.Coprime (n / k) m) :
    k = smoothPart m n := by
  have hkne : k ≠ 0 := by
    intro h; rw [h] at hk; exact hn (zero_dvd_iff.mp hk)
  apply Nat.eq_of_factorization_eq hkne (smoothPart_ne_zero m n)
  intro p
  by_cases hpp : p.Prime
  · by_cases hpm : p ∣ m
    · have hqne : n / k ≠ 0 :=
        Nat.div_ne_zero_iff.mpr ⟨hkne, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hk⟩
      have hz : (n / k).factorization p = 0 := by
        have hc : Nat.Coprime p (n / k) := (hcop.coprime_dvd_right hpm).symm
        exact Nat.factorization_eq_zero_of_not_dvd (hpp.coprime_iff_not_dvd.mp hc)
      have hval : n.factorization p = k.factorization p := by
        have h2 := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_mul hkne hqne)
        rw [Nat.mul_div_cancel' hk, Finsupp.add_apply, hz, add_zero] at h2
        exact h2
      rw [smoothPart_factorization'' m n p hm, if_pos ⟨hpp, hpm⟩, hval]
    · rw [smoothPart_factorization'' m n p hm, if_neg (fun hc => hpm hc.2)]
      exact Nat.factorization_eq_zero_of_not_dvd (fun hpk => hpm (hkm p hpp hpk))
  · rw [smoothPart_factorization'' m n p hm, if_neg (fun hc => hpp hc.1)]
    exact Nat.factorization_eq_zero_of_not_prime k hpp

/-! ## The reindexing -/

/-- **The splitting of `L(N)` along the `m`-smooth part of `n`** (the "next" step of *FI*
Prop. 23.2, `L(N) = Σ_{e | m} Σ_{c | e^∞} Σ_{n ≤ N/c, (n,m)=1} λ(cmn)`):
for `m ≥ 1`

  `L(N) = Σ_{k ≤ N, k | m^∞} L∗`-type with modulus `mk` and length `N/k`
        `= Σ_{k ∈ (Icc 1 N).filter (fun k => k ∣ m^N)} LStarLinear (m*k) (N/k) ψ`.

(The index set `{k ∈ Icc 1 N : k ∣ m^N}` is exactly the `m`-smooth numbers `≤ N`:
`Work.FIArea7.msmooth m k` (`= ∀ p, p.Prime → p ∣ k → p ∣ m`) holds for every divisor `k` of `m^N`,
and conversely an `m`-smooth `k ≤ N` satisfies `v_p(k) ≤ k ≤ N ≤ N·v_p(m)` for every `p ∣ k`, so
`k ∣ m^N`.)

Proof route: the map `(k, n') ↦ k·n'` is a bijection from
`P := {(k,n') : k ∈ K, n' ∈ Icc 1 (N/k), Nat.Coprime n' (m*k)}` (`K := (Icc 1 N).filter (· ∣ m^N)`)
onto `Icc 1 N`, with inverse given by the **`m`-smooth part** of `n`:
`k := ∏_{p ∈ m.primeFactors} p ^ (n.factorization p)`, `n' := n / k`.
One has `k ∣ n` and `k ∣ m^N` (the `p`-adic valuation of `k` is `n.factorization p` for `p ∣ m`
and `0` otherwise, via `Nat.factorization_prod`/`Nat.factorization_pow` on the pairwise coprime
factors `p ^ _`), every prime of `k` divides `m`, `Nat.Coprime (n/k) m` (the primes of `n/k` do not
divide `m`), and `k ≤ N`, `n' ≤ N/k`; conversely, if `k₁ ∣ m^N` has `k₁ ∣ n` and
`Nat.Coprime (n/k₁) m`, then `k₁ = k` (as `k₁ ∣ k`, and `k = k₁ · (k/k₁)` forces `k/k₁ = 1` because
any prime factor of `k/k₁` divides `m` and would also divide `n/k₁`).  Hence the sums over
`n ∈ Icc 1 N` and over `P` agree; the bookkeeping is `Finset.sum_sigma` (for
`Σ_{k ∈ K} Σ_{n' ∈ (Icc 1 (N/k)).filter (Coprime · (m*k))}`) followed by `Finset.sum_bij`. -/
theorem LLinear_eq_sum_LStarLinear (m N : ℕ) (hm : 1 ≤ m) (psi : GaussianInt → ℂ) :
    Work.FIArea7.LLinear m N psi
      = ∑ k ∈ (Finset.Icc 1 N).filter (fun k => k ∣ m ^ N),
          Work.FIArea7.LStarLinear (m * k) (N / k) psi := by
  have hm0 : m ≠ 0 := by omega
  set K : Finset ℕ := (Finset.Icc 1 N).filter (fun k => k ∣ m ^ N) with hK
  set D : ℕ → Finset ℕ :=
    fun k => (Finset.Icc 1 (N / k)).filter (fun n' => Nat.Coprime n' (m * k)) with hD
  have hRHS : (∑ k ∈ K, Work.FIArea7.LStarLinear (m * k) (N / k) psi)
      = ∑ p ∈ K.sigma D, quadEigen psi (m * (p.1 * p.2)) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Work.FIArea7.LStarLinear, ← Finset.sum_filter]
    simp only [hD]
    refine Finset.sum_congr rfl fun n' hn' => ?_
    simp only [Nat.mul_assoc]
  rw [Work.FIArea7.LLinear, hRHS]
  symm
  refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hk, hn⟩ := hp
    simp only [hK, Finset.mem_filter, Finset.mem_Icc] at hk
    simp only [hD, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hk1, hk2⟩, -⟩ := hk
    obtain ⟨⟨hn1, hn2⟩, -⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨one_le_mul hk1 hn1,
      (Nat.mul_le_mul_left p.1 hn2).trans (Nat.mul_div_le N p.1)⟩
  · intro p1 hp1 p2 hp2 heq
    rw [Finset.mem_sigma] at hp1 hp2
    obtain ⟨hk1, hn1⟩ := hp1
    obtain ⟨hk2, hn2⟩ := hp2
    simp only [hK, Finset.mem_filter, Finset.mem_Icc] at hk1 hk2
    simp only [hD, Finset.mem_filter, Finset.mem_Icc] at hn1 hn2
    obtain ⟨⟨hk1a, hk1b⟩, hk1dvd⟩ := hk1
    obtain ⟨⟨hk2a, hk2b⟩, hk2dvd⟩ := hk2
    obtain ⟨⟨hn1a, hn1b⟩, hn1cop⟩ := hn1
    obtain ⟨⟨hn2a, hn2b⟩, hn2cop⟩ := hn2
    have hk1pos : 0 < p1.1 := by omega
    have hk2pos : 0 < p2.1 := by omega
    have hnz1 : p1.1 * p1.2 ≠ 0 := mul_ne_zero (by omega) (by omega)
    have hnz2 : p2.1 * p2.2 ≠ 0 := mul_ne_zero (by omega) (by omega)
    have hms1 : msmooth m p1.1 := msmooth_of_dvd_pow m p1.1 N hm0 hk1dvd
    have hms2 : msmooth m p2.1 := msmooth_of_dvd_pow m p2.1 N hm0 hk2dvd
    have hcop1 : Nat.Coprime ((p1.1 * p1.2) / p1.1) m := by
      rw [Nat.mul_div_cancel_left p1.2 hk1pos]
      exact hn1cop.coprime_dvd_right (dvd_mul_right m p1.1)
    have hcop2 : Nat.Coprime ((p2.1 * p2.2) / p2.1) m := by
      rw [Nat.mul_div_cancel_left p2.2 hk2pos]
      exact hn2cop.coprime_dvd_right (dvd_mul_right m p2.1)
    have hkeq1 : p1.1 = smoothPart m (p1.1 * p1.2) :=
      eq_smoothPart_of_dvd_of_msmooth_of_coprime m (p1.1 * p1.2) p1.1 hm0 hnz1
        (dvd_mul_right p1.1 p1.2) hms1 hcop1
    have hkeq2 : p2.1 = smoothPart m (p2.1 * p2.2) :=
      eq_smoothPart_of_dvd_of_msmooth_of_coprime m (p2.1 * p2.2) p2.1 hm0 hnz2
        (dvd_mul_right p2.1 p2.2) hms2 hcop2
    have hk12 : p1.1 = p2.1 := by rw [hkeq1, hkeq2, heq]
    have hn12 : p1.2 = p2.2 := by
      have h2 : p1.1 * p1.2 = p1.1 * p2.2 := by rw [heq, hk12]
      exact Nat.mul_left_cancel hk1pos h2
    exact Sigma.ext hk12 (heq_of_eq hn12)
  · intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨hn1, hn2⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hkpos : 0 < smoothPart m n := Nat.pos_of_ne_zero (smoothPart_ne_zero m n)
    have hkdvd : smoothPart m n ∣ n := smoothPart_dvd m n hn0
    have hkle : smoothPart m n ≤ n := Nat.le_of_dvd (by omega) hkdvd
    have hmemK : smoothPart m n ∈ K := by
      rw [hK, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨smoothPart_pos m n, by omega⟩, smoothPart_dvd_pow m N n hm hn1 hn2⟩
    have hmemD : n / smoothPart m n ∈ D (smoothPart m n) := by
      simp only [hD, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨(Nat.one_le_div_iff hkpos).mpr hkle, Nat.div_le_div_right hn2⟩, ?_⟩
      refine (smoothPart_coprime m n hm0 hn0).mul_right ?_
      rw [← not_not (a := Nat.Coprime (n / smoothPart m n) (smoothPart m n)),
        Nat.Prime.not_coprime_iff_dvd]
      rintro ⟨p, hp, hpd, hpk⟩
      exact hp.coprime_iff_not_dvd.mp
        ((smoothPart_coprime m n hm0 hn0).symm.coprime_dvd_left
          (smoothPart_msmooth m n p hp hpk)) hpd
    refine ⟨⟨smoothPart m n, n / smoothPart m n⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]; exact ⟨hmemK, hmemD⟩
    · exact Nat.mul_div_cancel' hkdvd
  · intro p hp
    rfl

end

end Work.FIArea7
