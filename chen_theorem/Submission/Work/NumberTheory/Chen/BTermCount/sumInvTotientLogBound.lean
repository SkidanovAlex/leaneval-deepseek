import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

open Finset

/-!
## `Σ_{n ≤ X} 1/φ(n) ≤ C log X`

We prove the classical elementary estimate `Σ_{n ≤ X} 1/φ(n) = O(log X)`.

The route is the standard one: for `n ≥ 1` the Dirichlet identity

  `n/φ(n) = ∏_{p | n} (1 + 1/(p-1)) = Σ_{d | n, d squarefree} 1/φ(d)`

expresses `1/φ(n)` as the Dirichlet convolution of `h(n) = [n squarefree]/(n φ n)`
with `g(n) = 1/n`, and `Σ_{n ≤ X} h(n) ≤ 4` (since `n/φ(n) ≤ 2^{ω n}` and
`2^{ω n}/n²` has bounded summatory function), while `Σ_{n ≤ X} 1/n ≤ 1 + log X`.
-/

/-! ### Squarefree divisors as subsets of the prime factors -/

private lemma injOn_prod_powerset (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (↑(s.powerset) : Set (Finset ℕ)) := by
  intro t ht t' ht' heq
  have ht1 : t ⊆ s := mem_powerset.mp ht
  have ht2 : t' ⊆ s := mem_powerset.mp ht'
  have h1 : (∏ p ∈ t, p).primeFactors = t :=
    Nat.primeFactors_prod fun p hp => hs p (ht1 hp)
  have h2 : (∏ p ∈ t', p).primeFactors = t' :=
    Nat.primeFactors_prod fun p hp => hs p (ht2 hp)
  have h3 : (∏ p ∈ t, p).primeFactors = (∏ p ∈ t', p).primeFactors := congrArg Nat.primeFactors heq
  rwa [h1, h2] at h3

private lemma image_prod_powerset_eq (n : ℕ) (hn : n ≠ 0) :
    (n.primeFactors.powerset).image (fun t : Finset ℕ => ∏ p ∈ t, p)
      = n.divisors.filter Squarefree := by
  classical
  ext d
  rw [mem_image, mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [mem_powerset] at ht
    have htpr : ∀ p ∈ t, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
    refine ⟨⟨?_, hn⟩, ?_⟩
    · exact (prod_dvd_prod_of_subset t n.primeFactors (fun x => x) ht).trans
        (Nat.prod_primeFactors_dvd n)
    · exact squarefree_prod_of_pairwise_isCoprime
        (fun a ha b hb hab =>
          Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (htpr a ha) (htpr b hb)).mpr hab))
        (fun p hp => (htpr p hp).squarefree)
  · rintro ⟨⟨hdvd, _⟩, hsq⟩
    refine ⟨d.primeFactors, ?_, ?_⟩
    · rw [mem_powerset]
      intro p hp
      exact Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.mem_primeFactors.mp hp).2.1.trans hdvd, hn⟩
    · exact Nat.prod_primeFactors_of_squarefree hsq

private lemma sum_sqfree_divisors_eq_sum_powerset (n : ℕ) (hn : n ≠ 0) (F : ℕ → ℝ) :
    ∑ d ∈ n.divisors.filter Squarefree, F d
      = ∑ t ∈ n.primeFactors.powerset, F (∏ p ∈ t, p) := by
  rw [← image_prod_powerset_eq n hn, sum_image]
  exact injOn_prod_powerset n.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp

private lemma totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  have hm : 0 < ∏ p ∈ s, p := prod_pos fun p hp => (hs p hp).pos
  have hpf : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod hs
  have hkey := Nat.totient_mul_prod_primeFactors (∏ p ∈ s, p)
  rw [hpf] at hkey
  have h2 : (∏ p ∈ s, p) * Nat.totient (∏ p ∈ s, p)
      = (∏ p ∈ s, p) * (∏ p ∈ s, (p - 1)) := by
    rw [mul_comm (∏ p ∈ s, p) (Nat.totient (∏ p ∈ s, p))]
    exact hkey
  exact Nat.eq_of_mul_eq_mul_left hm h2

private lemma totient_div_eq_prod (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) / (Nat.totient n : ℝ)
      = ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hcast : (Nat.totient n : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ))
      = (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
    push_cast at h
    rw [show (∏ i ∈ n.primeFactors, (↑(i - 1) : ℝ))
        = (∏ i ∈ n.primeFactors, ((i : ℝ) - 1)) from
      prod_congr rfl fun p hp => by
        rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]] at h
    exact h
  have hphi : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have hB : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun p hp => ?_
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  rw [div_eq_iff hphi, prod_div_distrib, div_mul_eq_mul_div, eq_div_iff hB]
  rw [mul_comm (∏ p ∈ n.primeFactors, (p : ℝ)) (Nat.totient n : ℝ), ← hcast]

private lemma pow_card_primeFactors_eq_sum_sqfree_divisors (z : ℝ) (n : ℕ) (hn : n ≠ 0) :
    z ^ n.primeFactors.card
      = ∑ d ∈ n.divisors.filter Squarefree, (z - 1) ^ d.primeFactors.card := by
  have hprime : ∀ p ∈ n.primeFactors, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [sum_sqfree_divisors_eq_sum_powerset n hn]
  have hexp : z ^ n.primeFactors.card
      = ∑ t ∈ n.primeFactors.powerset, (z - 1) ^ t.card := by
    rw [← prod_const (s := n.primeFactors) z]
    rw [show (∏ _p ∈ n.primeFactors, z)
        = ∏ _p ∈ n.primeFactors, (1 + (z - 1)) from prod_congr rfl fun p _ => by ring]
    rw [prod_one_add]
    exact sum_congr rfl fun t _ => prod_const (s := t) (z - 1)
  rw [hexp]
  refine sum_congr rfl fun t ht => ?_
  rw [mem_powerset] at ht
  rw [Nat.primeFactors_prod fun p hp => hprime p (ht hp)]

private lemma two_pow_card_eq_sum_sqfree_one (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ n.primeFactors.card = ∑ _d ∈ n.divisors.filter Squarefree, (1 : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  rw [pow_card_primeFactors_eq_sum_sqfree_divisors 2 n hn0]
  refine sum_congr rfl fun d _ => ?_
  rw [show ((2 : ℝ) - 1) = 1 by norm_num, one_pow]

/-! ### The key Dirichlet identity -/

private lemma totient_div_eq_sum_sqfree_inv_totient (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / (Nat.totient n : ℝ)
      = ∑ d ∈ n.divisors.filter Squarefree, 1 / (Nat.totient d : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  rw [totient_div_eq_prod n hn0]
  have hstep : ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))
      = ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
    refine prod_congr rfl fun p hp => ?_
    have hne : ((p : ℝ) - 1) ≠ 0 := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      linarith
    field_simp
    ring
  rw [hstep, prod_one_add]
  rw [sum_sqfree_divisors_eq_sum_powerset n hn0 (fun d => 1 / (Nat.totient d : ℝ))]
  refine sum_congr rfl fun t ht => ?_
  rw [mem_powerset] at ht
  have htprime : ∀ p ∈ t, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  have hb : (∏ p ∈ t, ((p : ℝ) - 1)) = ((Nat.totient (∏ p ∈ t, p) : ℕ) : ℝ) := by
    rw [totient_prod_primes t htprime]
    push_cast
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (htprime p hp).one_le, Nat.cast_one]
  simp only [one_div]
  rw [prod_inv_distrib, hb]

/-! ### The two arithmetic functions whose convolution gives `1/φ` -/

private noncomputable def hPhi : ArithmeticFunction ℝ where
  toFun n := if Squarefree n then 1 / ((n : ℝ) * (Nat.totient n : ℝ)) else 0
  map_zero' := by simp [not_squarefree_zero]

private noncomputable def gId : ArithmeticFunction ℝ where
  toFun n := ((n : ℝ))⁻¹
  map_zero' := by simp

private noncomputable def fSq : ArithmeticFunction ℝ where
  toFun n := if Squarefree n then ((n : ℝ) ^ 2)⁻¹ else 0
  map_zero' := by simp [not_squarefree_zero]

private noncomputable def gSq : ArithmeticFunction ℝ where
  toFun n := ((n : ℝ) ^ 2)⁻¹
  map_zero' := by simp

private lemma hPhi_apply (n : ℕ) :
    hPhi n = if Squarefree n then 1 / ((n : ℝ) * (Nat.totient n : ℝ)) else 0 := rfl

private lemma gId_apply (n : ℕ) : gId n = ((n : ℝ))⁻¹ := rfl

private lemma fSq_apply (n : ℕ) :
    fSq n = if Squarefree n then ((n : ℝ) ^ 2)⁻¹ else 0 := rfl

private lemma gSq_apply (n : ℕ) : gSq n = ((n : ℝ) ^ 2)⁻¹ := rfl

private lemma hPhi_nonneg (n : ℕ) : 0 ≤ hPhi n := by
  rw [hPhi_apply]; split
  · positivity
  · exact le_refl 0

private lemma fSq_nonneg (n : ℕ) : 0 ≤ fSq n := by
  rw [fSq_apply]; split
  · positivity
  · exact le_refl 0

private lemma gSq_nonneg (n : ℕ) : 0 ≤ gSq n := by rw [gSq_apply]; positivity

private lemma fSq_mul_gSq_nonneg (n : ℕ) : 0 ≤ (fSq * gSq) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun x _ => mul_nonneg (fSq_nonneg x.1) (gSq_nonneg x.2)

/-! ### Pointwise domination of `hPhi` by `fSq * gSq` -/

private lemma totient_div_le_two_pow_card (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / (Nat.totient n : ℝ) ≤ (2 : ℝ) ^ n.primeFactors.card := by
  have hn0 : n ≠ 0 := by omega
  rw [totient_div_eq_prod n hn0]
  calc ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))
      ≤ ∏ _p ∈ n.primeFactors, (2 : ℝ) := by
        refine prod_le_prod₀ ?_ ?_
        · intro p hp
          have hp1 : (1 : ℝ) < (p : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
          have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          positivity
        · intro p hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          rw [div_le_iff₀ hpos]
          linarith
    _ = (2 : ℝ) ^ n.primeFactors.card := prod_const 2

private lemma one_div_mul_totient_le (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) * (Nat.totient n : ℝ))
      ≤ (2 : ℝ) ^ n.primeFactors.card / (n : ℝ) ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have htn : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hkey : (n : ℝ) ≤ (2 : ℝ) ^ n.primeFactors.card * (Nat.totient n : ℝ) := by
    have h := totient_div_le_two_pow_card n hn
    rwa [div_le_iff₀ htn] at h
  have hsq : (n : ℝ) ^ 2
      ≤ (2 : ℝ) ^ n.primeFactors.card * (Nat.totient n : ℝ) * (n : ℝ) := by
    calc (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) := by ring
      _ ≤ ((2 : ℝ) ^ n.primeFactors.card * (Nat.totient n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hnR)
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith [hsq]

private lemma fSq_mul_gSq_apply (n : ℕ) (hn : 1 ≤ n) :
    (fSq * gSq) n = (2 : ℝ) ^ n.primeFactors.card / (n : ℝ) ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun a b => fSq a * gSq b)]
  have hterm : ∀ i ∈ n.divisors,
      fSq i * gSq (n / i)
        = (if Squarefree i then (((n : ℝ) ^ 2))⁻¹ else 0) := by
    intro i hi
    obtain ⟨hidvd, -⟩ := Nat.mem_divisors.mp hi
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hidvd)
    have hq : i * (n / i) = n := Nat.mul_div_cancel' hidvd
    have hcast : ((i : ℝ) * (((n / i : ℕ)) : ℝ)) = (n : ℝ) := by
      rw [← Nat.cast_mul, hq]
    rw [fSq_apply, gSq_apply]
    by_cases hs : Squarefree i
    · rw [if_pos hs, if_pos hs]
      rw [← mul_inv, ← mul_pow, hcast]
    · rw [if_neg hs, if_neg hs]; ring
  rw [sum_congr rfl hterm]
  have h1 : ∑ i ∈ n.divisors, (if Squarefree i then (((n : ℝ) ^ 2))⁻¹ else 0)
      = (((n : ℝ) ^ 2))⁻¹ * ∑ _i ∈ n.divisors.filter Squarefree, (1 : ℝ) := by
    rw [sum_filter, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : Squarefree i <;> simp [h]
  rw [h1, two_pow_card_eq_sum_sqfree_one n hn, div_eq_mul_inv]
  ring

private lemma hPhi_le (n : ℕ) : hPhi n ≤ (fSq * gSq) n := by
  by_cases hn : n = 0
  · subst hn
    rw [hPhi_apply, if_neg not_squarefree_zero]
    exact fSq_mul_gSq_nonneg 0
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [hPhi_apply, fSq_mul_gSq_apply n hn1]
    by_cases hs : Squarefree n
    · rw [if_pos hs]
      exact one_div_mul_totient_le n hn1
    · rw [if_neg hs]
      exact div_nonneg (pow_nonneg (by norm_num) _) (by positivity)

/-! ### The convolution evaluations -/

private lemma hPhi_mul_gId_apply (n : ℕ) (hn : 1 ≤ n) :
    (hPhi * gId) n = 1 / (Nat.totient n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn0
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun a b => hPhi a * gId b)]
  have hterm : ∀ i ∈ n.divisors,
      hPhi i * gId (n / i)
        = (1 / (n : ℝ)) * (if Squarefree i then 1 / (Nat.totient i : ℝ) else 0) := by
    intro i hi
    obtain ⟨hidvd, -⟩ := Nat.mem_divisors.mp hi
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hidvd)
    have hiR : ((i : ℝ)) ≠ 0 := by exact_mod_cast hi0
    have htn : ((Nat.totient i : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hi0)).ne'
    have hdiv : (((n / i : ℕ)) : ℝ)⁻¹ = (i : ℝ) / (n : ℝ) := by
      rw [Nat.cast_div hidvd hiR]
      field_simp
    rw [hPhi_apply, gId_apply]
    by_cases hs : Squarefree i
    · rw [if_pos hs, if_pos hs, hdiv]
      field_simp
    · rw [if_neg hs, if_neg hs]; ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have h1 : ∑ i ∈ n.divisors, (if Squarefree i then 1 / (Nat.totient i : ℝ) else 0)
      = ∑ i ∈ n.divisors.filter Squarefree, 1 / (Nat.totient i : ℝ) := by
    rw [sum_filter]
  rw [h1, ← totient_div_eq_sum_sqfree_inv_totient n hn]
  have htn : ((Nat.totient n : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)).ne'
  field_simp

/-! ### Bounds for the harmonic and square-reciprocal sums -/

private lemma sum_inv_sq_le_two (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  have hsplit : Finset.Icc 1 M = insert 1 (Finset.Ioc 1 M) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  have hnot : (1 : ℕ) ∉ Finset.Ioc 1 M := by simp [Finset.mem_Ioc]
  rw [hsplit, sum_insert hnot]
  have h2 : ∑ k ∈ Finset.Ioc 1 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 := by
    have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := M) (by norm_num) hM
    have h' : ∑ k ∈ Finset.Ioc 1 M, (1 : ℝ) / (k : ℝ) ^ 2
        = ∑ k ∈ Finset.Ioc 1 M, (((k : ℝ)) ^ 2)⁻¹ := by
      refine sum_congr rfl fun k _ => ?_
      rw [one_div]
    rw [h']
    have h3 : ((1 : ℝ))⁻¹ - (M : ℝ)⁻¹ ≤ 1 := by
      rw [inv_one]
      have : (0 : ℝ) ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
      linarith
    linarith
  have h1 : (1 : ℝ) / (1 : ℝ) ^ 2 = 1 := by norm_num
  linarith

private lemma sum_inv_le_one_add_log (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (M : ℝ) := by
  have hcast : ((harmonic M : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    refine sum_congr rfl fun k _ => ?_
    rw [one_div]
  rw [← hcast]
  exact harmonic_le_one_add_log M

/-! ### Summatory bounds for the two test functions -/

private lemma sum_fSq_le (X : ℕ) : ∑ n ∈ Finset.Ioc 0 X, fSq n ≤ 2 := by
  have hIoc : Finset.Ioc 0 X = Finset.Icc 1 X := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc]
  calc ∑ n ∈ Finset.Icc 1 X, fSq n
      ≤ ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ 2 := by
        refine sum_le_sum fun n _ => ?_
        rw [fSq_apply]
        by_cases h : Squarefree n
        · rw [if_pos h, one_div]
        · rw [if_neg h]; positivity
    _ ≤ 2 := sum_inv_sq_le_two X

private lemma sum_gSq_le (X : ℕ) : ∑ n ∈ Finset.Ioc 0 X, gSq n ≤ 2 := by
  have hIoc : Finset.Ioc 0 X = Finset.Icc 1 X := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc]
  calc ∑ n ∈ Finset.Icc 1 X, gSq n
      = ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ 2 := by
        refine sum_congr rfl fun n _ => ?_
        rw [gSq_apply, one_div]
    _ ≤ 2 := sum_inv_sq_le_two X

private lemma sum_fSq_mul_gSq_le (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (fSq * gSq) n ≤ 4 := by
  have hIoc : Finset.Ioc 0 X = Finset.Icc 1 X := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [← hIoc, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum fSq gSq X]
  have h1 : ∑ n ∈ Finset.Ioc 0 X, fSq n * ∑ m ∈ Finset.Ioc 0 (X / n), gSq m
      ≤ ∑ n ∈ Finset.Ioc 0 X, fSq n * ∑ m ∈ Finset.Ioc 0 X, gSq m := by
    refine sum_le_sum fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    refine mul_le_mul_of_nonneg_left ?_ (fSq_nonneg n)
    refine sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro m hm
      rw [Finset.mem_Ioc] at hm ⊢
      exact ⟨hm.1, hm.2.trans (Nat.div_le_self X n)⟩
    · intro m _ _; exact gSq_nonneg m
  calc ∑ n ∈ Finset.Ioc 0 X, fSq n * ∑ m ∈ Finset.Ioc 0 (X / n), gSq m
      ≤ ∑ n ∈ Finset.Ioc 0 X, fSq n * ∑ m ∈ Finset.Ioc 0 X, gSq m := h1
    _ = (∑ n ∈ Finset.Ioc 0 X, fSq n) * (∑ m ∈ Finset.Ioc 0 X, gSq m) :=
        (sum_mul _ _ _).symm
    _ ≤ 2 * 2 := by
        refine mul_le_mul (sum_fSq_le X) (sum_gSq_le X) ?_ ?_
        · exact sum_nonneg fun n _ => gSq_nonneg n
        · norm_num
    _ = 4 := by norm_num

private lemma sum_hPhi_le (X : ℕ) : ∑ n ∈ Finset.Icc 1 X, hPhi n ≤ 4 := by
  calc ∑ n ∈ Finset.Icc 1 X, hPhi n
      ≤ ∑ n ∈ Finset.Icc 1 X, (fSq * gSq) n := sum_le_sum fun n _ => hPhi_le n
    _ ≤ 4 := sum_fSq_mul_gSq_le X

/-! ### The main bound -/

theorem sumInvTotientLogBound : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
    (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (Nat.totient n : ℝ)) ≤ C * Real.log (X : ℝ) := by
  refine ⟨16, by norm_num, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have h2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hlogX : (1 : ℝ) / 2 ≤ Real.log (X : ℝ) := by
    have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
      norm_num at h
      linarith
    have hle : Real.log 2 ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hX)
    linarith
  have hIoc : Finset.Ioc 0 X = Finset.Icc 1 X := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hstep1 : (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (Nat.totient n : ℝ))
      = ∑ n ∈ Finset.Ioc 0 X, (hPhi * gId) n := by
    rw [hIoc]
    refine sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    exact (hPhi_mul_gId_apply n hn.1).symm
  have hstep2 : (∑ n ∈ Finset.Ioc 0 X, (hPhi * gId) n)
      = ∑ n ∈ Finset.Ioc 0 X, hPhi n * ∑ m ∈ Finset.Ioc 0 (X / n), gId m :=
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum hPhi gId X
  have hinner : ∀ n ∈ Finset.Ioc 0 X,
      (∑ m ∈ Finset.Ioc 0 (X / n), gId m) ≤ 1 + Real.log (X : ℝ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hset : Finset.Ioc 0 (X / n) = Finset.Icc 1 (X / n) := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hset]
    have h1 : ∑ m ∈ Finset.Icc 1 (X / n), gId m
        = ∑ m ∈ Finset.Icc 1 (X / n), (1 : ℝ) / (m : ℝ) := by
      refine sum_congr rfl fun m _ => ?_
      rw [gId_apply, one_div]
    rw [h1]
    have h2 := sum_inv_le_one_add_log (X / n)
    have h3 : Real.log (((X / n : ℕ)) : ℝ) ≤ Real.log (X : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · have hle : 1 ≤ X / n := (Nat.one_le_div_iff hn.1).mpr hn.2
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hle)
      · exact_mod_cast Nat.div_le_self X n
    linarith
  have hhPhi : (∑ n ∈ Finset.Ioc 0 X, hPhi n) ≤ 4 := by
    rw [hIoc]
    exact sum_hPhi_le X
  calc (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (Nat.totient n : ℝ))
      = ∑ n ∈ Finset.Ioc 0 X, (hPhi * gId) n := hstep1
    _ = ∑ n ∈ Finset.Ioc 0 X, hPhi n * ∑ m ∈ Finset.Ioc 0 (X / n), gId m := hstep2
    _ ≤ ∑ n ∈ Finset.Ioc 0 X, hPhi n * (1 + Real.log (X : ℝ)) :=
        sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hinner n hn) (hPhi_nonneg n)
    _ = (∑ n ∈ Finset.Ioc 0 X, hPhi n) * (1 + Real.log (X : ℝ)) := (sum_mul _ _ _).symm
    _ ≤ 4 * (1 + Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_right hhPhi (by linarith)
    _ ≤ 16 * Real.log (X : ℝ) := by linarith

end Work.NumberTheory.Chen.BTermCount
