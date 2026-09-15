import Mathlib
import Submission.Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct

/-!
# Euler product for the Dirichlet series, weighted summability hypothesis

Version of `Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct` in which the summability
hypothesis carries the extra decay factor `(p : Real) ^ (-c)`, `c > 0`, and the exponents are
assumed to have real part at least `c`.
-/

open Finset
open scoped BigOperators

set_option linter.unusedVariables false

namespace Commons.NumberTheory.Sieve

private lemma PrimeData.ne_zero_iff {m : ℕ} (σ : PrimeData m) :
    σ ≠ 0 ↔ σ.X ≠ ∅ ∨ σ.X' ≠ ∅ := by
  constructor
  · intro h
    by_contra hc
    simp only [not_or, ne_eq, not_not] at hc
    exact h (by
      obtain ⟨X, X'⟩ := σ
      obtain ⟨h1, h2⟩ := hc
      change X = ∅ at h1
      change X' = ∅ at h2
      rw [h1, h2]
      rfl)
  · rintro (h | h) hc
    · exact h (congrArg PrimeData.X hc)
    · exact h (congrArg PrimeData.X' hc)

/-! ## Auxiliary lemmas -/

/-- A product of distinct primes is squarefree. -/
private lemma squarefree_prod_of_primes {s : Finset ℕ} (h : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha' : Nat.Prime a := h a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, Nat.Prime p := fun p hp => h p (Finset.mem_insert_of_mem hp)
    have hsq : Squarefree a := Irreducible.squarefree ha'
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      rw [ha'.coprime_iff_not_dvd]
      intro hdvd
      have hp' : Nat.Prime p := hs p hp
      have hpe : p = a := (hp'.dvd_iff_eq ha'.ne_one).1 hdvd
      exact ha (hpe ▸ hp)
    exact (Nat.squarefree_mul hcop).mpr ⟨hsq, ih hs⟩

private lemma prod_natCast_cpow (s : Finset ℕ) (z : ℂ) :
    ((∏ p ∈ s, p : ℕ) : ℂ) ^ z = ∏ p ∈ s, (p : ℂ) ^ z := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul]
    rw [Complex.natCast_mul_natCast_cpow, ih]

/-- For a squarefree `n`, the complex power of its cast factors over its prime factors. -/
private lemma natCast_cpow_eq_prod_primeFactors {n : ℕ} (hn : Squarefree n) (z : ℂ) :
    (n : ℂ) ^ z = ∏ p ∈ n.primeFactors, (p : ℂ) ^ z := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  exact prod_natCast_cpow n.primeFactors z

/-- The complex Möbius function of a squarefree `n` is the product of `-1` over its primes. -/
private lemma moebius_eq_prod_neg_one {n : ℕ} (hn : Squarefree n) :
    (ArithmeticFunction.moebius n : ℂ) = ∏ _p ∈ n.primeFactors, (-1 : ℂ) := by
  have hΩ : (ArithmeticFunction.cardFactors n) = n.primeFactors.card := by
    have h1 : ArithmeticFunction.cardDistinctFactors n = ArithmeticFunction.cardFactors n :=
      (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero).mpr hn
    have h2 : ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
      rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors]
      exact List.card_toFinset _
    omega
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn, hΩ, Finset.prod_const]
  push_cast
  rfl

/-- The prime factors of `n` inside those of a nonzero multiple `P`. -/
private lemma primeFactors_filter_dvd {P n : ℕ} (hP : P ≠ 0) (hdvd : n ∣ P) :
    P.primeFactors.filter (fun p => p ∣ n) = n.primeFactors := by
  have hn : n ≠ 0 := by rintro rfl; exact hP (zero_dvd_iff.mp hdvd)
  ext p
  rw [Finset.mem_filter, Nat.mem_primeFactors_of_ne_zero hP, Nat.mem_primeFactors_of_ne_zero hn]
  constructor
  · rintro ⟨⟨hp, -⟩, hpn⟩
    exact ⟨hp, hpn⟩
  · rintro ⟨hp, hpn⟩
    exact ⟨⟨hp, hpn.trans hdvd⟩, hpn⟩

/-- If `n ∣ P` then a product over the prime factors of `P` weighted by the indicator of
`p ∣ n` collapses to a product over the prime factors of `n`. -/
private lemma prod_ite_dvd_eq_prod_primeFactors {M : Type*} [CommMonoid M] {P n : ℕ} (hP : P ≠ 0)
    (hdvd : n ∣ P) (f : ℕ → M) :
    ∏ p ∈ P.primeFactors, (if p ∣ n then f p else 1) = ∏ p ∈ n.primeFactors, f p := by
  rw [← Finset.prod_filter, primeFactors_filter_dvd hP hdvd]

/-- The complex power `p^{-z}` of a natural number with `Re z > 0` has norm at most one. -/
private lemma norm_natCast_cpow_neg_le_one (p : ℕ) (z : ℂ) (hz : 0 < z.re) :
    ‖(p : ℂ) ^ (-z)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have hzne : -z ≠ 0 := by
      intro h
      have : z = 0 := neg_eq_zero.mp h
      rw [this] at hz
      simp at hz
    rw [Nat.cast_zero, Complex.zero_cpow hzne, norm_zero]
    exact zero_le_one
  · rw [Complex.norm_natCast_cpow_of_pos h0, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast h0) (by linarith)

/-! ## The local weight attached to a prime and local data -/

/-- The summand of the Euler factor: the local weight at the prime `p` with local data `σ`,
*including* the Möbius sign. -/
private noncomputable def localW (m : ℕ) (v : ℕ → PrimeData m → ℂ) (z z' : Fin m → ℂ) (p : ℕ)
    (σ : PrimeData m) : ℂ :=
  v p σ * ((-1 : ℂ) ^ (σ.X.card + σ.X'.card)) *
    ((∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))) * (∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i))))

private lemma eulerFactor_eq_sum_localW (m : ℕ) (v : ℕ → PrimeData m → ℂ) (z z' : Fin m → ℂ)
    (p : ℕ) : eulerFactor m v z z' p = ∑ σ : PrimeData m, localW m v z z' p σ := rfl

private lemma norm_localW_le (m : ℕ) (v : ℕ → PrimeData m → ℂ) (z z' : Fin m → ℂ) (p : ℕ)
    (σ : PrimeData m) (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    ‖localW m v z z' p σ‖ ≤ ‖v p σ‖ := by
  have hA : ‖((-1 : ℂ) ^ (σ.X.card + σ.X'.card))‖ = 1 := by simp
  have hB : ‖∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))‖ ≤ 1 := by
    refine (Finset.norm_prod_le _ _).trans ?_
    exact Finset.prod_le_one (fun i _ => norm_nonneg _)
      (fun i _ => norm_natCast_cpow_neg_le_one p (z i) (hz i))
  have hC : ‖∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i))‖ ≤ 1 := by
    refine (Finset.norm_prod_le _ _).trans ?_
    exact Finset.prod_le_one (fun i _ => norm_nonneg _)
      (fun i _ => norm_natCast_cpow_neg_le_one p (z' i) (hz' i))
  have hBC : ‖∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))‖ * ‖∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i))‖ ≤ 1 :=
    by nlinarith [hB, hC, norm_nonneg (∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))),
      norm_nonneg (∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i)))]
  simp only [localW, norm_mul, hA]
  nlinarith [norm_nonneg (v p σ), hBC]

/-- `‖p^{-z}‖ ≤ p^{-c}` when `c > 0` and `c ≤ Re z`. -/
private lemma norm_cpow_neg_le_rpow (p : ℕ) (z : ℂ) (c : ℝ) (hc : 0 < c)
    (hz : c ≤ z.re) : ‖(p : ℂ) ^ (-z)‖ ≤ (p : ℝ) ^ (-c) := by
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have hzne : -z ≠ 0 := by
      intro h
      have hz0 : z = 0 := neg_eq_zero.mp h
      rw [hz0] at hz
      simp at hz
      linarith
    have h1 : ((0 : ℕ) : ℂ) ^ (-z) = 0 := by rw [Nat.cast_zero, Complex.zero_cpow hzne]
    have h2 : ((0 : ℕ) : ℝ) ^ (-c) = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (by linarith : -c ≠ 0)]
    rw [h1, h2]
    simp
  · rw [Complex.norm_natCast_cpow_of_pos h0, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h0) (by linarith)

/-- A product of `p^{-z_i}` over any index set has norm at most one. -/
private lemma norm_prod_cpow_neg_le_one {m : ℕ} (p : ℕ) (s : Finset (Fin m)) (z : Fin m → ℂ)
    (hz : ∀ i, 0 < (z i).re) : ‖∏ i ∈ s, (p : ℂ) ^ (-(z i))‖ ≤ 1 := by
  classical
  refine (Finset.norm_prod_le _ _).trans ?_
  exact Finset.prod_le_one (fun i _ => norm_nonneg _)
    (fun i _ => norm_natCast_cpow_neg_le_one p (z i) (hz i))

/-- A nonempty product of `p^{-z_i}` has norm at most `p^{-c}` when `Re z_i ≥ c > 0`. -/
private lemma norm_prod_cpow_neg_le_rpow {m : ℕ} (p : ℕ) (s : Finset (Fin m)) (z : Fin m → ℂ)
    (c : ℝ) (hc : 0 < c) (hz : ∀ i, c ≤ (z i).re) (hs : s.Nonempty) :
    ‖∏ i ∈ s, (p : ℂ) ^ (-(z i))‖ ≤ (p : ℝ) ^ (-c) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  refine (Finset.norm_prod_le _ _).trans ?_
  rw [← Finset.mul_prod_erase s (fun i => ‖(p : ℂ) ^ (-(z i))‖) hi₀]
  have h1 : ∏ i ∈ s.erase i₀, ‖(p : ℂ) ^ (-(z i))‖ ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _)
      (fun i _ => norm_natCast_cpow_neg_le_one p (z i) (lt_of_lt_of_le hc (hz i)))
  have h2 : ‖(p : ℂ) ^ (-(z i₀))‖ ≤ (p : ℝ) ^ (-c) :=
    norm_cpow_neg_le_rpow p (z i₀) c hc (hz i₀)
  calc ‖(p : ℂ) ^ (-(z i₀))‖ * ∏ i ∈ s.erase i₀, ‖(p : ℂ) ^ (-(z i))‖
      ≤ ‖(p : ℂ) ^ (-(z i₀))‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖(p : ℂ) ^ (-(z i₀))‖ := mul_one _
    _ ≤ (p : ℝ) ^ (-c) := h2

/-- The sharp (weighted) bound on the local weight: for `σ ≠ 0` the extra factor
`∏_{i∈σ.X} p^{-z_i} ∏_{i∈σ.X'} p^{-z'_i}` has norm at most `p^{-c}`. -/
private lemma norm_localW_le_weighted {m : ℕ} (v : ℕ → PrimeData m → ℂ) (z z' : Fin m → ℂ)
    (p : ℕ) (σ : PrimeData m) (hσ : σ ≠ 0) (c : ℝ) (hc : 0 < c)
    (hz : ∀ i, c ≤ (z i).re) (hz' : ∀ i, c ≤ (z' i).re) :
    ‖localW m v z z' p σ‖ ≤ ‖v p σ‖ * (p : ℝ) ^ (-c) := by
  have hsign : ‖((-1 : ℂ) ^ (σ.X.card + σ.X'.card))‖ = 1 := by simp
  have hnonneg : 0 ≤ (p : ℝ) ^ (-c) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hAB : ‖(∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))) * (∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i)))‖
      ≤ (p : ℝ) ^ (-c) := by
    rw [norm_mul]
    rcases (PrimeData.ne_zero_iff σ).mp hσ with hX | hX
    · have h1 := norm_prod_cpow_neg_le_rpow p σ.X z c hc hz (Finset.nonempty_iff_ne_empty.mpr hX)
      have h2 := norm_prod_cpow_neg_le_one p σ.X' z' (fun i => lt_of_lt_of_le hc (hz' i))
      calc ‖∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))‖ * ‖∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i))‖
          ≤ (p : ℝ) ^ (-c) * 1 := mul_le_mul h1 h2 (norm_nonneg _) hnonneg
        _ = (p : ℝ) ^ (-c) := mul_one _
    · have h1 := norm_prod_cpow_neg_le_one p σ.X z (fun i => lt_of_lt_of_le hc (hz i))
      have h2 := norm_prod_cpow_neg_le_rpow p σ.X' z' c hc hz' (Finset.nonempty_iff_ne_empty.mpr hX)
      calc ‖∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))‖ * ‖∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i))‖
          ≤ 1 * (p : ℝ) ^ (-c) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
        _ = (p : ℝ) ^ (-c) := one_mul _
  have hnorm : ‖localW m v z z' p σ‖
      = ‖v p σ‖ * ‖(∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))) * (∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i)))‖ := by
    simp only [localW, norm_mul, hsign, mul_one]
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left hAB (norm_nonneg _)


/-! ## The bijection between squarefree pairs and finitely supported local data -/

section Bijection

variable {m : ℕ}

/-- The pair of tuples attached to a finitely supported family of local data:
`d i = ∏_{p : i ∈ X_p} p` and `e i = ∏_{p : i ∈ X'_p} p`. -/
private noncomputable def pairOf (f : ℕ →₀ PrimeData m) : (Fin m → ℕ) × (Fin m → ℕ) :=
  (fun i => ∏ p ∈ f.support, if i ∈ (f p).X then p else 1,
   fun i => ∏ p ∈ f.support, if i ∈ (f p).X' then p else 1)

/-- All entries of the pair `de` are squarefree. -/
private def IsSqPair (de : (Fin m → ℕ) × (Fin m → ℕ)) : Prop :=
  ∀ i, Squarefree (de.1 i) ∧ Squarefree (de.2 i)

private lemma IsSqPair.prod_ne_zero {de : (Fin m → ℕ) × (Fin m → ℕ)} (h : IsSqPair de) :
    (∏ i, de.1 i * de.2 i) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  exact fun i _ => mul_ne_zero (h i).1.ne_zero (h i).2.ne_zero

/-- The finitely supported family of local data attached to a squarefree pair of tuples. -/
private noncomputable def finsuppOf (de : (Fin m → ℕ) × (Fin m → ℕ)) (h : IsSqPair de) :
    ℕ →₀ PrimeData m :=
  Finsupp.onFinset ((∏ i, de.1 i * de.2 i)).primeFactors
    (fun p => if p.Prime then
      (⟨univ.filter (fun i => p ∣ de.1 i), univ.filter (fun i => p ∣ de.2 i)⟩ : PrimeData m)
      else 0)
    (fun p hp => by
      rw [Nat.mem_primeFactors]
      by_cases hpp : p.Prime
      · rw [if_pos hpp] at hp
        rcases (PrimeData.ne_zero_iff _).mp hp with hX | hX
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hX
          exact ⟨hpp, dvd_trans (dvd_trans (Finset.mem_filter.mp hi).2 (dvd_mul_right _ _))
            (dvd_prod_of_mem _ (Finset.mem_univ i)), h.prod_ne_zero⟩
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hX
          exact ⟨hpp, dvd_trans (dvd_trans (Finset.mem_filter.mp hi).2 (dvd_mul_left _ _))
            (dvd_prod_of_mem _ (Finset.mem_univ i)), h.prod_ne_zero⟩
      · rw [if_neg hpp] at hp
        exact absurd rfl hp)

private lemma finsuppOf_apply (de : (Fin m → ℕ) × (Fin m → ℕ)) (h : IsSqPair de) (p : ℕ) :
    finsuppOf de h p = if p.Prime then
      (⟨univ.filter (fun i => p ∣ de.1 i), univ.filter (fun i => p ∣ de.2 i)⟩ : PrimeData m)
      else 0 :=
  Finsupp.onFinset_apply

private lemma finsuppOf_apply_of_prime (de : (Fin m → ℕ) × (Fin m → ℕ)) (h : IsSqPair de) {p : ℕ}
    (hp : p.Prime) :
    finsuppOf de h p =
      ⟨univ.filter (fun i => p ∣ de.1 i), univ.filter (fun i => p ∣ de.2 i)⟩ := by
  rw [finsuppOf_apply, if_pos hp]

private lemma support_finsuppOf (de : (Fin m → ℕ) × (Fin m → ℕ)) (h : IsSqPair de) :
    (finsuppOf de h).support = (∏ i, de.1 i * de.2 i).primeFactors := by
  rw [finsuppOf, Finsupp.support_onFinset]
  refine Finset.filter_true_of_mem (fun p hp => ?_)
  rw [if_pos (Nat.prime_of_mem_primeFactors hp)]
  have hdiv : p ∣ ∏ i, de.1 i * de.2 i := (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨i, -, hi⟩ := ((Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp)).dvd_finsetProd_iff
    (fun i => de.1 i * de.2 i)).mp hdiv
  rcases (Nat.prime_of_mem_primeFactors hp).dvd_mul.mp hi with h | h
  · exact (PrimeData.ne_zero_iff _).mpr (Or.inl (Finset.ne_empty_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)))
  · exact (PrimeData.ne_zero_iff _).mpr (Or.inr (Finset.ne_empty_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)))

private lemma prime_of_mem_support_finsuppOf (de : (Fin m → ℕ) × (Fin m → ℕ)) (h : IsSqPair de)
    {p : ℕ} (hp : p ∈ (finsuppOf de h).support) : p.Prime :=
  Nat.prime_of_mem_primeFactors (support_finsuppOf de h ▸ hp)

/-- The primes dividing `d i`, read from the finsupp of local data. -/
private lemma dvd_pairOf_left (f : ℕ →₀ PrimeData m) (hf : ∀ p ∈ f.support, p.Prime)
    {p : ℕ} (hp : p.Prime) (i : Fin m) :
    p ∣ (pairOf f).1 i ↔ p ∈ f.support ∧ i ∈ (f p).X := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ :=
      ((Nat.prime_iff.mp hp).dvd_finsetProd_iff (fun q => if i ∈ (f q).X then q else 1)).mp h
    by_cases hqi : i ∈ (f q).X
    · rw [if_pos hqi] at hpq
      have hq' : Nat.Prime q := hf q hq
      have hqe : q = p := (hq'.dvd_iff_eq hp.ne_one).1 hpq
      exact ⟨hqe ▸ hq, hqe ▸ hqi⟩
    · rw [if_neg hqi] at hpq
      exact absurd (Nat.dvd_one.mp hpq) hp.ne_one
  · rintro ⟨hps, hip⟩
    exact dvd_trans (show p ∣ (if i ∈ (f p).X then p else 1) by rw [if_pos hip])
      (dvd_prod_of_mem (fun q => if i ∈ (f q).X then q else 1) hps)

private lemma dvd_pairOf_right (f : ℕ →₀ PrimeData m) (hf : ∀ p ∈ f.support, p.Prime)
    {p : ℕ} (hp : p.Prime) (i : Fin m) :
    p ∣ (pairOf f).2 i ↔ p ∈ f.support ∧ i ∈ (f p).X' := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ :=
      ((Nat.prime_iff.mp hp).dvd_finsetProd_iff (fun q => if i ∈ (f q).X' then q else 1)).mp h
    by_cases hqi : i ∈ (f q).X'
    · rw [if_pos hqi] at hpq
      have hq' : Nat.Prime q := hf q hq
      have hqe : q = p := (hq'.dvd_iff_eq hp.ne_one).1 hpq
      exact ⟨hqe ▸ hq, hqe ▸ hqi⟩
    · rw [if_neg hqi] at hpq
      exact absurd (Nat.dvd_one.mp hpq) hp.ne_one
  · rintro ⟨hps, hip⟩
    exact dvd_trans (show p ∣ (if i ∈ (f p).X' then p else 1) by rw [if_pos hip])
      (dvd_prod_of_mem (fun q => if i ∈ (f q).X' then q else 1) hps)

/-- A prime divides `∏ i, d i * e i` (for `(d,e) = pairOf f`) exactly when it is in the support. -/
private lemma prime_dvd_prod_pairOf (f : ℕ →₀ PrimeData m) (hf : ∀ p ∈ f.support, p.Prime)
    {p : ℕ} (hp : p.Prime) :
    p ∣ (∏ i, (pairOf f).1 i * (pairOf f).2 i) ↔ p ∈ f.support := by
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff
      (fun i => (pairOf f).1 i * (pairOf f).2 i)).mp h
    rcases hp.dvd_mul.mp hi with h' | h'
    · exact ((dvd_pairOf_left f hf hp i).mp h').1
    · exact ((dvd_pairOf_right f hf hp i).mp h').1
  · intro hps
    have hne : (f p) ≠ 0 := Finsupp.mem_support_iff.mp hps
    rcases (PrimeData.ne_zero_iff _).mp hne with hX | hX
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hX
      exact dvd_trans (dvd_trans ((dvd_pairOf_left f hf hp i).mpr ⟨hps, hi⟩) (dvd_mul_right _ _))
        (dvd_prod_of_mem _ (Finset.mem_univ i))
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hX
      exact dvd_trans (dvd_trans ((dvd_pairOf_right f hf hp i).mpr ⟨hps, hi⟩) (dvd_mul_left _ _))
        (dvd_prod_of_mem _ (Finset.mem_univ i))

/-- The pair of tuples attached to a family of local data supported on primes is squarefree. -/
private lemma isSqPair_pairOf (f : ℕ →₀ PrimeData m) (hf : ∀ p ∈ f.support, p.Prime) :
    IsSqPair (pairOf f) := by
  intro i
  have h1 : (pairOf f).1 i = ∏ p ∈ f.support.filter (fun p => i ∈ (f p).X), p := by
    simp only [pairOf, Finset.prod_filter]
  have h2 : (pairOf f).2 i = ∏ p ∈ f.support.filter (fun p => i ∈ (f p).X'), p := by
    simp only [pairOf, Finset.prod_filter]
  exact ⟨h1 ▸ squarefree_prod_of_primes (fun p hp => hf p (Finset.mem_filter.mp hp).1),
    h2 ▸ squarefree_prod_of_primes (fun p hp => hf p (Finset.mem_filter.mp hp).1)⟩

/-- Round trip: the local data attached to the pair of a family is the original family. -/
private lemma finsuppOf_pairOf (f : ℕ →₀ PrimeData m) (hf : ∀ p ∈ f.support, p.Prime) :
    finsuppOf (pairOf f) (isSqPair_pairOf f hf) = f := by
  ext p
  by_cases hps : p ∈ f.support
  · have hp : p.Prime := hf p hps
    rw [finsuppOf_apply_of_prime (pairOf f) (isSqPair_pairOf f hf) hp]
    have hX : Finset.univ.filter (fun i => p ∣ (pairOf f).1 i) = (f p).X := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [dvd_pairOf_left f hf hp i, and_iff_right hps]
    have hX' : Finset.univ.filter (fun i => p ∣ (pairOf f).2 i) = (f p).X' := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [dvd_pairOf_right f hf hp i, and_iff_right hps]
    rw [hX, hX']
  · rw [Finsupp.notMem_support_iff.mp hps, finsuppOf_apply]
    by_cases hp : p.Prime
    · rw [if_pos hp]
      have hX : Finset.univ.filter (fun i => p ∣ (pairOf f).1 i) = ∅ := by
        rw [← not_nonempty_iff_eq_empty]
        rintro ⟨i, hi⟩
        exact hps ((dvd_pairOf_left f hf hp i).mp (Finset.mem_filter.mp hi).2).1
      have hX' : Finset.univ.filter (fun i => p ∣ (pairOf f).2 i) = ∅ := by
        rw [← not_nonempty_iff_eq_empty]
        rintro ⟨i, hi⟩
        exact hps ((dvd_pairOf_right f hf hp i).mp (Finset.mem_filter.mp hi).2).1
      rw [hX, hX']
      rfl
    · rw [if_neg hp]

/-- Round trip: the pair of tuples attached to squarefree data is the original pair. -/
private lemma pairOf_finsuppOf (de : (Fin m → ℕ) × (Fin m → ℕ)) (h : IsSqPair de) :
    pairOf (finsuppOf de h) = de := by
  have hP : (∏ i, de.1 i * de.2 i) ≠ 0 := h.prod_ne_zero
  have hdvd (i : Fin m) : de.1 i ∣ ∏ i, de.1 i * de.2 i :=
    dvd_trans (dvd_mul_right _ _) (dvd_prod_of_mem _ (Finset.mem_univ i))
  have hdvd' (i : Fin m) : de.2 i ∣ ∏ i, de.1 i * de.2 i :=
    dvd_trans (dvd_mul_left _ _) (dvd_prod_of_mem _ (Finset.mem_univ i))
  apply Prod.ext
  · funext i
    show (∏ p ∈ (finsuppOf de h).support,
      (if i ∈ ((finsuppOf de h) p).X then p else 1)) = de.1 i
    rw [support_finsuppOf]
    trans ∏ p ∈ (∏ i, de.1 i * de.2 i).primeFactors, (if p ∣ de.1 i then p else 1)
    · refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [finsuppOf_apply_of_prime de h (Nat.prime_of_mem_primeFactors hp)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · rw [prod_ite_dvd_eq_prod_primeFactors hP (hdvd i) (fun p => p),
        Nat.prod_primeFactors_of_squarefree (h i).1]
  · funext i
    show (∏ p ∈ (finsuppOf de h).support,
      (if i ∈ ((finsuppOf de h) p).X' then p else 1)) = de.2 i
    rw [support_finsuppOf]
    trans ∏ p ∈ (∏ i, de.1 i * de.2 i).primeFactors, (if p ∣ de.2 i then p else 1)
    · refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [finsuppOf_apply_of_prime de h (Nat.prime_of_mem_primeFactors hp)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · rw [prod_ite_dvd_eq_prod_primeFactors hP (hdvd' i) (fun p => p),
        Nat.prod_primeFactors_of_squarefree (h i).2]

/-- Finitely supported local data which is supported on primes. -/
private def GoodFinsupp (m : ℕ) : Set (ℕ →₀ PrimeData m) := {f | ∀ p ∈ f.support, p.Prime}

/-- Pairs of tuples all of whose entries are squarefree. -/
private def GoodPair (m : ℕ) : Set ((Fin m → ℕ) × (Fin m → ℕ)) := {de | IsSqPair de}

/-- The bijection. -/
private noncomputable def goodEquiv (m : ℕ) : ↥(GoodFinsupp m) ≃ ↥(GoodPair m) where
  toFun f := ⟨pairOf f.1, isSqPair_pairOf f.1 f.2⟩
  invFun de := ⟨finsuppOf de.1 de.2, fun _ hp => prime_of_mem_support_finsuppOf de.1 de.2 hp⟩
  left_inv f := by
    refine Subtype.ext ?_
    exact finsuppOf_pairOf f.1 f.2
  right_inv de := by
    refine Subtype.ext ?_
    exact pairOf_finsuppOf de.1 de.2

end Bijection

/-! ## The summand of the Dirichlet series -/

section Summand

variable {m : ℕ}

/-- The summand of the `Λ_R²` Dirichlet series: the Möbius factors times the global coefficient. -/
private noncomputable def summand (m : ℕ) (v : ℕ → PrimeData m → ℂ) (z z' : Fin m → ℂ)
    (de : (Fin m → ℕ) × (Fin m → ℕ)) : ℂ :=
  (∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ) * (ArithmeticFunction.moebius (de.2 i) : ℂ)
    * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i)))))
  * localWeight m v de.1 de.2

/-- The per-prime factorisation of `∏_i (1 - p^{-z_i}[p ∣ d_i])(1 - p^{-z'_i}[p ∣ e_i])`. -/
private lemma prod_ite_mul_eq (d e : Fin m → ℕ) (z z' : Fin m → ℂ) (p : ℕ) :
    (∏ i, ((if p ∣ d i then (-1 : ℂ) * (p : ℂ) ^ (-(z i)) else 1) *
            (if p ∣ e i then (-1 : ℂ) * (p : ℂ) ^ (-(z' i)) else 1)))
      = (-1 : ℂ) ^ ((univ.filter (fun i => p ∣ d i)).card
            + (univ.filter (fun i => p ∣ e i)).card) *
        ((∏ i ∈ univ.filter (fun i => p ∣ d i), (p : ℂ) ^ (-(z i))) *
         (∏ i ∈ univ.filter (fun i => p ∣ e i), (p : ℂ) ^ (-(z' i)))) := by
  rw [Finset.prod_mul_distrib]
  have h1 : (∏ i, if p ∣ d i then (-1 : ℂ) * (p : ℂ) ^ (-(z i)) else 1)
      = (-1 : ℂ) ^ (univ.filter (fun i => p ∣ d i)).card *
        (∏ i ∈ univ.filter (fun i => p ∣ d i), (p : ℂ) ^ (-(z i))) := by
    rw [← Finset.prod_filter, Finset.prod_mul_distrib, Finset.prod_const]
  have h2 : (∏ i, if p ∣ e i then (-1 : ℂ) * (p : ℂ) ^ (-(z' i)) else 1)
      = (-1 : ℂ) ^ (univ.filter (fun i => p ∣ e i)).card *
        (∏ i ∈ univ.filter (fun i => p ∣ e i), (p : ℂ) ^ (-(z' i))) := by
    rw [← Finset.prod_filter, Finset.prod_mul_distrib, Finset.prod_const]
  rw [h1, h2, pow_add]
  ring

/-- The Möbius product of a squarefree pair of tuples factors over the primes. -/
private lemma mobius_prod_eq (d e : Fin m → ℕ) (z z' : Fin m → ℂ)
    (hd : ∀ i, Squarefree (d i)) (he : ∀ i, Squarefree (e i)) :
    (∏ i, (ArithmeticFunction.moebius (d i) : ℂ) * (ArithmeticFunction.moebius (e i) : ℂ)
        * ((d i : ℂ) ^ (-(z i))) * ((e i : ℂ) ^ (-(z' i))))
      = ∏ p ∈ (∏ i, d i * e i).primeFactors,
          (-1 : ℂ) ^ ((univ.filter (fun i => p ∣ d i)).card
              + (univ.filter (fun i => p ∣ e i)).card) *
          ((∏ i ∈ univ.filter (fun i => p ∣ d i), (p : ℂ) ^ (-(z i))) *
           (∏ i ∈ univ.filter (fun i => p ∣ e i), (p : ℂ) ^ (-(z' i)))) := by
  have hP : (∏ i, d i * e i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => mul_ne_zero (hd i).ne_zero (he i).ne_zero
  have hdvd (i : Fin m) : d i ∣ ∏ i, d i * e i :=
    dvd_trans (dvd_mul_right _ _) (dvd_prod_of_mem _ (Finset.mem_univ i))
  have hedvd (i : Fin m) : e i ∣ ∏ i, d i * e i :=
    dvd_trans (dvd_mul_left _ _) (dvd_prod_of_mem _ (Finset.mem_univ i))
  have key (i : Fin m) :
      (ArithmeticFunction.moebius (d i) : ℂ) * (ArithmeticFunction.moebius (e i) : ℂ)
        * ((d i : ℂ) ^ (-(z i))) * ((e i : ℂ) ^ (-(z' i)))
      = ∏ p ∈ (∏ i, d i * e i).primeFactors,
          ((if p ∣ d i then (-1 : ℂ) * (p : ℂ) ^ (-(z i)) else 1) *
           (if p ∣ e i then (-1 : ℂ) * (p : ℂ) ^ (-(z' i)) else 1)) := by
    have hdi : (ArithmeticFunction.moebius (d i) : ℂ) * ((d i : ℂ) ^ (-(z i)))
        = ∏ p ∈ (∏ i, d i * e i).primeFactors,
            (if p ∣ d i then (-1 : ℂ) * (p : ℂ) ^ (-(z i)) else 1) := by
      rw [moebius_eq_prod_neg_one (hd i), natCast_cpow_eq_prod_primeFactors (hd i),
        ← Finset.prod_mul_distrib,
        prod_ite_dvd_eq_prod_primeFactors hP (hdvd i) (fun p => (-1 : ℂ) * (p : ℂ) ^ (-(z i)))]
    have hei : (ArithmeticFunction.moebius (e i) : ℂ) * ((e i : ℂ) ^ (-(z' i)))
        = ∏ p ∈ (∏ i, d i * e i).primeFactors,
            (if p ∣ e i then (-1 : ℂ) * (p : ℂ) ^ (-(z' i)) else 1) := by
      rw [moebius_eq_prod_neg_one (he i), natCast_cpow_eq_prod_primeFactors (he i),
        ← Finset.prod_mul_distrib,
        prod_ite_dvd_eq_prod_primeFactors hP (hedvd i) (fun p => (-1 : ℂ) * (p : ℂ) ^ (-(z' i)))]
    have step : (ArithmeticFunction.moebius (d i) : ℂ) * (ArithmeticFunction.moebius (e i) : ℂ)
          * ((d i : ℂ) ^ (-(z i))) * ((e i : ℂ) ^ (-(z' i)))
        = ((ArithmeticFunction.moebius (d i) : ℂ) * ((d i : ℂ) ^ (-(z i))))
          * ((ArithmeticFunction.moebius (e i) : ℂ) * ((e i : ℂ) ^ (-(z' i)))) := by ring
    rw [step, hdi, hei]
    exact (Finset.prod_mul_distrib (s := (∏ i, d i * e i).primeFactors)).symm
  rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_comm]
  exact Finset.prod_congr rfl (fun p _ => prod_ite_mul_eq d e z z' p)

/-- On squarefree pairs, the summand is the product of the local weights over the support. -/
private lemma summand_eq_prod_localW (de : (Fin m → ℕ) × (Fin m → ℕ)) (h : IsSqPair de)
    (v : ℕ → PrimeData m → ℂ) (z z' : Fin m → ℂ) :
    summand m v z z' de
      = ∏ p ∈ (finsuppOf de h).support, localW m v z z' p (finsuppOf de h p) := by
  rw [summand, localWeight, support_finsuppOf,
    mobius_prod_eq de.1 de.2 z z' (fun i => (h i).1) (fun i => (h i).2),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [finsuppOf_apply_of_prime de h (Nat.prime_of_mem_primeFactors hp), localW]
  ring

end Summand
private noncomputable def eulerTerm (m : ℕ) (v : ℕ → PrimeData m → ℂ) (z z' : Fin m → ℂ)
    (f : ℕ →₀ PrimeData m) : ℂ :=
  ∏ n ∈ f.support, localW m v z z' n (f n)

private lemma localW_zero (m : ℕ) (v : ℕ → PrimeData m → ℂ) (z z' : Fin m → ℂ) (p : ℕ) :
    localW m v z z' p (0 : PrimeData m) = v p 0 := by
  rw [localW]
  rw [show ((0 : PrimeData m)).X = ∅ from rfl, show ((0 : PrimeData m)).X' = ∅ from rfl]
  simp


/-- **Euler product for the Green–Tao §10 Dirichlet series, with the *weighted* summability
hypothesis.**  This is exactly `Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct` except
that the summability hypothesis `hv3` carries the extra decay factor `(p : ℝ) ^ (-c)`, `c > 0`,
and the conclusion is restricted to exponents `z, z'` with real part at least `c`.

WHY: in the application (Green–Tao §10, eq. (10.2)/(10.7)) the local weights are
`v p σ = (density of the congruence system defined by σ)`, so `v p ⟨{i}, ∅⟩ = 1/p` exactly and
`v p σ = O(1/p²)` for `|σ.X ∪ σ.X'| ≥ 2`.  Hence the *unweighted* hypothesis
`Summable (fun p => ∑ σ, ‖v p σ - δ_{σ0}‖)` of the existing version is FALSE for the application
(its `2m` single-index terms give `∑_p 1/p = ∞`), while the weighted version holds: the single
index terms contribute `∑_p p^{-(1+c)} < ∞`.  The existing version was proved with the crude bound
`‖localW m v z z' p σ‖ ≤ ‖v p σ‖`; the weighted version needs the sharper bound
`‖localW m v z z' p σ‖ ≤ ‖v p σ‖ * (p : ℝ) ^ (-c)` for `σ ≠ 0`, which holds because every index in
`σ.X ∪ σ.X'` contributes a factor `‖(p : ℂ) ^ (-(z i))‖ = (p : ℝ) ^ (-(z i).re) ≤ (p : ℝ) ^ (-c)`
(`Complex.norm_natCast_cpow_neg`), and `σ ≠ 0` means at least one such factor is present.

PROOF: copy `Submission/Commons/NumberTheory/Sieve/hasSum_dirichlet_eulerProduct.lean` (all the
bookkeeping there — `localW`, `eulerFactor_eq_sum_localW`, the squarefree-pair bijection
`GoodFinsupp ↔ GoodPair`, the round trips, and the final reduction to
`Commons.Analysis.DirichletSeries.eulerProduct_finsupp` — is independent of how the summability
input `hsum : Summable (fun p => ∑ σ, ‖localW m v z z' p σ - δ_{σ0}‖)` is obtained) and replace only
the derivation of `hsum`: from `hv3` and the sharper `norm_localW_le` above,
`∑ σ, ‖localW m v z z' p σ - (if σ = 0 then 1 else 0)‖ ≤ ∑ σ, ‖v p σ - (if σ = 0 then 1 else 0)‖ * p^{-c}`
(use `localW` at `σ = 0`: `localW m v z z' p 0 = v p 0 = 1`), then `Summable.of_nonneg_of_le`.
The hypothesis `hv4` and the final support arguments are unchanged (they only use `‖v p σ‖ ≤ C/p`).
Note `c` is not used anywhere except through `hv3` and `hz`/`hz'`. -/
theorem hasSum_dirichlet_eulerProduct_weighted (m : ℕ) (v : ℕ → PrimeData m → ℂ)
    (C c : ℝ) (hc : 0 < c)
    (hv1 : ∀ p : ℕ, v p 0 = 1)
    (hv2 : ∀ p : ℕ, ¬ Nat.Prime p → ∀ σ : PrimeData m, σ ≠ 0 → v p σ = 0)
    (hv3 : Summable (fun p : ℕ => ∑ σ : PrimeData m,
        ‖v p σ - (if σ = 0 then 1 else 0)‖ * (p : ℝ) ^ (-c)))
    (hv4 : ∀ p : ℕ, ∀ σ : PrimeData m, σ ≠ 0 → ‖v p σ‖ ≤ C / (p : ℝ))
    (z z' : Fin m → ℂ) (hz : ∀ i, c ≤ (z i).re) (hz' : ∀ i, c ≤ (z' i).re) :
    HasSum (fun de : (Fin m → ℕ) × (Fin m → ℕ) =>
        (∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ) * (ArithmeticFunction.moebius (de.2 i) : ℂ)
          * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i)))))
        * localWeight m v de.1 de.2)
      (∏' p : ℕ, eulerFactor m v z z' p)
:= by
  classical
  have hsum : Summable (fun p : ℕ =>
      ∑ σ : PrimeData m, ‖localW m v z z' p σ - (if σ = 0 then 1 else 0)‖) := by
    refine Summable.of_nonneg_of_le (fun p => Finset.sum_nonneg (fun σ _ => norm_nonneg _))
      (fun p => ?_) hv3
    refine Finset.sum_le_sum (fun σ _ => ?_)
    by_cases hσ : σ = 0
    · subst hσ
      rw [localW_zero m v z z' p, hv1 p]
      simp
    · simp only [if_neg hσ, sub_zero]
      exact norm_localW_le_weighted v z z' p σ hσ c hc hz hz'
  have hbase := Commons.Analysis.DirichletSeries.eulerProduct_finsupp (PrimeData m)
    (localW m v z z')
    (fun n => by rw [localW_zero m v z z' n, hv1 n])
    (fun n hn a ha => by rw [localW, hv2 n hn a ha]; ring) hsum
  have hEP : HasSum (eulerTerm m v z z') (∏' p : ℕ, eulerFactor m v z z' p) := hbase
  have hsuppT : Function.support (eulerTerm m v z z') ⊆ GoodFinsupp m := by
    intro f hf p hp
    by_contra hnp
    refine hf (Finset.prod_eq_zero hp ?_)
    rw [localW, hv2 p hnp (f p) (Finsupp.mem_support_iff.mp hp)]
    ring
  have h2 : HasSum (eulerTerm m v z z' ∘ Subtype.val) (∏' p : ℕ, eulerFactor m v z z' p) :=
    (hasSum_subtype_iff_of_support_subset hsuppT).mpr hEP
  have h3 : HasSum (fun de : ↥(GoodPair m) => summand m v z z' ↑de)
      (∏' p : ℕ, eulerFactor m v z z' p) := by
    have h := (Equiv.hasSum_iff (e := (goodEquiv m).symm)
      (f := eulerTerm m v z z' ∘ Subtype.val)).mpr h2
    refine h.congr_fun (fun de => ?_)
    have hsq : IsSqPair (de : (Fin m → ℕ) × (Fin m → ℕ)) :=
      de.2
    show summand m v z z' (de : (Fin m → ℕ) × (Fin m → ℕ))
      = ∏ n ∈ (finsuppOf (de : (Fin m → ℕ) × (Fin m → ℕ)) hsq).support,
          localW m v z z' n (finsuppOf (de : (Fin m → ℕ) × (Fin m → ℕ)) hsq n)
    exact summand_eq_prod_localW (m := m) (de : (Fin m → ℕ) × (Fin m → ℕ)) hsq v z z'
  have hsuppS : Function.support (summand m v z z') ⊆ GoodPair m := by
    intro de hde
    by_contra hns
    simp only [GoodPair, Set.mem_ofPred_eq] at hns
    rw [IsSqPair, not_forall] at hns
    obtain ⟨i, hi⟩ := hns
    rw [not_and_or] at hi
    rcases hi with hi | hi
    · have hz0 : (∏ i, (ArithmeticFunction.moebius (de.1 i) : ℂ)
            * (ArithmeticFunction.moebius (de.2 i) : ℂ)
            * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i)))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i)
          (by simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi])
      exact hde (by rw [summand, hz0, zero_mul])
    · have hz0 : (∏ i, (ArithmeticFunction.moebius (de.1 i) : ℂ)
            * (ArithmeticFunction.moebius (de.2 i) : ℂ)
            * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i)))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i)
          (by simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi])
      exact hde (by rw [summand, hz0, zero_mul])
  have h4 : HasSum (summand m v z z') (∏' p : ℕ, eulerFactor m v z z' p) :=
    (hasSum_subtype_iff_of_support_subset hsuppS).mp h3
  exact h4


end Commons.NumberTheory.Sieve
