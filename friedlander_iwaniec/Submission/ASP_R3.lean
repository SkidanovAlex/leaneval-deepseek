import Submission.ASP_R

set_option maxHeartbeats 4000000

/-!
# Hypothesis `(R₃)` of the companion "Asymptotic sieve for primes" for `X² + Y⁴`

The companion paper's Theorem 2 (its §9) applies to sequences which are *not*
supported on squarefree numbers.  Instead of `(R)` it assumes the slightly
stronger `(R₃)`: for `L = (log x)^{2^24}` and a modulus cut-off `D = D(x)` with
`x^{2/3} < D < x`,

  `(R₃)   ∑^{♭3}_{d < D L²} |r_d(t)| ≤ A(x) L^{-2}   for all t ≤ x`,

the superscript restricting to cubefree moduli.

This file verifies `(R₃)` for the Friedlander–Iwaniec sequence
`a_n = #{(a,c) ∈ ℤ² : a² + c⁴ = n}` with the choice `D = ⌊x^{7/10}⌋`.  The exponent
`7/10` is optimal for our method: Lemma 3.1 `(3.3)` of the main paper carries a
`x^{1/100}` slack, which requires `D·L² ≤ x^{3/4 - 1/25}`.

The proof of the decomposition used here (every cubefree `d` with `¬ 4 ∣ d` is
`d₁ d₂²` with `d₁, d₂` squarefree and coprime) is in this file; it is what makes
the `cubeSum` normalisation of §3 of the main paper applicable to the cubefree sum.
-/

namespace Submission

open Finset

/-- `d` is cubefree: no prime cube divides it. -/
def Cubefree (d : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d

/-- Decidable version of `Cubefree`, phrased with `primeFactors` (so that it can be
used inside a `Finset.filter`). -/
def CubefreeD (d : ℕ) : Prop := ∀ p ∈ d.primeFactors, d.factorization p ≤ 2

instance instDecidableCubefreeD (d : ℕ) : Decidable (CubefreeD d) :=
  inferInstanceAs (Decidable (∀ p ∈ d.primeFactors, d.factorization p ≤ 2))

lemma cubefree_iff (d : ℕ) (hd : d ≠ 0) :
    Cubefree d ↔ ∀ p : ℕ, d.factorization p ≤ 2 := by
  constructor
  · intro h p
    by_contra hc
    have hc' : 3 ≤ d.factorization p := by omega
    have hp : p.Prime := by
      by_contra hp
      rw [Nat.factorization_eq_zero_of_not_prime d hp] at hc'
      omega
    exact h p hp ((hp.pow_dvd_iff_le_factorization hd).mpr hc')
  · intro h p hp hdiv
    have h3 : 3 ≤ d.factorization p := (hp.pow_dvd_iff_le_factorization hd).mp hdiv
    have := h p
    omega

lemma cubefree_iff_cubefreeD (d : ℕ) (hd : d ≠ 0) : Cubefree d ↔ CubefreeD d := by
  rw [cubefree_iff d hd]
  constructor
  · intro h p hp
    exact h p
  · intro h p
    by_cases hp : p ∈ d.primeFactors
    · exact h p hp
    · have : d.factorization p = 0 := by
        by_contra hz
        have hpp : p.Prime := by
          by_contra hp'
          exact hz (Nat.factorization_eq_zero_of_not_prime d hp')
        exact hp (Nat.mem_primeFactors.mpr ⟨hpp, Nat.dvd_of_factorization_pos hz, hd⟩)
      omega

/-- **Cubefree decomposition**: a cubefree `d` with `¬ 4 ∣ d` is `d₁ d₂²` with `d₁, d₂`
squarefree and coprime. -/
lemma cubefree_decomp {d : ℕ} (hd : 0 < d) (hc : Cubefree d) (h4 : ¬ 4 ∣ d) :
    ∃ d₁ d₂ : ℕ, Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ d₁ * d₂ ^ 2 = d := by
  classical
  have hd0 : d ≠ 0 := by omega
  set S : Finset ℕ := d.primeFactors.filter (fun p => d.factorization p = 2) with hS
  set S₁ : Finset ℕ := d.primeFactors.filter (fun p => d.factorization p = 1) with hS₁
  set d₂ : ℕ := ∏ p ∈ S, p with hd₂
  set d₁ : ℕ := ∏ p ∈ S₁, p with hd₁
  have hdle2 : ∀ p, d.factorization p ≤ 2 := (cubefree_iff d hd0).mp hc
  have h2le1 : d.factorization 2 ≤ 1 := by
    by_contra h
    exact h4 ((Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := 2) (n := d)
      Nat.prime_two hd0).mpr (by omega))
  have hmemS : ∀ {p : ℕ}, p ∈ S → p ∈ d.primeFactors := by
    intro p hp
    rw [hS] at hp
    exact (Finset.mem_filter.mp hp).1
  have hmemS₁ : ∀ {p : ℕ}, p ∈ S₁ → p ∈ d.primeFactors := by
    intro p hp
    rw [hS₁] at hp
    exact (Finset.mem_filter.mp hp).1
  have hle : ∀ {p : ℕ}, p ∈ S → d.factorization p = 2 := by
    intro p hp
    rw [hS] at hp
    exact (Finset.mem_filter.mp hp).2
  have hle₁ : ∀ {p : ℕ}, p ∈ S₁ → d.factorization p = 1 := by
    intro p hp
    rw [hS₁] at hp
    exact (Finset.mem_filter.mp hp).2
  have hd₂0 : d₂ ≠ 0 := by
    rw [hd₂]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    exact (Nat.prime_of_mem_primeFactors (hmemS hp)).ne_zero
  have hd₁0 : d₁ ≠ 0 := by
    rw [hd₁]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    exact (Nat.prime_of_mem_primeFactors (hmemS₁ hp)).ne_zero
  have hfac₁ : ∀ q : ℕ, d₁.factorization q = if q ∈ S₁ then 1 else 0 := by
    intro q
    have hsum : (∏ p ∈ S₁, p).factorization = ∑ p ∈ S₁, Finsupp.single p 1 := by
      rw [Nat.factorization_prod (fun p hp => (Nat.prime_of_mem_primeFactors (hmemS₁ hp)).ne_zero)]
      exact Finset.sum_congr rfl fun p hp =>
        Nat.Prime.factorization (Nat.prime_of_mem_primeFactors (hmemS₁ hp))
    rw [hd₁, hsum, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']

  have hfac₂ : ∀ q : ℕ, d₂.factorization q = if q ∈ S then 1 else 0 := by
    intro q
    have hsum : (∏ p ∈ S, p).factorization = ∑ p ∈ S, Finsupp.single p 1 := by
      rw [Nat.factorization_prod (fun p hp => (Nat.prime_of_mem_primeFactors (hmemS hp)).ne_zero)]
      exact Finset.sum_congr rfl fun p hp =>
        Nat.Prime.factorization (Nat.prime_of_mem_primeFactors (hmemS hp))
    rw [hd₂, hsum, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']

  have hdisj : Disjoint S₁ S := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have e1 := hle₁ hp1
    have e2 := hle hp2
    omega
  refine ⟨d₁, d₂, ?_, ?_, ?_, ?_⟩
  · rw [Nat.squarefree_iff_factorization_le_one hd₁0]
    intro q
    rw [hfac₁]
    split <;> omega
  · rw [Nat.squarefree_iff_factorization_le_one hd₂0]
    intro q
    rw [hfac₂]
    split <;> omega
  · have hgcd : d₁.gcd d₂ = 1 := by
      refine Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left hd₁0) one_ne_zero fun q => ?_
      rw [Nat.factorization_gcd hd₁0 hd₂0, Finsupp.inf_apply, hfac₁, hfac₂, Nat.factorization_one]
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      by_cases hq1 : q ∈ S₁
      · have hq2 : q ∉ S := fun h => Finset.disjoint_left.mp hdisj hq1 h
        simp [hq1, hq2]
      · by_cases hq2 : q ∈ S
        · simp [hq1, hq2]
        · simp [hq1, hq2]
    exact hgcd
  · refine Nat.eq_of_factorization_eq (mul_ne_zero hd₁0 (pow_ne_zero 2 hd₂0)) hd0 fun q => ?_
    rw [Nat.factorization_mul hd₁0 (pow_ne_zero 2 hd₂0), Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hfac₁, hfac₂]
    by_cases hq : q ∈ d.primeFactors
    · obtain ⟨hpq, hdvd, -⟩ := Nat.mem_primeFactors.mp hq
      have hge : 1 ≤ d.factorization q := (hpq.dvd_iff_one_le_factorization hd0).mp hdvd
      have hle2 := hdle2 q
      by_cases h1 : q ∈ S₁
      · have e1 : d.factorization q = 1 := hle₁ h1
        have h2 : q ∉ S := fun h => Finset.disjoint_left.mp hdisj h1 h
        simp [h1, h2, e1]
      · by_cases h2 : q ∈ S
        · have e2 : d.factorization q = 2 := hle h2
          simp [h1, h2, e2]
        · exfalso
          have hmem₁ : q ∈ S ∪ S₁ := by
            rcases (by omega : d.factorization q = 1 ∨ d.factorization q = 2) with h | h
            · exact Finset.mem_union.mpr (Or.inr (show q ∈ S₁ from by
                rw [hS₁]; exact Finset.mem_filter.mpr ⟨hq, h⟩))
            · exact Finset.mem_union.mpr (Or.inl (show q ∈ S from by
                rw [hS]; exact Finset.mem_filter.mpr ⟨hq, h⟩))
          rcases Finset.mem_union.mp hmem₁ with h | h
          · exact h2 h
          · exact h1 h
    · have hz : d.factorization q = 0 := by
        by_contra hz
        have hpq : q.Prime := by
          by_contra hq'
          exact hz (Nat.factorization_eq_zero_of_not_prime d hq')
        exact hq (Nat.mem_primeFactors.mpr ⟨hpq, Nat.dvd_of_factorization_pos hz, hd0⟩)
      have h1 : q ∉ S₁ := fun h => hq (hmemS₁ h)
      have h2 : q ∉ S := fun h => hq (hmemS h)
      simp [h1, h2, hz]



/-- The modulus cut-off of `(R₃)`: `D(x)·L² = x^{7/10}(log x)^{2^25}` with `L = (log x)^{2^24}`. -/
noncomputable def R3cut (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)⌋₊

/-- The left hand side of `(R₃)`, restricted to the cubefree moduli `¬ 4 ∣ d`. -/
noncomputable def R3sum (x t : ℕ) : ℝ :=
  ∑ d ∈ (Finset.range (R3cut x)).filter (fun d => CubefreeD d ∧ ¬ 4 ∣ d),
    |(Ad d t : ℝ) - (gdens d : ℝ) * (Aseq t : ℝ)|

/-- The sum over the cubefree moduli `¬ 4 ∣ d` of a nonnegative function is at most the
`cubeSum` over the pairs `(d₁, d₂)` of §3 of the main paper (via the cubefree decomposition). -/
lemma cubefree_sum_le_cubeSum (M : ℕ) (hM : 1 ≤ M) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ d ∈ (Finset.range M).filter (fun d => CubefreeD d ∧ ¬ 4 ∣ d), F d)
      ≤ cubeSum M (fun d₁ d₂ => F (d₁ * d₂ ^ 2)) := by
  classical
  set T : Finset ℕ := (Finset.range M).filter (fun d => CubefreeD d ∧ ¬ 4 ∣ d) with hT
  set P : Finset (ℕ × ℕ) :=
    (((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 (Nat.sqrt M))).filter
      (fun p => cubeCond M p.1 p.2)) with hP
  have hdec : ∀ d : ℕ, ∃ p : ℕ × ℕ, d ∈ T →
      (Squarefree p.1 ∧ Squarefree p.2 ∧ Nat.Coprime p.1 p.2 ∧ p.1 * p.2 ^ 2 = d) := by
    intro d
    by_cases hd : d ∈ T
    · obtain ⟨hdM, hcd, h4⟩ := Finset.mem_filter.mp (by rw [← hT]; exact hd)
      have hdlt : d < M := Finset.mem_range.mp hdM
      have hcd' : Cubefree d := (cubefree_iff_cubefreeD d (by omega)).mpr hcd
      obtain ⟨d₁, d₂, h1, h2, h3, h4'⟩ := cubefree_decomp (by omega) hcd' h4
      exact ⟨(d₁, d₂), fun _ => ⟨h1, h2, h3, h4'⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hd⟩
  choose φ hφ using hdec
  have hmemP : ∀ d ∈ T, φ d ∈ P := by
    intro d hd
    obtain ⟨h1, h2, h3, h4⟩ := hφ d hd
    obtain ⟨hdM, -, h4n⟩ := Finset.mem_filter.mp (by rw [← hT]; exact hd)
    have hdlt : d < M := Finset.mem_range.mp hdM
    have hφ1pos : 0 < (φ d).1 := (h1.ne_zero).bot_lt
    have hφ2pos : 0 < (φ d).2 := (h2.ne_zero).bot_lt
    rw [hP, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨hφ1pos, ?_⟩
      calc (φ d).1 ≤ (φ d).1 * (φ d).2 ^ 2 := Nat.le_mul_of_pos_right _ (pow_pos hφ2pos 2)
        _ = d := h4
        _ ≤ M := le_of_lt hdlt
    · rw [Finset.mem_Icc]
      refine ⟨hφ2pos, ?_⟩
      rw [Nat.le_sqrt']
      have h5 : (φ d).2 ^ 2 ≤ (φ d).1 * (φ d).2 ^ 2 := Nat.le_mul_of_pos_left _ hφ1pos
      rw [h4] at h5
      exact le_trans h5 (le_of_lt hdlt)
    · refine ⟨h1, h2, h3, ?_, ?_⟩
      · rw [h4]; exact h4n
      · rw [h4]; exact le_of_lt hdlt
  have hinj : ∀ a ∈ T, ∀ b ∈ T, φ a = φ b → a = b := by
    intro a ha b hb heq
    obtain ⟨h1, h2, h3, h4⟩ := hφ a ha
    obtain ⟨h5, h6, h7, h8⟩ := hφ b hb
    obtain ⟨h9, h10⟩ := Prod.ext_iff.mp heq
    rw [← h4, ← h8, h9, h10]
  calc (∑ d ∈ T, F d)
      = ∑ d ∈ T, F ((φ d).1 * (φ d).2 ^ 2) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [(hφ d hd).2.2.2]
    _ = ∑ p ∈ T.image φ, F (p.1 * p.2 ^ 2) := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hinj a ha b hb hab
    _ ≤ ∑ p ∈ P, F (p.1 * p.2 ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
          exact hmemP d hd
        · intro p _ _
          exact hF _
    _ = cubeSum M (fun d₁ d₂ => F (d₁ * d₂ ^ 2)) := by
        have hpp : (∑ d₁ ∈ Finset.Icc 1 M, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt M),
              (if cubeCond M d₁ d₂ then F (d₁ * d₂ ^ 2) else 0))
            = ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 (Nat.sqrt M)),
                (if cubeCond M p.1 p.2 then F (p.1 * p.2 ^ 2) else 0) := by
          rw [Finset.sum_product]
        have hpp2 : (∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 (Nat.sqrt M)),
                (if cubeCond M p.1 p.2 then F (p.1 * p.2 ^ 2) else 0))
            = ∑ p ∈ P, F (p.1 * p.2 ^ 2) := by
          rw [hP, Finset.sum_filter]
        rw [← hpp2, ← hpp, cubeSum]


/-- The general "power beats polylog" comparison with an arbitrary polylog loss `B`. -/
lemma poly_tail_gen (K α β c B : ℝ) (hK : 0 < K) (hα : α < 3 / 4) (hc : 0 < c) :
    ∃ X : ℕ, 5 ≤ X ∧ ∀ x : ℕ, X ≤ x →
      K * (x : ℝ) ^ α * (Real.log x) ^ β
        ≤ c * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-B) := by
  obtain ⟨X₁, -, hX₁⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := K / c) (by positivity)
      (n := ⌈β + B⌉₊) (r := (3:ℝ)/4 - α) (by linarith)
  refine ⟨max 5 ⌈X₁⌉₊ + 1, by omega, fun x hx => ?_⟩
  have hx5 : 5 ≤ x := by omega
  have hxX : X₁ ≤ (x : ℝ) := by
    have h1 : ((max 5 ⌈X₁⌉₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    push_cast at h1
    have h2 : ((⌈X₁⌉₊ : ℕ) : ℝ) ≤ ((max 5 ⌈X₁⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 5 ⌈X₁⌉₊
    push_cast at h2
    have h3 : X₁ ≤ ((⌈X₁⌉₊ : ℕ) : ℝ) := Nat.le_ceil X₁
    linarith
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx5
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hx0 : 0 ≤ (x : ℝ) := le_of_lt hxpos
  have hlog0 : 0 ≤ Real.log x := le_of_lt hlogpos
  have hmain := hX₁ (x : ℝ) hxX
  -- Step 1: `(K/c)·(log x)^{β+B} ≤ x^{3/4-α}`
  have hβ : (Real.log x) ^ (β + B) ≤ (Real.log x) ^ (⌈β + B⌉₊ : ℕ) := by
    simpa [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hlog1 (Nat.le_ceil (β + B))
  have hstep1 : (K / c) * (Real.log x) ^ (β + B) ≤ (x : ℝ) ^ ((3 : ℝ) / 4 - α) :=
    le_trans (mul_le_mul_of_nonneg_left hβ (by positivity)) hmain
  -- Step 2: multiply by `x^{α - 3/4}`
  have hp : (x : ℝ) ^ ((3 : ℝ) / 4 - α) * (x : ℝ) ^ (α - (3 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add hxpos, show (3:ℝ)/4 - α + (α - 3/4) = 0 by ring, Real.rpow_zero]
  have hstep2 : (K / c) * (Real.log x) ^ (β + B) * (x : ℝ) ^ (α - (3 : ℝ) / 4) ≤ 1 := by
    rw [← hp]
    exact mul_le_mul_of_nonneg_right hstep1 (Real.rpow_nonneg hx0 _)
  have hstep2' : K * (Real.log x) ^ (β + B) * (x : ℝ) ^ (α - (3 : ℝ) / 4) ≤ c := by
    have heq : (K / c) * (Real.log x) ^ (β + B) * (x : ℝ) ^ (α - (3 : ℝ) / 4)
        = (K * (Real.log x) ^ (β + B) * (x : ℝ) ^ (α - (3 : ℝ) / 4)) / c := by ring
    rw [heq] at hstep2
    have := (div_le_iff₀ hc).mp hstep2
    simpa using this
  -- Step 3: multiply by `x^{3/4 - α}`
  have hp3 : (x : ℝ) ^ (α - (3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4 - α) = 1 := by
    rw [← Real.rpow_add hxpos, show α - 3/4 + ((3:ℝ)/4 - α) = 0 by ring, Real.rpow_zero]
  have hstep3 : K * (Real.log x) ^ (β + B) ≤ c * (x : ℝ) ^ ((3 : ℝ) / 4 - α) := by
    have h := mul_le_mul_of_nonneg_right hstep2' (Real.rpow_nonneg hx0 ((3:ℝ)/4 - α))
    rw [mul_assoc, hp3, mul_one] at h
    exact h
  -- Step 4: multiply by `x^α`
  have hp4 : (x : ℝ) ^ ((3 : ℝ) / 4 - α) * (x : ℝ) ^ α = (x : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hxpos, show (3:ℝ)/4 - α + α = (3:ℝ)/4 by ring]
  have hstep4 : K * (Real.log x) ^ (β + B) * (x : ℝ) ^ α ≤ c * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    have h := mul_le_mul_of_nonneg_right hstep3 (Real.rpow_nonneg hx0 α)
    calc K * (Real.log x) ^ (β + B) * (x : ℝ) ^ α
        ≤ (c * (x : ℝ) ^ ((3 : ℝ) / 4 - α)) * (x : ℝ) ^ α := h
      _ = c * (x : ℝ) ^ ((3 : ℝ) / 4) := by rw [mul_assoc, hp4]
  -- Step 5: multiply by `(log x)^{-B}`
  have hstep5 : K * (Real.log x) ^ (β + B) * (x : ℝ) ^ α * (Real.log x) ^ (-B)
      ≤ c * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-B) :=
    mul_le_mul_of_nonneg_right hstep4 (Real.rpow_nonneg hlog0 _)
  have hsplit : (Real.log x) ^ (β + B) * (Real.log x) ^ (-B) = (Real.log x) ^ β := by
    rw [← Real.rpow_add hlogpos, show β + B + (-B) = β by ring]
  calc K * (x : ℝ) ^ α * (Real.log x) ^ β
      = K * (Real.log x) ^ (β + B) * (x : ℝ) ^ α * (Real.log x) ^ (-B) := by
        rw [← hsplit]; ring
    _ ≤ c * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-B) := hstep5



/-- Uniqueness of the cubefree decomposition `d = d₁ d₂²` (for squarefree coprime `d₁`, `d₂`). -/
lemma mul_sq_inj_cube' {d₁ d₂ e₁ e₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (ht₁ : Squarefree e₁) (ht₂ : Squarefree e₂)
    (htcop : Nat.Coprime e₁ e₂) (heq : d₁ * d₂ ^ 2 = e₁ * e₂ ^ 2) :
    d₁ = e₁ ∧ d₂ = e₂ := by
  have hd₁0 : d₁ ≠ 0 := hs₁.ne_zero
  have hd₂0 : d₂ ≠ 0 := hs₂.ne_zero
  have he₁0 : e₁ ≠ 0 := ht₁.ne_zero
  have he₂0 : e₂ ≠ 0 := ht₂.ne_zero
  have hfac : ∀ p : ℕ, d₁.factorization p + 2 * d₂.factorization p
      = e₁.factorization p + 2 * e₂.factorization p := by
    intro p
    have h1 := congrArg (fun n : ℕ => n.factorization p) heq
    rw [Nat.factorization_mul hd₁0 (pow_ne_zero 2 hd₂0),
      Nat.factorization_mul he₁0 (pow_ne_zero 2 he₂0),
      Nat.factorization_pow, Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul] at h1
    exact h1
  have h1 := (Nat.squarefree_iff_factorization_le_one hd₁0).mp hs₁
  have h2 := (Nat.squarefree_iff_factorization_le_one hd₂0).mp hs₂
  have h3 := (Nat.squarefree_iff_factorization_le_one he₁0).mp ht₁
  have h4 := (Nat.squarefree_iff_factorization_le_one he₂0).mp ht₂
  constructor
  · refine Nat.eq_of_factorization_eq hd₁0 he₁0 fun p => ?_
    have := hfac p
    have hh1 := h1 p; have hh2 := h2 p; have hh3 := h3 p; have hh4 := h4 p
    omega
  · refine Nat.eq_of_factorization_eq hd₂0 he₂0 fun p => ?_
    have := hfac p
    have hh1 := h1 p; have hh2 := h2 p; have hh3 := h3 p; have hh4 := h4 p
    omega

/-- `cubeSum` over the cubefree pairs is at most the sum over all moduli `d ≤ M`
for a nonnegative summand. -/
lemma cubeSum_le_sum_Icc (M : ℕ) (hM : 1 ≤ M) (G : ℕ → ℝ) (hG : ∀ d, 0 ≤ G d) :
    cubeSum M (fun d₁ d₂ => G (d₁ * d₂ ^ 2)) ≤ ∑ d ∈ Finset.Icc 1 M, G d := by
  classical
  set P : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 M ×ˢ Finset.Icc 1 (Nat.sqrt M)).filter (fun p => cubeCond M p.1 p.2)) with hP
  have hcube : cubeSum M (fun d₁ d₂ => G (d₁ * d₂ ^ 2)) = ∑ p ∈ P, G (p.1 * p.2 ^ 2) := by
    have hpp : (∑ d₁ ∈ Finset.Icc 1 M, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt M),
          (if cubeCond M d₁ d₂ then G (d₁ * d₂ ^ 2) else 0))
        = ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 (Nat.sqrt M)),
            (if cubeCond M p.1 p.2 then G (p.1 * p.2 ^ 2) else 0) := by
      rw [Finset.sum_product]
    have hpp2 : (∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 (Nat.sqrt M)),
            (if cubeCond M p.1 p.2 then G (p.1 * p.2 ^ 2) else 0))
        = ∑ p ∈ P, G (p.1 * p.2 ^ 2) := by
      rw [hP, Finset.sum_filter]
    rw [cubeSum, hpp, hpp2]
  rw [hcube]
  have hinj : ∀ p ∈ P, ∀ q ∈ P, p.1 * p.2 ^ 2 = q.1 * q.2 ^ 2 → p = q := by
    intro p hp q hq heq
    obtain ⟨hs₁, hs₂, hcop, -, -⟩ := (Finset.mem_filter.mp (by rw [← hP]; exact hp)).2
    obtain ⟨ht₁, ht₂, htcop, -, -⟩ := (Finset.mem_filter.mp (by rw [← hP]; exact hq)).2
    obtain ⟨h1, h2⟩ := mul_sq_inj_cube' hs₁ hs₂ hcop ht₁ ht₂ htcop heq
    exact Prod.ext h1 h2
  have hsub : P.image (fun p : ℕ × ℕ => p.1 * p.2 ^ 2) ⊆ Finset.Icc 1 M := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨-, -, -, -, hle⟩ := (Finset.mem_filter.mp (by rw [← hP]; exact hp)).2
    have hmem := Finset.mem_of_mem_filter p (by rw [← hP]; exact hp)
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hmem
    rw [Finset.mem_Icc] at hp1 hp2 ⊢
    refine ⟨?_, hle⟩
    calc (1 : ℕ) = 1 * 1 ^ 2 := by ring
      _ ≤ p.1 * p.2 ^ 2 := Nat.mul_le_mul hp1.1 (Nat.pow_le_pow_left hp2.1 2)
  have himg : (∑ p ∈ P, G (p.1 * p.2 ^ 2))
      = ∑ d ∈ P.image (fun p : ℕ × ℕ => p.1 * p.2 ^ 2), G d := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj a ha b hb hab
  rw [himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hG d)

/-- `⌊x^{7/10}(log x)^{2^25}⌋ ≤ x` for large `x`. -/
lemma R3cut_le_self :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → R3cut x ≤ x := by
  obtain ⟨Z, hZ1, hZ⟩ := Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
    (K := 1) (by norm_num) (n := ⌈((2:ℝ)^25)⌉₊) (r := (3:ℝ)/10) (by norm_num)
  refine ⟨max ⌈Z⌉₊ 5 + 1, fun x hx => ?_⟩
  have hx5 : 5 ≤ x := by omega
  have hxZ : Z ≤ (x : ℝ) := by
    have h1 : ((max ⌈Z⌉₊ 5 + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have h2 : Z ≤ ((⌈Z⌉₊ : ℕ) : ℝ) := Nat.le_ceil Z
    have h3 : ((⌈Z⌉₊ : ℕ) : ℝ) ≤ ((max ⌈Z⌉₊ 5 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    push_cast at h1
    push_cast at h3
    linarith
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx5
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hbound := hZ (x : ℝ) hxZ
  have hb : (1 : ℝ) * Real.log x ^ (↑(⌈((2 : ℝ) ^ 25)⌉₊) : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 10) := by
    rw [Real.rpow_natCast]
    exact hbound
  rw [one_mul] at hb
  have hle : Real.log x ^ ((2 : ℝ) ^ 25) ≤ (x : ℝ) ^ ((3 : ℝ) / 10) := by
    refine le_trans ?_ hb
    simpa using Real.rpow_le_rpow_of_exponent_le hlog1 (Nat.le_ceil ((2:ℝ)^25))
  have hprod : (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) ≤ (x : ℝ) := by
    calc (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (x : ℝ) ^ ((3 : ℝ) / 10) :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (le_of_lt hx0) _)
      _ = (x : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
  have hfloor : ⌊(x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)⌋₊ ≤ x := by
    have h1 : ((⌊(x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      le_trans (Nat.floor_le (by positivity)) hprod
    exact_mod_cast h1
  simpa [R3cut] using hfloor


/-- `⌊x^{7/10}(log x)^{2^25}⌋ ≥ 2` for `x ≥ 5`. -/
lemma two_le_R3cut {x : ℕ} (hx : 5 ≤ x) : 2 ≤ R3cut x := by
  unfold R3cut
  refine Nat.le_floor ?_
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have h4 : (2 : ℝ) ^ 2 ≤ (x : ℝ) := by nlinarith
  have hs : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    calc (2 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt h4
      _ = (x : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
  have hup : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogpow : (1 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) := by
    have := Real.rpow_le_rpow (le_of_lt zero_lt_one) hlog1 (by positivity : (0:ℝ) ≤ (2:ℝ)^25)
    simpa using this
  have hs' : (2 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := le_trans hs hup
  calc (2 : ℝ) = 2 * 1 := by ring
    _ ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
        mul_le_mul hs' hlogpow (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg x) _)

/-- **(R₃)** of the companion paper for the Friedlander–Iwaniec sequence, for the
cubefree moduli not divisible by `4` (which are exactly the moduli parametrised by
`d = d₁ d₂²` in §3 of the main paper). -/
theorem X2Y4_R3_generic (lamm : ℝ) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      R3sum x t ≤ (Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
  obtain ⟨cA, hcA, XA, hAlow⟩ := exists_const_mul_rpow_le_Aseq
  obtain ⟨CA, hCA, hAup⟩ := Aseq_le_const_mul_rpow
  obtain ⟨CAd, hCAd, hAd⟩ := sum_Ad_le
  obtain ⟨Cg₀, Ag₀, hCg₀, hGg₀⟩ := cubeSum_gdens_le
  obtain ⟨C35, A35, hC35, hA35, h35⟩ := prop35_unconditional
  -- a nonnegative-exponent version of the `gdens` summatory bound
  obtain ⟨Cg, Ag, hCg, hAg, hGg⟩ : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) ≤ C * (Real.log y) ^ A := by
    refine ⟨Cg₀ * max 1 ((Real.log 2) ^ (Ag₀ - max Ag₀ 0)), max Ag₀ 0,
      mul_pos hCg₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), le_max_right _ _, fun y hy => ?_⟩
    have hmain := hGg₀ y hy
    have hb := rpow_log_le_const_mul (B := Ag₀) (A := max Ag₀ 0) (le_max_left _ _) hy
    have hlogy : (0 : ℝ) ≤ (Real.log y) ^ (max Ag₀ 0) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y))) _
    have h2 : (Real.log 2) ^ (Ag₀ - max Ag₀ 0) ≤ max 1 ((Real.log 2) ^ (Ag₀ - max Ag₀ 0)) :=
      le_max_right _ _
    calc cubeSum y (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) ≤ Cg₀ * (Real.log y) ^ Ag₀ := hmain
      _ ≤ Cg₀ * ((Real.log 2) ^ (Ag₀ - max Ag₀ 0) * (Real.log y) ^ (max Ag₀ 0)) :=
          mul_le_mul_of_nonneg_left hb hCg₀.le
      _ = Cg₀ * (Real.log 2) ^ (Ag₀ - max Ag₀ 0) * (Real.log y) ^ (max Ag₀ 0) := by ring
      _ ≤ Cg₀ * max 1 ((Real.log 2) ^ (Ag₀ - max Ag₀ 0)) * (Real.log y) ^ (max Ag₀ 0) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogy
          exact mul_le_mul_of_nonneg_left h2 hCg₀.le
  obtain ⟨Y1, hY1x, hY1⟩ := poly_tail_gen C35 ((7 : ℝ) / 40 + 9 / 16 + 1 / 100) ((2 : ℝ) ^ 23)
    (cA / 2) lamm hC35 (by norm_num) (by positivity)
  obtain ⟨Y2, hY2x, hY2⟩ := poly_tail_gen (C35 * 2 ^ A35) (1 / 2) A35 (cA / 2) lamm
    (by positivity) (by norm_num) (by positivity)
  obtain ⟨Y3, hY3x, hY3⟩ := poly_tail_gen 1 ((7 : ℝ) / 10) ((2 : ℝ) ^ 25) (cA / 3) lamm
    (by norm_num) (by norm_num) (by positivity)
  obtain ⟨Y4, hY4x, hY4⟩ := poly_tail_gen (CAd * CA) ((7 : ℝ) / 10 + 1 / 100) ((2 : ℝ) ^ 25)
    (cA / 3) lamm (by positivity) (by norm_num) (by positivity)
  obtain ⟨Y5, hY5x, hY5⟩ := poly_tail_gen (Cg * CA) ((7 : ℝ) / 10) ((2 : ℝ) ^ 25 + Ag) (cA / 3)
    lamm (by positivity) (by norm_num) (by positivity)
  obtain ⟨Z, hZ⟩ := R3cut_le_self
  refine ⟨Y1 + Y2 + Y3 + Y4 + Y5 + Z + XA + 6, fun x hx t ht2 htx => ?_⟩
  have hxY1 : Y1 ≤ x := by omega
  have hxY2 : Y2 ≤ x := by omega
  have hxY3 : Y3 ≤ x := by omega
  have hxY4 : Y4 ≤ x := by omega
  have hxY5 : Y5 ≤ x := by omega
  have hxZ : Z ≤ x := by omega
  have hxXA : XA ≤ x := by omega
  have hx5 : 5 ≤ x := by omega
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx5
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hlog0 : 0 ≤ Real.log x := le_of_lt hlogpos
  have hM2 : 2 ≤ R3cut x := two_le_R3cut hx5
  have hMxN : R3cut x ≤ x := hZ x hxZ
  have hMx : (R3cut x : ℝ) ≤ (x : ℝ) := by exact_mod_cast hMxN
  have hAx : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Aseq x : ℝ) := hAlow x hxXA
  have ht1 : 1 ≤ t := by omega
  have htle : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have hlogM0 : 0 ≤ Real.log (R3cut x) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R3cut x))
  have hlogM : Real.log (R3cut x) ≤ Real.log x := by
    have h3 : (0 : ℝ) < (R3cut x : ℝ) := by
      have : (0 : ℕ) < R3cut x := by omega
      exact_mod_cast this
    exact Real.log_le_log h3 hMx
  have hlogz : (0 : ℝ) ≤ (Real.log x) ^ ((-lamm)) := Real.rpow_nonneg hlog0 _
  have hgn : ∀ d : ℕ, 0 ≤ (gdens d : ℝ) := fun d => Rat.cast_nonneg.mpr (gdens_nonneg d)
  have hfabs : ∀ d : ℕ, 0 ≤ |(gdens d : ℝ)| := fun d => abs_nonneg _
  have hF : ∀ d : ℕ, 0 ≤ |(Ad d t : ℝ) - (gdens d : ℝ) * (Aseq t : ℝ)| :=
    fun d => abs_nonneg _
  by_cases hcase : R3cut x ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊
  · -- ## Case A : the full modulus range is inside the range of `(3.3)`
    have hR1 : R3sum x t ≤ cubeSum (R3cut x) (fun d₁ d₂ =>
        |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|) :=
      cubefree_sum_le_cubeSum (R3cut x) (by omega) _ hF
    have h35' := h35 (R3cut x) t hM2 ht2 hcase
    have hMpow : (R3cut x : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 40) * (Real.log x) ^ ((2 : ℝ) ^ 23) := by
      have h1 : (R3cut x : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
        Nat.floor_le (by positivity)
      have h2 : (R3cut x : ℝ) ^ ((1 : ℝ) / 4)
          ≤ ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by norm_num)
      have h3 : ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)) ^ ((1 : ℝ) / 4)
          = (x : ℝ) ^ ((7 : ℝ) / 40) * (Real.log x) ^ ((2 : ℝ) ^ 23) := by
        rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg x) _) (Real.rpow_nonneg hlog0 _)]
        rw [← Real.rpow_mul (Nat.cast_nonneg x), ← Real.rpow_mul hlog0]
        norm_num
      rwa [h3] at h2
    have htpow : (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
        ≤ (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
      Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
    have hterm1 : (R3cut x : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 40 + 9 / 16 + 1 / 100) * (Real.log x) ^ ((2 : ℝ) ^ 23) := by
      have h3 : (7 : ℝ) / 40 + ((9 : ℝ) / 16 + 1 / 100) = (7 : ℝ) / 40 + 9 / 16 + 1 / 100 := by ring
      calc (R3cut x : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
          ≤ ((x : ℝ) ^ ((7 : ℝ) / 40) * (Real.log x) ^ ((2 : ℝ) ^ 23))
              * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
            mul_le_mul hMpow htpow (Real.rpow_nonneg (Nat.cast_nonneg t) _) (by positivity)
        _ = (x : ℝ) ^ ((7 : ℝ) / 40) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
              * (Real.log x) ^ ((2 : ℝ) ^ 23) := by ring
        _ = (x : ℝ) ^ ((7 : ℝ) / 40 + 9 / 16 + 1 / 100) * (Real.log x) ^ ((2 : ℝ) ^ 23) := by
            rw [← Real.rpow_add hxpos, h3]
    have hlogarg0 : 0 ≤ Real.log ((R3cut x : ℝ) + (t : ℝ) + 2) := by
      refine Real.log_nonneg ?_
      have h1 : (0 : ℝ) ≤ (R3cut x : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (t : ℝ) := by positivity
      linarith
    have hlogbound : Real.log ((R3cut x : ℝ) + (t : ℝ) + 2) ≤ 2 * Real.log x := by
      have h1 : (R3cut x : ℝ) + (t : ℝ) + 2 ≤ 3 * (x : ℝ) := by linarith [hMx, htle, hxR]
      have h2 : Real.log (3 * (x : ℝ)) = Real.log 3 + Real.log x :=
        Real.log_mul (by norm_num) (ne_of_gt hxpos)
      have h3 : Real.log 3 ≤ Real.log x := by
        have h4 : (3 : ℝ) ≤ (x : ℝ) := by
          have : (3 : ℕ) ≤ x := by omega
          exact_mod_cast this
        exact Real.log_le_log (by norm_num) h4
      have h4 : (0 : ℝ) < (R3cut x : ℝ) + (t : ℝ) + 2 := by
        have h5 : (0 : ℝ) ≤ (R3cut x : ℝ) := by positivity
        have h6 : (0 : ℝ) ≤ (t : ℝ) := by positivity
        linarith
      calc Real.log ((R3cut x : ℝ) + (t : ℝ) + 2) ≤ Real.log (3 * (x : ℝ)) :=
            Real.log_le_log h4 h1
        _ = Real.log 3 + Real.log x := h2
        _ ≤ 2 * Real.log x := by linarith
    have hterm2 : Real.sqrt (t : ℝ) * (Real.log ((R3cut x : ℝ) + (t : ℝ) + 2)) ^ A35
        ≤ 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35) := by
      have hs : Real.sqrt (t : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
      have hl : (Real.log ((R3cut x : ℝ) + (t : ℝ) + 2)) ^ A35 ≤ (2 * Real.log x) ^ A35 :=
        Real.rpow_le_rpow hlogarg0 hlogbound hA35
      have hl2 : (2 * Real.log x) ^ A35 = 2 ^ A35 * (Real.log x) ^ A35 :=
        Real.mul_rpow (by norm_num) hlog0
      calc Real.sqrt (t : ℝ) * (Real.log ((R3cut x : ℝ) + (t : ℝ) + 2)) ^ A35
          ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (2 ^ A35 * (Real.log x) ^ A35) :=
            mul_le_mul hs (hl2 ▸ hl) (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hx0 _)
        _ = 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35) := by ring
    have hY1' : C35 * ((x : ℝ) ^ ((7 : ℝ) / 40 + 9 / 16 + 1 / 100) * (Real.log x) ^ ((2 : ℝ) ^ 23))
        ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := by
      have h := hY1 x hxY1
      calc C35 * ((x : ℝ) ^ ((7 : ℝ) / 40 + 9 / 16 + 1 / 100) * (Real.log x) ^ ((2 : ℝ) ^ 23))
          = C35 * (x : ℝ) ^ ((7 : ℝ) / 40 + 9 / 16 + 1 / 100) * (Real.log x) ^ ((2 : ℝ) ^ 23) := by ring
        _ ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := h
    have hY2' : C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35))
        ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := by
      have h := hY2 x hxY2
      calc C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35))
          = C35 * 2 ^ A35 * (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35 := by ring
        _ ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := h
    calc R3sum x t
        ≤ cubeSum (R3cut x) (fun d₁ d₂ =>
            |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|) := hR1
      _ ≤ C35 * ((R3cut x : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
            + Real.sqrt (t : ℝ) * (Real.log ((R3cut x : ℝ) + (t : ℝ) + 2)) ^ A35) := h35'
      _ ≤ C35 * ((x : ℝ) ^ ((7 : ℝ) / 40 + 9 / 16 + 1 / 100) * (Real.log x) ^ ((2 : ℝ) ^ 23)
            + 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35)) :=
          mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hC35.le
      _ = C35 * ((x : ℝ) ^ ((7 : ℝ) / 40 + 9 / 16 + 1 / 100) * (Real.log x) ^ ((2 : ℝ) ^ 23))
            + C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35)) := by ring
      _ ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm))
            + cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) :=
          add_le_add hY1' hY2'
      _ = cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := by ring
      _ ≤ (Aseq x : ℝ) * (Real.log x) ^ ((-lamm)) := mul_le_mul_of_nonneg_right hAx hlogz
  · -- ## Case B : the modulus range exceeds `t^{3/4}`, use the crude bounds
    have hlt : ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ < R3cut x := Nat.lt_of_not_le hcase
    have ht34 : (t : ℝ) ^ ((3 : ℝ) / 4) < (R3cut x : ℝ) := by
      have h1 : (t : ℝ) ^ ((3 : ℝ) / 4) < ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h2 : ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 ≤ (R3cut x : ℝ) := by
        exact_mod_cast hlt
      exact lt_of_lt_of_le h1 h2
    have hfloorM : (R3cut x : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      have h := Nat.floor_le (show (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)
        by positivity)
      simpa [R3cut] using h
    have hAt : (Aseq t : ℝ) ≤ CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)) := by
      calc (Aseq t : ℝ) ≤ CA * (t : ℝ) ^ ((3 : ℝ) / 4) := hAup t ht1
        _ ≤ CA * (R3cut x : ℝ) := mul_le_mul_of_nonneg_left (le_of_lt ht34) hCA.le
        _ ≤ CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)) :=
            mul_le_mul_of_nonneg_left hfloorM hCA.le
    -- the `cubeSum` splits into the `A_d` part and the `g` part
    have hsplit : cubeSum (R3cut x) (fun d₁ d₂ =>
          |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
        ≤ (∑ d ∈ Finset.Icc 1 (R3cut x), (Ad d t : ℝ))
          + (Aseq t : ℝ) * cubeSum (R3cut x)
              (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := by
      have h1 : cubeSum (R3cut x) (fun d₁ d₂ =>
            |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
          ≤ cubeSum (R3cut x) (fun d₁ d₂ => (Ad (d₁ * d₂ ^ 2) t : ℝ)
              + (Aseq t : ℝ) * |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := by
        refine cubeSum_le (R3cut x) fun a b => ?_
        by_cases hc : cubeCond (R3cut x) a b
        · rw [if_pos hc, if_pos hc]
          have hx0' : (0 : ℝ) ≤ (Ad (a * b ^ 2) t : ℝ) := by positivity
          have hAseq0 : (0 : ℝ) ≤ (Aseq t : ℝ) := by positivity
          have h3 : (gdens (a * b ^ 2) : ℝ) * (Aseq t : ℝ)
              ≤ |(gdens (a * b ^ 2) : ℝ)| * (Aseq t : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hAseq0
          have h4 : -(gdens (a * b ^ 2) : ℝ) * (Aseq t : ℝ)
              ≤ |(gdens (a * b ^ 2) : ℝ)| * (Aseq t : ℝ) :=
            mul_le_mul_of_nonneg_right (neg_le_abs _) hAseq0
          rw [abs_le]
          constructor <;> nlinarith [hx0', h3, h4]
        · rw [if_neg hc, if_neg hc]
      have h2 : cubeSum (R3cut x) (fun d₁ d₂ => (Ad (d₁ * d₂ ^ 2) t : ℝ))
          ≤ ∑ d ∈ Finset.Icc 1 (R3cut x), (Ad d t : ℝ) :=
        cubeSum_le_sum_Icc (R3cut x) (by omega) (fun d => (Ad d t : ℝ)) (fun d => by positivity)
      have h3 := cubeSum_add (R3cut x)
        (fun a b => (Ad (a * b ^ 2) t : ℝ)) (fun a b => (Aseq t : ℝ) * |(gdens (a * b ^ 2) : ℝ)|)
      have h4 := cubeSum_const_mul (R3cut x) (Aseq t) (fun a b => |(gdens (a * b ^ 2) : ℝ)|)
      rw [h3, h4] at h1
      exact le_trans h1 (add_le_add h2 le_rfl)
    have hpiece1 : (∑ d ∈ Finset.Icc 1 (R3cut x), (Ad d t : ℝ))
        ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)
          + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
      have h1 := hAd (R3cut x) t
      have h3 : (t : ℝ) ^ ((1 : ℝ) / 100) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
      have h4 : CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
          ≤ CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCAd.le) (by positivity)
      linarith [h1, h4, hfloorM]
    have hpiece2 : (Aseq t : ℝ) * cubeSum (R3cut x) (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|)
        ≤ CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))
          * (Cg * (Real.log x) ^ Ag) := by
      have h1 := hGg (R3cut x) hM2
      have hAg' : (Real.log (R3cut x)) ^ Ag ≤ (Real.log x) ^ Ag :=
        Real.rpow_le_rpow hlogM0 hlogM hAg
      have h2 : cubeSum (R3cut x) (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|)
          ≤ Cg * (Real.log x) ^ Ag := le_trans h1 (mul_le_mul_of_nonneg_left hAg' hCg.le)
      have h4 : (0 : ℝ) ≤ Cg * (Real.log x) ^ Ag :=
        mul_nonneg hCg.le (Real.rpow_nonneg hlog0 _)
      have h5 : (0 : ℝ) ≤ cubeSum (R3cut x) (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := by
        unfold cubeSum
        positivity
      exact mul_le_mul hAt h2 h5 (by positivity)
    have hY3' : (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := by
      have h := hY3 x hxY3
      simpa only [one_mul] using h
    have hY4' : CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := by
      have h := hY4 x hxY4
      have h5 : CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
          ≤ CAd * (x : ℝ) ^ ((1 : ℝ) / 100)
              * (CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))) :=
        mul_le_mul_of_nonneg_left hAt (by positivity)
      have hpow : (x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((7 : ℝ) / 10)
          = (x : ℝ) ^ ((7 : ℝ) / 10 + 1 / 100) := by
        rw [← Real.rpow_add hxpos]; ring_nf
      refine le_trans h5 ?_
      calc CAd * (x : ℝ) ^ ((1 : ℝ) / 100)
              * (CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)))
          = CAd * CA * ((x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((7 : ℝ) / 10))
              * (Real.log x) ^ ((2 : ℝ) ^ 25) := by ring
        _ = CAd * CA * (x : ℝ) ^ ((7 : ℝ) / 10 + 1 / 100)
              * (Real.log x) ^ ((2 : ℝ) ^ 25) := by rw [hpow]
        _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := h
    have hY5' : CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))
            * (Cg * (Real.log x) ^ Ag)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := by
      have h := hY5 x hxY5
      calc CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)) * (Cg * (Real.log x) ^ Ag)
          = Cg * CA * (x : ℝ) ^ ((7 : ℝ) / 10) * ((Real.log x) ^ ((2 : ℝ) ^ 25) * (Real.log x) ^ Ag) := by
            ring
        _ = Cg * CA * (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25 + Ag) := by
            rw [← Real.rpow_add hlogpos]
        _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := h
    calc R3sum x t
        ≤ cubeSum (R3cut x) (fun d₁ d₂ =>
            |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|) :=
          cubefree_sum_le_cubeSum (R3cut x) (by omega) _ hF
      _ ≤ (∑ d ∈ Finset.Icc 1 (R3cut x), (Ad d t : ℝ))
          + (Aseq t : ℝ) * cubeSum (R3cut x)
              (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := hsplit
      _ ≤ ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)
            + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ))
          + CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))
              * (Cg * (Real.log x) ^ Ag) := add_le_add hpiece1 hpiece2
      _ = (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)
            + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
            + CA * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))
                * (Cg * (Real.log x) ^ Ag) := by ring
      _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm))
            + cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm))
            + cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) :=
          add_le_add (add_le_add hY3' hY4') hY5'
      _ = cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ ((-lamm)) := by ring
      _ ≤ (Aseq x : ℝ) * (Real.log x) ^ ((-lamm)) := mul_le_mul_of_nonneg_right hAx hlogz


/-- **(R₃)** of the companion paper for the Friedlander–Iwaniec sequence (at the exponent `2^25`
used by the rest of the development), as a special case of the generic statement. -/
theorem X2Y4_R3 :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      R3sum x t ≤ (Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
  obtain ⟨X₀, hX₀⟩ := X2Y4_R3_generic ((2 : ℝ) ^ 25)
  exact ⟨X₀, fun x hx t ht2 htx => hX₀ x hx t ht2 htx⟩

end Submission
