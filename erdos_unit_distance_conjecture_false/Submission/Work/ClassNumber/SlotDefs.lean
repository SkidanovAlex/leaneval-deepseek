import Mathlib

namespace Work.ClassNumber

open NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- For a nonzero prime ideal `p₀` of `ℤ`, the number of prime ideals of the ring of integers of
`K` lying above it is at most `[K : ℚ]`. -/
theorem primesOver_card_le_finrank (p₀ : Ideal ℤ) [p₀.IsPrime] (h0 : p₀ ≠ ⊥) :
    Nat.card (p₀.primesOver (NumberField.RingOfIntegers K)) ≤ Module.finrank ℚ K := by
  haveI : p₀.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h0
  calc Nat.card (p₀.primesOver (NumberField.RingOfIntegers K))
      = Fintype.card (p₀.primesOver (NumberField.RingOfIntegers K)) := Nat.card_eq_fintype_card
    _ = ∑ _p : p₀.primesOver (NumberField.RingOfIntegers K), 1 := Fintype.card_eq_sum_ones
    _ ≤ ∑ p : p₀.primesOver (NumberField.RingOfIntegers K),
          p.1.ramificationIdx ℤ * p.1.inertiaDeg ℤ := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        have h1 : 1 ≤ p.1.ramificationIdx ℤ :=
          Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Ideal.ramificationIdx_pos p.1 ℤ))
        have h2 : 1 ≤ p.1.inertiaDeg ℤ :=
          Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Ideal.inertiaDeg_pos p.1 ℤ))
        exact one_le_mul h1 h2
    _ = Module.finrank ℤ (NumberField.RingOfIntegers K) :=
        Ideal.sum_ramification_inertia_eq_finrank p₀ (NumberField.RingOfIntegers K)
    _ = Module.finrank ℚ K := NumberField.RingOfIntegers.rank K

/-- An injection of the prime ideals above a nonzero prime `p₀` of `ℤ` into `Fin [K : ℚ]`. -/
noncomputable def slotEmb (p₀ : Ideal ℤ) [p₀.IsPrime] (h0 : p₀ ≠ ⊥) :
    p₀.primesOver (NumberField.RingOfIntegers K) ↪ Fin (Module.finrank ℚ K) :=
  letI : p₀.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h0
  (Fintype.equivFin _).toEmbedding.trans
    (Fin.castLEEmb (by rw [Fintype.card_eq_nat_card]; exact primesOver_card_le_finrank K p₀ h0))

/-- The slot (an index in `Fin [K : ℚ]`) attached to a prime ideal of `𝓞 K`; default `0` for
non-prime or zero ideals. -/
noncomputable def slotOf (P : Ideal (NumberField.RingOfIntegers K)) : Fin (Module.finrank ℚ K) := by
  classical
  exact if h : P.IsPrime ∧ P ≠ ⊥ then
    letI : P.IsPrime := h.1
    letI : (P.under ℤ).IsPrime := Ideal.isPrime_of_liesOver P (P.under ℤ)
    slotEmb K (P.under ℤ) (Ideal.IsIntegral.under_ne_bot ℤ h.2)
      ⟨P, inferInstance, Ideal.over_under P⟩
  else ⟨0, Module.finrank_pos⟩

/-- The map sending an ideal to an `[K : ℚ]`-tuple of natural numbers, obtained by distributing
the prime powers in the factorization of the ideal over the slots. -/
noncomputable def Phi (I : Ideal (NumberField.RingOfIntegers K)) :
    Fin (Module.finrank ℚ K) → ℕ := by
  classical
  exact fun i => ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
    if slotOf K P = i then (Ideal.absNorm P) ^
      ((UniqueFactorizationMonoid.normalizedFactors I).count P) else 1

variable {K}

/-- The product of the entries of `Phi K I` is the absolute norm of `I`. -/
theorem Phi_prod (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    ∏ i, Phi K I i = Ideal.absNorm I := by
  classical
  have h1 : ∏ i, Phi K I i
      = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
          (Ideal.absNorm P) ^ ((UniqueFactorizationMonoid.normalizedFactors I).count P) := by
    simp only [Phi]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [Finset.prod_ite_eq]
    simp
  have h2 : ((UniqueFactorizationMonoid.normalizedFactors I).map Ideal.absNorm).prod
      = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
          (Ideal.absNorm P) ^ ((UniqueFactorizationMonoid.normalizedFactors I).count P) :=
    Finset.prod_multiset_map_count _ _
  have h3 : ((UniqueFactorizationMonoid.normalizedFactors I).map Ideal.absNorm).prod
      = Ideal.absNorm I := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
  rw [h1, ← h2, h3]

end Work.ClassNumber
