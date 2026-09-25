import Mathlib
import Submission.Work.Tower.Unramified.SplitsCompletelyNF

namespace Work.Tower.Unramified

open NumberField

/-- **From the explicit definition of complete splitting to its normal form.**

If `q` splits completely in the number field `K` in the sense of `Work.Defs.SplitsCompletely`
(namely `q𝒪_K` is the product of `[K : ℚ]` pairwise distinct primes with residue field `𝔽_q`),
then the primes of `𝒪_K` above `(q)` are exactly `[K : ℚ]` in number and each of them has
ramification index `1` and inertia degree `1` over `ℤ`.

The two halves are extracted from the fundamental identity
`∑_{P | (q)} e(P) f(P) = [K : ℚ]`: the hypothesis already exhibits `[K : ℚ]` distinct primes
above `(q)`, so the sum has exactly `[K : ℚ]` terms and, since every term `e(P) f(P) ≥ 1`,
each term must be `1`. -/
theorem splitsCompletely_imp_NF {K : Type*} [Field K] [NumberField K] (q : ℕ) (hq : Nat.Prime q)
    (h : Work.Defs.SplitsCompletely q K) : Work.Tower.Unramified.SplitsCompletelyNF q K := by
  classical
  obtain ⟨𝔮, hprime, hmem, hres, hinc, hprod⟩ := h
  haveI : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsPrime := isPrime_span_singleton_int hq
  haveI : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsMaximal := isMaximal_span_singleton_int hq
  -- every `𝔮 i` is a prime of `𝒪_K` above `(q)`
  have hmemPO : ∀ i, 𝔮 i ∈ (Ideal.span {(q : ℤ)}).primesOver (𝓞 K) :=
    fun i => (mem_primesOver_span_nat_iff hq (𝔮 i)).mpr ⟨hprime i, hmem i⟩
  -- the `𝔮 i` are distinct
  have hinj : Function.Injective 𝔮 := fun i j hij => by
    by_contra hne
    exact hinc i j hne (le_of_eq hij)
  -- the fundamental identity `∑_{P | (q)} e(P) f(P) = [K : ℚ]`
  have hsum : ∑ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K),
      P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ = Module.finrank ℚ K := by
    rw [Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(q : ℤ)} : Ideal ℤ) (𝓞 K),
      IsFractionRing.finrank_eq ℤ ℚ (𝓞 K) K]
  -- every summand is at least `1`
  have hf : ∀ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K),
      1 ≤ P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ := by
    intro P
    have h1 : 0 < P.1.ramificationIdx ℤ := Ideal.ramificationIdx_pos P.1 ℤ
    have h2 : 0 < P.1.inertiaDeg ℤ := Ideal.inertiaDeg_pos P.1 ℤ
    exact Nat.mul_pos h1 h2
  -- cardinality of the set of primes over `(q)`
  have hcard_ge : Module.finrank ℚ K ≤
      Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) := by
    have hφ : Function.Injective (fun i : Fin (Module.finrank ℚ K) =>
        (⟨𝔮 i, hmemPO i⟩ : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K))) :=
      fun i j hij => hinj (Subtype.ext_iff.mp hij)
    simpa using Fintype.card_le_of_injective _ hφ
  have hcard_le : Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) ≤
      Module.finrank ℚ K := by
    have h1 : (∑ _ : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), (1 : ℕ)) =
        Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) := by simp
    rw [← hsum, ← h1]
    exact Finset.sum_le_sum fun P _ => hf P
  have hcard : Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) = Module.finrank ℚ K :=
    le_antisymm hcard_le hcard_ge
  constructor
  · rw [Nat.card_eq_fintype_card]
    exact hcard
  · intro P
    -- the summand at `P` is `1`, since the sum equals the number of summands
    have hterm : P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ = 1 := by
      by_contra hne
      have hlt : (1 : ℕ) < P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ :=
        lt_of_le_of_ne (hf P) (Ne.symm hne)
      have hsum' : ∑ Q : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K),
          Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ =
            Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) := by
        rw [hsum, hcard]
      have hlt' := Finset.sum_lt_sum (s := Finset.univ)
        (f := fun _ : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K) => (1 : ℕ))
        (g := fun Q : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K) =>
          Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ)
        (fun Q _ => hf Q) ⟨P, Finset.mem_univ P, hlt⟩
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hlt'
      rw [hsum'] at hlt'
      exact absurd hlt' (lt_irrefl _)
    exact ⟨Nat.dvd_one.mp ⟨P.1.inertiaDeg ℤ, hterm.symm⟩,
      Nat.dvd_one.mp ⟨P.1.ramificationIdx ℤ, by rw [mul_comm]; exact hterm.symm⟩⟩

end Work.Tower.Unramified
